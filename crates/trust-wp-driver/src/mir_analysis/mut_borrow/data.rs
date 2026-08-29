// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::{HashMap, HashSet};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Body, Local},
    ty::TyCtxt,
};
use trust_wp_core::formula::{BorrowIdOrigin, PureExpr};
use trust_wp_driver::StdSpec;

use crate::mir_analysis::{resolver::ResolveResults, translate::ExprLookup};

/// Expression lookup that combines local expressions with deref-tracked expressions.
///
/// Wraps `HashMap<Local, PureExpr>` (regular locals), `HashMap<Local, PureExpr>`
/// (whole-deref tracked values), and `HashMap<(Local, u32), PureExpr>` (field-deref
/// tracked values) into a single `ExprLookup` implementation. This allows the
/// shared `translate_rvalue`/`translate_operand`/`translate_place` functions from
/// `translate.rs` to resolve deref-aware expressions without separate `_with_deref`
/// variants. (#895)
pub(super) struct DerefLookup<'a> {
    pub(super) locals: &'a HashMap<Local, PureExpr>,
    pub(super) deref_exprs: &'a HashMap<Local, PureExpr>,
    pub(super) field_deref_exprs: &'a HashMap<(Local, u32), PureExpr>,
}

impl ExprLookup for DerefLookup<'_> {
    fn get_expr(&self, local: &Local) -> Option<&PureExpr> {
        self.locals.get(local)
    }

    fn get_deref_expr(&self, local: &Local) -> Option<&PureExpr> {
        self.deref_exprs.get(local)
    }

    fn get_field_deref_expr(&self, local: &Local, field: u32) -> Option<&PureExpr> {
        self.field_deref_exprs.get(&(*local, field))
    }

    fn rich_field_projections(&self) -> bool {
        false
    }
}

/// Target of a write through a mutable borrow.
///
/// For regular `&mut` params, a write looks like `*v = expr` (whole deref).
/// For FnMut closure captures, a write looks like `(*_1).0 = expr` (field deref).
#[derive(Debug, Clone, Copy)]
pub(super) enum DerefTarget {
    /// Write to the whole dereferenced value: `*v = expr`
    Whole(Local),
    /// Write to a field of the dereferenced value: `(*v).N = expr`
    /// Used for FnMut closure capture mutations.
    Field(Local, u32),
}

/// A write through an index operation on a `&mut` slice/vec parameter.
///
/// Records the components of `(*param)[idx] = value` so the verification
/// code can synthesize IndexMut postconditions (point-write, length
/// preservation, frame condition). (#1317)
#[derive(Debug, Clone)]
pub(crate) struct IndexedWrite {
    /// Name of the `&mut` parameter being indexed into.
    pub(crate) param_name: String,
    /// Index expression (typically a constant or local variable).
    pub(crate) index: PureExpr,
    /// Value written at the index.
    pub(crate) value: PureExpr,
}

/// A mutable sub-slice reborrow created by a range `IndexMut` call.
#[derive(Debug, Clone)]
pub(super) struct SliceReborrow {
    /// Original tracked mutable slice parameter.
    pub(super) parent_local: Local,
    /// Offset of the sub-slice within the parent slice.
    pub(super) start_expr: PureExpr,
}

/// Result of extracting mutable borrow body.
///
/// For a function like `fn increment_ref(v: &mut i32) { *v += 1; }`, this
/// captures the relationship between the initial and final values of
/// mutable borrows.
#[derive(Debug, Clone)]
pub(crate) struct MutBorrowBody {
    /// Map from mutable borrow parameter name to final value expression.
    ///
    /// For `increment_ref(v)` with body `*v += 1`:
    /// - key: "v"
    /// - value: `Deref(Var("v")) + 1` (i.e., `*v + 1`)
    ///
    /// In RustHorn encoding, this becomes: `v_final = v_current + 1`
    pub(crate) final_values: HashMap<String, PureExpr>,
    /// Indexed writes through `&mut` slice/vec parameters (#1317).
    ///
    /// When the body contains `(*a)[idx] = val`, the mut_borrow extractor
    /// can't express this as a simple `a_final = <expr>` (since the indexed
    /// write only modifies one element). Instead, the write is recorded here
    /// so the verification code can synthesize IndexMut postconditions.
    pub(crate) indexed_writes: Vec<IndexedWrite>,
    /// Dataflow-precise resolve results for `&mut` parameters (#2150 Phase 2).
    ///
    /// When present, indicates that the resolver has computed exact MIR
    /// locations where each `&mut` borrow can be resolved. The SMT encoder
    /// can use this to emit `v_final == v_current` at precise points instead
    /// of at function scope, enabling the 6-to-2 variable reduction.
    pub(crate) resolve_results: Option<ResolveResults>,
    /// Per-reborrow finality from backward dataflow analysis (#2181).
    ///
    /// Maps reborrow child name (e.g., `"v_rb5"`) to its `BorrowFinality`.
    /// When a reborrow is `Final`, the encoder can skip the fresh prophecy
    /// variable and reuse the parent's, reducing SMT quantifier load.
    pub(crate) finality: HashMap<String, trust_wp_core::formula::BorrowFinality>,
    /// Per-reborrow borrow-id provenance for whole-borrow equality. (#2141)
    pub(crate) borrow_id_origins: HashMap<String, BorrowIdOrigin>,
    /// Delayed writebacks for two-phase borrows, lowered as call assumptions.
    ///
    /// These keep two-phase reservations out of the immediate prophecy path by
    /// asserting the parent/child relationship only after the activating call.
    pub(crate) delayed_writeback_assumptions: Vec<PureExpr>,
    /// Parameters whose mutation was detected but could not be symbolically
    /// advanced (#2124 Phase 5).
    ///
    /// When a mutation call (e.g., `v.push(x)`) cannot be forward-simulated
    /// by `try_spec_advancement` or `try_index_mut_continuation`, the parameter
    /// is recorded here. The SMT encoder uses this set to skip the identity
    /// `v_final == v_current` assertion from `final_values`, letting
    /// `call_assumptions` + `resolve_assertions` be the sole constraints on
    /// the parameter's final value.
    pub(crate) mutation_continued_params: HashSet<String>,
    /// RustHorn expiry resolutions for rebindable mut-ref parameter slots
    /// (nested-reborrow transfer calls, e.g. `swap(&mut ma, &mut mb)` with
    /// `ma: &mut u32`).
    ///
    /// Each entry is a premise `Final(<content>) == <value>` where `<content>`
    /// is the (branch-merged, mutref-sorted) entry borrow residing in a
    /// parameter slot at function exit, and `<value>` is the pointee value of
    /// that slot at exit. This is the prophecy resolution of the borrow that
    /// actually expires in that slot — for rebound slots this is NOT the slot's
    /// entry borrow, so the plain `final_values` identity would be wrong and is
    /// removed for these params (they are added to `mutation_continued_params`
    /// instead so no identity resolve is emitted either).
    pub(crate) nested_slot_resolutions: Vec<PureExpr>,
    /// Parameter names whose slots were rebound by a recognized nested-reborrow
    /// transfer call. Used to filter the (unguarded, level-collapsed) call-site
    /// spec instantiations that would otherwise mis-constrain `<p>_final`.
    pub(crate) nested_transfer_params: HashSet<String>,
}

/// Return type for block extraction:
/// (whole-deref finals, field-deref finals, nested-slot content finals).
///
/// The third map tracks, for rebindable mut-ref parameter slots, WHICH entry
/// borrow (as a mutref-sorted `PureExpr`) resides in the slot at function
/// exit. Absent entries mean the identity (the slot still holds its entry
/// borrow).
pub(super) type BlockResult = Option<(
    HashMap<Local, PureExpr>,
    HashMap<(Local, u32), PureExpr>,
    HashMap<Local, PureExpr>,
)>;

/// Metadata for a pending IndexMut call result that hasn't been written to yet.
///
/// When `IndexMut::index_mut(&mut v, idx)` is called, the returned `&mut T`
/// reference is not immediately useful. It becomes meaningful only when the
/// caller writes through it (`*result = val`). This struct tracks the metadata
/// needed to synthesize an `IndexedWrite` when the write occurs. (#2124 Phase 4)
#[derive(Debug, Clone)]
pub(super) struct PendingIndexMut {
    /// The parameter name for the IndexedWrite.
    pub(super) param_name: String,
    /// The index expression passed to `index_mut`.
    pub(super) index_expr: PureExpr,
    /// The tracked `&mut` parameter local, for updating `deref_exprs`
    /// with the post-write intermediate state. (#2124 Phase 5)
    pub(super) receiver_local: Local,
}

/// Mutable accumulators threaded through `extract_mut_borrow_from_block`.
///
/// Replaces the former `INDEXED_WRITES`, `MUTATION_CONTINUED_PARAMS`, and
/// `PENDING_INDEX_MUT` thread-locals with explicit parameters. (#2166)
pub(super) struct MutBorrowAccumulators {
    /// Indexed writes: `(*param)[idx] = val` entries. (#1317)
    pub(super) indexed_writes: Vec<IndexedWrite>,
    /// `&mut` params whose mutation could not be symbolically advanced. (#2124 Phase 5)
    pub(super) mutation_continued_params: HashSet<String>,
    /// Pending IndexMut metadata keyed by destination local. (#2124 Phase 4)
    pub(super) pending_index_mut: HashMap<Local, PendingIndexMut>,
    /// Mut-ref parameter slots rebound by a recognized nested-reborrow
    /// transfer call (e.g. `swap(&mut ma, &mut mb)`).
    pub(super) nested_transfer_slots: HashSet<Local>,
    /// Set when the analysis saw something that could invalidate nested-slot
    /// content tracking (an untranslatable deref write, or a nested slot
    /// borrow escaping into an unrecognized call). When set, no
    /// `nested_slot_resolutions` are emitted (fail-closed: the affected params
    /// keep only their suppressed/unresolved state).
    pub(super) nested_transfer_poisoned: bool,
}

/// Mutable traversal state threaded through `extract_mut_borrow_from_block` recursion.
///
/// Groups the per-block local expression maps, deref tracking maps, reborrow
/// maps, and visited set that were previously passed as individual parameters.
/// This keeps recursive function signatures under clippy's `too_many_arguments`
/// threshold. (#2657)
#[derive(Clone)]
pub(super) struct MutBorrowTraversalState {
    /// Map from MIR locals to their current symbolic expressions.
    pub(super) local_exprs: HashMap<Local, PureExpr>,
    /// Map from dereferenced locals to their tracked symbolic value.
    pub(super) deref_exprs: HashMap<Local, PureExpr>,
    /// Per-field deref tracking for FnMut closure captures.
    pub(super) field_deref_exprs: HashMap<(Local, u32), PureExpr>,
    /// Reborrow chain: maps a reborrowed local to the original `&mut` param.
    pub(super) reborrow_map: HashMap<Local, Local>,
    /// Field reborrow chain: maps a local to (param, field_idx) it reborrows.
    pub(super) field_reborrow_map: HashMap<Local, (Local, u32)>,
    /// Sub-slice reborrow chain for range `IndexMut` results.
    pub(super) slice_reborrow_map: HashMap<Local, SliceReborrow>,
    /// Nested slot borrows: maps a temp holding `&mut <slot_local>` (a borrow
    /// of a rebindable mut-ref parameter slot, projection-less on both sides)
    /// to the borrowed slot local. Used to recognize nested-reborrow transfer
    /// calls like `swap(&mut ma, &mut mb)`.
    pub(super) slot_borrow_map: HashMap<Local, Local>,
    /// Current content of rebindable mut-ref parameter slots, as mutref-sorted
    /// expressions over the ENTRY borrows. Absent = identity (slot holds its
    /// entry borrow). Updated by nested-reborrow transfer advancement.
    pub(super) slot_exprs: HashMap<Local, PureExpr>,
    /// Set of visited basic blocks (loop detection).
    pub(super) visited: HashSet<BasicBlock>,
}

/// Immutable context for `extract_mut_borrow_from_block` recursive traversal.
///
/// Groups the read-only parameters that are threaded unchanged through every
/// recursive call, keeping the function signature under clippy's
/// `too_many_arguments` threshold while preserving the traversal API.
pub(super) struct MutBorrowBlockContext<'a, 'tcx> {
    pub(super) tcx: TyCtxt<'tcx>,
    pub(super) body: &'a Body<'tcx>,
    pub(super) mut_borrow_params: &'a [Local],
    pub(super) arg_names: &'a [String],
    pub(super) user_specs: &'a HashMap<DefId, StdSpec>,
    pub(super) trait_specs: &'a HashMap<DefId, StdSpec>,
    pub(super) extern_specs: &'a HashMap<String, StdSpec>,
}
