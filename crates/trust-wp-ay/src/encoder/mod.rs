// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! AY Encoder - Translates separation logic formulas to ay SMT terms.
//!
//! This module provides the core encoding logic for translating `trust_wp_core::formula`
//! types into ay's API terms.
//!
//! # Key Types
//!
//! - [`AYEncoder`]: Main encoder struct holding solver state and symbol tables
//!
//! # Encoding Overview
//!
//! The encoder translates:
//! - Pure expressions (`PureExpr`) to ay `Term`s
//! - Separation logic formulas (`Formula`) to ay `Term`s with heap modeling
//! - Logic function definitions to ay function declarations
//!
//! # Variable Naming Algebra (RustHorn Encoding)
//!
//! For mutable reference parameters, the encoder generates SMT variables using a
//! suffix-based naming scheme. Given a base parameter name `v`:
//!
//! | Expression | SMT Variable | Meaning |
//! |---|---|---|
//! | `Var("v")` | `v` | The reference itself |
//! | `Deref(Var("v"))` = `*v` | `v_current` | Current (entry) value |
//! | `Final(Var("v"))` = `^v` | `v_final` | Final (post-borrow) value |
//! | `Final(Deref(Var("v")))` = `^(*v)` | `v_current_final` | Final via Deref path |
//! | `Deref(Deref(Var("v")))` = `*(*v)` | `v_current_current` | Entry via nested Deref |
//! | `Deref(Final(Var("v")))` = `*(^v)` | `v_final_current` | Post-state via Deref |
//! | `Final(Final(Var("v")))` = `^(^v)` | `v_final_final` | Post-state via nested Final |
//! | `Old(Deref(Var("v")))` = `old(*v)` | `v_current` | Same as `*v` |
//! | `Old(Var("v"))` = `old(v)` | `old_v` | Old prefix |
//!
//! The suffixes compose recursively: `Deref` appends `_current`, `Final` appends
//! `_final`. This is implemented by [`sort_context::resolve_nameable_expr`].
//!
//! ## Alias Constraints (Critical for Soundness)
//!
//! The body of a `&mut` function sets `v_final = body_expr` where `body_expr` uses
//! `v_current`. When postconditions are transformed by
//! [`PureExpr::transform_postcondition_for_mut_refs`](trust_wp_core::formula::PureExpr::transform_postcondition_for_mut_refs),
//! bare `Var(v)` becomes `Deref(Var(v))` and `*v` becomes `^v`. For tuple/struct
//! fields, the encoder pushes `Final`/`Deref` inside `LogicFnCall` arguments,
//! producing `v_current_final` and `v_current_current`. Without explicit alias
//! constraints, these are free (unconstrained) variables causing spurious failures.
//!
//! The verification code in [`crate::verify::mut_borrow`] asserts these aliases
//! per parameter using [`sort_context::MutRefVarNames`]:
//!
//! - `v_current_final = body_expr` (connects `^(*v)` to body)
//! - `v_current_current = v_current` (connects `*(*v)` to entry state)
//! - `v_final_current = body_expr` (normalizes `*(^v)`)
//! - `v_final_final = body_expr` (normalizes `^(^v)`)
//!
//! See #858, #745, #868 for the history of spurious failures from missing aliases.
//!
//! # See Also
//!
//! - [`crate::verify`]: Uses encoder for verification condition generation
//! - [`crate::memory_model`]: Heap encoding abstraction

use std::collections::{HashMap, HashSet};

mod adt_axioms;
mod axioms;
mod closure_axioms;
pub(crate) mod closure_inline;
pub(crate) mod closure_sorts;
mod constructors;
pub(crate) mod final_collapse_guard;
pub(crate) mod ground_pool;
mod guards;
mod heap;
mod logic_fn;
pub(crate) mod match_enc;
mod method_call;
#[cfg(test)]
mod method_call_tests;
mod mut_borrow_enc;
mod mut_ref_sort;
mod nonlinear_product_bounds;
#[cfg(test)]
mod operator_tests;
mod operators;
mod produces_axioms;
mod produces_ground;
mod produces_predicate;
mod pure_encoding;
// The native QF_BV proof lane recognises the driver's shift-amount marker
// so it can emit the range obligation as a native BV check (ledger
// int-shift-full).
pub(crate) use self::pure_encoding::parse_shift_amount_in_range_name;
pub(crate) mod quantifier;
pub(crate) mod quantifier_ctor_elim;
#[cfg(test)]
mod quantifier_tests;
mod recursive_eval;
pub(crate) use self::recursive_eval::{simplify_ground, try_evaluate_recursive};
pub(crate) mod replay_artifact;
use replay_artifact::ReplayRecorder;
#[cfg(any(test, feature = "sep-logic"))]
mod sep_logic;
pub(crate) mod seq;
#[cfg(test)]
mod seq_reverse_tests;
mod seq_synth;
#[cfg(test)]
mod seq_tests;
#[cfg(test)]
mod seq_type_param_tests;
mod shell;
mod solver;
pub(crate) mod sort_context;
mod state;
#[cfg(test)]
pub(crate) mod test_solver_limiter;
pub(crate) mod trigger;
#[cfg(test)]
mod trigger_tests;
mod type_resolve;
mod var_declare;
mod var_env;
// Unsoundness tracking for encoding approximations (#2106).
// Made pub for cross-crate use by trust-wp-driver (#2206).
pub(crate) mod ay_api;
pub mod unsoundness;
mod view;

// Re-export state structs so existing consumers (sibling submodules and crate-level) work unchanged.
// All structs are pub(crate) inside the private `state` module; re-exported here for stability.

// Re-export sort context items used by sibling submodules (via `super::`)
use ay_dpll::api::{DatatypeSort, Solver, Sort, Term};
use sort_context::{
    coerce_ite_sorts, coerce_to_numeric, collect_bool_hints, resolve_view_var_name,
    select_structural_sort_target, NumericOperandMode,
};
// Re-export sort context items also used outside the encoder module (verify.rs)
pub(crate) use sort_context::{
    effective_expr_annotation, extract_base_var_name, extract_inner_var_annotation,
    infer_expr_sort, is_definitely_non_bool, MutRefVarNames,
};
#[cfg(test)]
pub(crate) use state::SynthesizedTriggerDiagnostic;
pub(crate) use state::{
    AdtState, ArithmeticModeState, AssertionPhase, AssertionPipelineState, ClosureState,
    ContainerElementInvariantSpec, DeclarationState, DedupSnapshot, EncodingCacheState,
    QuantifierState, ResolveElsewhereFootprint, ResolveElsewhereFrame, SeqFunctions, SeqState,
    SeqValue, SortResolverState, TraversalState,
};
#[cfg(any(test, feature = "sep-logic"))]
pub(crate) use state::{FormulaCacheKey, SepConjCache};
#[cfg(any(test, feature = "sep-logic"))]
use trust_wp_core::formula::Formula;
use trust_wp_core::formula::{ExprSort, PureExpr};
// Qualified `T::MIN`/`T::MAX` folding for the native QF_BV fast path
// (verify/function/bitwise_bv_proof_general).
pub(crate) use type_resolve::resolve_qualified_int_constant;
// Re-export type constant resolution for external use (trust-wp-driver via lib.rs)
pub use type_resolve::type_constants_for_int;
pub(in crate::encoder) use var_env::VarEnv;

use crate::{error::EncodingError, memory_model::MemState};

/// Threshold (total footprint size) for switching from cross-pair to quantified
/// disjointness in separating conjunction encoding. When
/// `left_locs.len() + right_locs.len()` reaches this value AND the solver supports
/// quantifiers, the encoder uses UF domain predicates with a quantified assertion:
///
/// ```text
/// D_left(loc_i) = true, D_right(loc_j) = true,
/// forall x. D_left(x) => !D_right(x)  [trigger: D_left(x)]
/// ```
///
/// instead of O(L*R) pairwise `l != r` constraints.
///
/// For left-recursive chains of N elements, the top-level `SepConj` has (N-1) + 1
/// total locations. With threshold 8, chains of 8+ elements use quantified encoding.
/// Cross-pair is preferred for small footprints where ground reasoning is faster.
#[cfg(any(test, feature = "sep-logic"))]
pub(super) const TRUST_WP_QUANTIFIED_DISJOINTNESS_THRESHOLD: usize = 8;

/// Maximum recursion depth for encoding `PureExpr` and `Formula` trees.
///
/// Pathologically deep ASTs can cause stack overflows since the encoder
/// traverses them recursively. This limit is checked at each recursive
/// entry point (`encode` and `encode_pure_impl`) and returns
/// `EncodingError::unsupported` when exceeded. The value is chosen to be
/// safely below the stack-overflow threshold in debug/test builds (test
/// threads use 2 MB stacks) while remaining far above any realistic user
/// contract depth. `128` was calibrated from failing `201`-depth tests in
/// shared default-stack test runs. (#1116)
pub(crate) const MAX_ENCODING_DEPTH: usize = 128;

// RAII guards (DepthGuard, PathConditionGuard) live in `guards.rs` (#2655).
use guards::{DepthGuard, PathConditionGuard};

/// Strict domain sort lookup that replaces silent `Sort::Int` fallbacks (#1608).
///
/// Returns `Err(EncodingError::SortInference)` when `idx` is out of bounds,
/// providing a diagnosable failure instead of defaulting to `Sort::Int`.
pub(crate) fn require_domain_sort(
    domain: &[Sort],
    idx: usize,
    context: &str,
) -> Result<Sort, EncodingError> {
    domain.get(idx).cloned().ok_or_else(|| {
        EncodingError::sort_inference(
            context,
            format!(
                "domain has {} sorts but index {idx} requested",
                domain.len()
            ),
        )
    })
}

/// Encoder for translating separation logic to ay.
///
/// # Push/Pop Policy (ay#3664, #1698)
///
/// ay-dpll's `Solver::push()`/`pop()` historically had soundness issues due to
/// an underspecified `TheorySolver` push/pop contract (ay#3664). The contract
/// is now formalized and all theory solvers comply.
///
/// **Production usage:** Push/pop is used only for obligation slicing in
/// `verify/function/mod.rs` and `verify/mut_borrow/mod.rs`, where multiple
/// postconditions are checked against a shared base context. This is the
/// canonical incremental solving pattern and is safe under the ay contract.
///
/// **Other verification boundaries** (loop sub-proofs, proof_assert, etc.)
/// create a fresh `AYEncoder` per obligation. Prefer fresh encoders when:
/// - Obligations have independent expression trees (different logic needs)
/// - Timeout isolation between phases is desired
/// - The base context is cheap to re-encode
///
/// Use push/pop only when the shared base context is expensive (preconditions,
/// body encoding, Skolemized existentials) and slices share the same logic.
///
/// Controls whether logic ground-pool flushing is enabled during `check_sat`.
///
/// Used by #1925 MBQI evaluation to compare current behavior (Enabled: manual
/// ground instantiation + automatic MBQI fallback) against MBQI-only (Disabled:
/// skip ground-pool flushing, rely on ay-dpll's automatic MBQI).
///
/// This does NOT gate `assert_recursive_logic_fn_ground_instances` or
/// `assert_standard_ground_instances` — only the generalized ground-pool
/// flushing path in `assert_ground_pool_instances()`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) enum LogicGroundInstantiationMode {
    /// Ground-pool flushing enabled (default).
    #[default]
    Enabled,
    /// Ground-pool flushing disabled — relies on ay-dpll MBQI.
    Disabled,
}

#[derive(Clone, Debug)]
pub(crate) struct DirectViewFn {
    pub(crate) full_path: String,
    pub(crate) param: String,
    pub(crate) param_sort: Option<ExprSort>,
    pub(crate) body: PureExpr,
}

#[derive(Clone, Debug)]
pub(crate) struct ViewReturnFn {
    pub(crate) full_path: String,
    pub(crate) param_sort: Option<ExprSort>,
    pub(crate) return_sort: Sort,
}

pub struct AYEncoder {
    /// The ay solver instance — the primary SMT interface.
    ///
    /// **Intentionally `pub(crate)`:** solver is the external SMT dependency,
    /// not internal encoder state. Every encoding operation needs it (1176
    /// `self.solver` accesses across 50 encoder/ files). Production code in
    /// `verify/` already uses the `solver()` / `solver_mut()` accessors
    /// exclusively; `pub(crate)` remains for test convenience (~1900 test
    /// accesses across 67 files). See the `solver()` / `solver_mut()`
    /// accessors in `encoder::solver`.
    /// (#1584 architectural decision)
    pub(crate) solver: Solver,
    /// Current memory state (heap, domain, permissions)
    ///
    /// Visibility: private — production accesses in encoder/{heap,sep_logic,quantifier/}.
    /// Tests use mem_state_for_test() accessors. (#1584)
    #[cfg_attr(not(test), allow(dead_code))]
    // accessed via self.mem_state in encoder/{heap,sep_logic,shell/path}.rs
    mem_state: MemState,
    /// Shell-owned variable environment for declared terms, tracked sorts, and
    /// unit-sorted markers. (#1584)
    var_env: VarEnv,
    /// Function and datatype declarations registry (#840).
    ///
    /// Visibility: private — encoder/ submodules access directly.
    /// verify/ production code uses decls() read accessor.
    /// Tests use decls() for reads, decls_for_test_mut() for writes. (#1584)
    decls: DeclarationState,
    /// Separation logic caching state for `SepConj` encoding (#840).
    #[cfg(any(test, feature = "sep-logic"))]
    sep_cache: SepConjCache,
    /// Side-effect assertion state and quantified-disjointness lazy recheck pipeline.
    assertion_pipeline: AssertionPipelineState,
    /// Sort resolution, type constants, and one-shot axiom dedup state (#840).
    /// Visibility: private — all external accesses use sort_resolver_for_test() accessor. (#1584)
    sort_resolver: SortResolverState,
    /// Quantifier variable naming and scope tracking state (#840).
    quantifier_state: QuantifierState,
    /// Seq sort and function declaration state (#840).
    ///
    /// Visibility: private — external tests use seq_state_for_test() accessors. (#1584)
    seq_state: SeqState,
    /// Recursion depth, path-condition stack, and solver configuration for
    /// encoding traversal. Includes `logic` and `supports_quantifiers` which
    /// were previously top-level fields (#2655).
    traversal: TraversalState,
    /// Ground-term pool for generalized E-matching workaround (#994).
    ///
    /// Collects ground function applications during encoding so that the
    /// verification layer can assert targeted ground instances of quantified
    /// axioms before `check_sat()`. This compensates for ay-dpll's single-round
    /// E-matching limitation.
    ///
    /// Visibility: private -- production accesses in encoder/ submodules.
    /// Tests use ground_pool_for_test() accessors. (#1584)
    ground_pool: ground_pool::GroundTermPool,
    /// Per-solve record of which quantified FMap universals were actually
    /// asserted by `assert_fmap_axioms` (CAP-80 staged retirement).
    ///
    /// Fail-closed default `false`: the FMap ground pool is retained whenever
    /// a universal was NOT asserted (`Logic::All` len-proxy mode, non-Int
    /// legacy insert signature, missing `fmap_insert` decl, or direct encoder
    /// users that never call `assert_fmap_axioms`). Ordering doc-pin: the
    /// flags are valid only because `assert_fmap_axioms` runs before every
    /// ground-pool flush — see `ground_pool::retirement` module docs.
    fmap_quantified_coverage: ground_pool::retirement::FmapQuantifiedCoverage,
    /// Test-only override for the ground-pool retirement stage (mirrors
    /// `GroundTermPool::per_slice_budget_override`). Production reads the
    /// `TRUST_WP_GROUND_POOL_RETIREMENT_STAGE` env var through a OnceLock,
    /// which is racy to toggle per-test; tests set this instead.
    retirement_stage_override: Option<u8>,
    /// ADT declaration and field range constraint state (#1584, #1982, #2097).
    adt_state: AdtState,
    /// Deduplicates struct field placeholder alias axioms.
    struct_field_alias_axioms: HashSet<String>,
    /// Deduplicates the permutation/exchange equivalence + bridge axiom bundle.
    ///
    /// Keyed by the monomorphized UF symbol the axiom group is asserted over
    /// (e.g. `method_permutation_of_2_...`), so each bundle is emitted at most
    /// once per Seq sort even when `permutation_of`/`exchange` is encoded many
    /// times across a function body. (#sorting-stage-a)
    permutation_exchange_axioms: HashSet<String>,
    /// Struct field placeholder applications observed during encoding.
    ///
    /// Unlike the generalized ground pool, this includes applications created
    /// while encoding quantifier bodies. Loop obligations can later use the same
    /// receiver at ground level, and the final field-alias pass needs these
    /// applications to emit concrete placeholder/native/length bridges.
    struct_field_ground_applications: Vec<(String, Term, Term)>,
    /// Single-parameter predicate closures lowered to Mapping constants
    /// (#985, #2316). Each entry is `(closure_map, bound_var, body_int)`,
    /// recorded by `encode_closure_in_logic` when a closure such as
    /// `c@ == |z: u32| z@ % 2 == 0` becomes a fresh Mapping constant
    /// `closure_map` with the defining axiom
    /// `forall z. mapping_get(closure_map, z) == body_int`. That quantified
    /// axiom guides ay-dpll's single-round E-matching, which routinely fails
    /// to instantiate at the obligation's concrete keys. The Mapping
    /// ground-instance flush re-materializes
    /// `mapping_get(closure_map, k) == body_int[bound_var := k]` for each
    /// observed key `k` — a sound ground instance of the asserted universal.
    closure_mapping_axioms: Vec<(Term, Term, Term)>,
    /// Enum-payload / UF-constructor bridge UNIVERSALS recorded for the vacuity
    /// base-recheck exemption (#result_own). Each entry is a `forall` axiom that
    /// the encoder emits to DEFINE a fresh projection/coercion symbol
    /// (`enum_payload_get_N`, `__trust_wp_uf_ctor_coerce_*`) in terms of the
    /// native datatype selectors/testers — e.g.
    /// `forall x. is_Ok(x) => enum_payload_get_0(x) = ownresult_ok_0(x)`.
    ///
    /// These are a conservative DEFINITIONAL extension over a fresh symbol: they
    /// never constrain the base's real variables except through that symbol, and
    /// the encoder ALSO emits their ground consequences at every observed
    /// receiver. On the SAT-side vacuity base recheck they are pure churn: ay's
    /// batch solver reports `quantifier-unhandled` whenever they are present (it
    /// never returns SAT), while the identical ground fragment is SAT in
    /// milliseconds. Recorded by identity (only the encoder's own bridge-emitter
    /// tags, never a user-authored precondition forall) so the base recheck can
    /// exempt EXACTLY these from a native, model-validated fresh SAT check. See
    /// `replay_native_base_exempting_bridge_foralls`.
    enum_payload_bridge_forall_terms: Vec<Term>,
    /// Stable receiver-to-datatype bridge constants for native selector fallback.
    ///
    /// Generic/erased receivers can be declared with an uninterpreted ay sort
    /// while the extracted Rust sort says a datatype field selector is valid.
    /// Reusing the bridge per receiver/datatype keeps repeated field accesses
    /// to the same logical value connected.
    datatype_selector_bridges: HashMap<(Term, DatatypeSort), Term>,
    /// Ground-term tracking for injective bridge UFs.
    ///
    /// Structural-sort and Seq coercion bridges use exact per-application
    /// injectivity instances instead of global quantifiers. Prior closed terms
    /// are recorded per bridge symbol so each newly observed pair gets
    /// `bridge(new) == bridge(old) => new == old`. (#2699)
    injective_bridge_ground_terms: HashMap<String, Vec<Term>>,
    /// Closure body inlining state (#1584, #2151 Phase 2).
    closure_state: ClosureState,
    /// Open Seq-returning `View::view` bodies that can be instantiated directly
    /// for `@` terms, avoiding a quantified `logic_view` axiom.
    direct_view_fns: Vec<DirectViewFn>,
    /// Declared return sorts for one-argument `View::view` functions, including
    /// opaque/trusted views whose bodies cannot be inlined.
    view_return_fns: Vec<ViewReturnFn>,
    /// Arithmetic mode flags and division obligations (#2655).
    arithmetic_mode: ArithmeticModeState,
    /// Encoding caches, solve diagnostics, option assertions, ext_eq registry,
    /// sort inference cache, and logic ground instantiation mode (#2655).
    encoding_cache: EncodingCacheState,
    /// Solver-facing replay recorder for provenance and reducer handoff.
    replay_recorder: ReplayRecorder,
    /// RAII permit from the global solver instance limiter (#2710).
    ///
    /// In test builds, this limits the number of concurrent AYEncoder instances
    /// to prevent OOM from ~6700 tests each creating solver instances. The permit
    /// is acquired in `from_solver_and_mem_state()` and released on drop.
    /// See `test_solver_limiter` module for details.
    #[cfg(test)]
    _solver_permit: test_solver_limiter::SolverPermit,
}

// State structs (SepConjCache, FormulaCacheKey, SortResolverState, DeclarationState,
// QuantifierState, SeqValue, SeqState, AssertionPipelineState, SeqFunctions) live
// under encoder/state/. Re-exported above.

impl AYEncoder {
    /// Encode a formula as a ay term.
    ///
    /// # Contracts
    ///
    /// ```text
    /// REQUIRES: formula is a well-formed Formula variant.
    /// REQUIRES: Variables referenced in formula have been declared or will be auto-declared.
    ///
    /// ENSURES (Soundness): If Ok(term), then term is a semantically equivalent
    ///     ay SMT term. For formula F and model M: M |= F iff M |= term.
    ///
    /// ENSURES (Error): Err only if formula contains unsupported constructs
    ///     (e.g., unknown method calls, malformed expressions).
    /// ```
    ///
    /// # Errors
    /// Returns `EncodingError` when the formula contains unsupported constructs
    /// or when encoding nested expressions fails.
    #[cfg(any(test, feature = "sep-logic"))]
    pub fn encode(&mut self, formula: &Formula) -> Result<Term, EncodingError> {
        if self.traversal.recursion_depth == 0 {
            self.quantifier_state.clear_synthesized_triggers();
        }
        self.assertion_pipeline.mark_encoded();
        self.traversal.recursion_depth += 1;
        if self.traversal.recursion_depth > MAX_ENCODING_DEPTH {
            self.traversal.recursion_depth -= 1;
            return Err(EncodingError::unsupported(
                "formula nesting exceeds maximum depth",
            ));
        }
        let _guard = DepthGuard(&raw mut self.traversal.recursion_depth);
        match formula {
            Formula::True => Ok(self.solver.bool_const(true)),
            Formula::False => Ok(self.solver.bool_const(false)),
            Formula::Pure(expr) => self.encode_pure(expr),
            Formula::And(l, r) => {
                let lt = self.encode(l)?;
                let rt = self.encode(r)?;
                Ok(self.solver.and(lt, rt))
            }
            Formula::Or(l, r) => {
                let lt = self.encode(l)?;
                let rt = self.encode(r)?;
                Ok(self.solver.or(lt, rt))
            }
            Formula::Implies(l, r) => {
                let lt = self.encode(l)?;
                let rt = self.encode(r)?;
                Ok(self.solver.implies(lt, rt))
            }
            #[cfg(any(test, feature = "sep-logic"))]
            Formula::PointsTo {
                location,
                value,
                permission,
            } => self.encode_points_to(location, value, *permission),
            Formula::MutBorrow {
                var,
                current,
                final_val,
                id,
            } => self.encode_mut_borrow(var, current, final_val, id),
            #[cfg(any(test, feature = "sep-logic"))]
            Formula::SepConj(l, r) => self.encode_sep_conj(formula, l, r),
            #[cfg(any(test, feature = "sep-logic"))]
            Formula::MagicWand(ante, conseq) => self.encode_magic_wand(ante, conseq),
            Formula::Exists {
                var,
                var_sort,
                body,
                triggers,
                ..
            } => self.encode_exists(var, var_sort.clone(), body, triggers),
            Formula::Forall {
                var,
                var_sort,
                body,
                triggers,
                ..
            } => self.encode_forall(var, var_sort.clone(), body, triggers),
            // Formula is #[non_exhaustive]; required for cross-crate match.
            #[allow(unreachable_patterns)]
            _ => Err(EncodingError::unsupported(format!(
                "unhandled Formula variant: {formula:?}"
            ))),
        }
    }

    /// Encode a pure expression as a ay term.
    ///
    /// # Contracts
    ///
    /// ```text
    /// REQUIRES: expr is a well-formed PureExpr variant.
    /// REQUIRES: Referenced variables will be auto-declared as Sort::Int if not present.
    ///
    /// ENSURES (Soundness): If Ok(term), then term preserves semantics:
    ///     For expression E and valuation V: eval(E, V) = eval(term, V)
    ///
    /// ENSURES (Type preservation): Boolean expressions yield Bool terms;
    ///     integer expressions yield Int terms.
    ///
    /// ENSURES (Error): Err only for unsupported constructs (unknown methods, etc.)
    /// ```
    ///
    /// # Errors
    /// Returns `EncodingError` when the expression uses unsupported constructs
    /// (such as an unknown method call) or when a sub-expression fails to encode.
    /// Assert the negation of `ante ==> conseq` (i.e. `ante /\ !conseq`, the
    /// preservation goal for an implication invariant) and RETURN the consequent
    /// `Term` — a SINGLE encode of `conseq`. A proven-lemma close can then assert
    /// exactly that returned term true, creating a DIRECT `t /\ !t` propositional
    /// conflict rather than a freshly-encoded `P(..)` forall that only closes via
    /// a fragile (and here non-converging) E-matching loop. SOUND only when the
    /// caller has independently established that `conseq` is entailed by the
    /// asserted context (see `cons_tail_prophecy_gate`). (#994 all_zero_list)
    pub(crate) fn assert_negated_implication_capturing_consequent(
        &mut self,
        ante: &PureExpr,
        conseq: &PureExpr,
    ) -> Result<Term, EncodingError> {
        let t_ante = self.encode_pure(ante)?;
        self.assert_term(t_ante);
        let t_conseq = self.encode_pure(conseq)?;
        let not_conseq = self.solver.not(t_conseq);
        self.assert_term(not_conseq);
        Ok(t_conseq)
    }

    pub fn encode_pure(&mut self, expr: &PureExpr) -> Result<Term, EncodingError> {
        if self.traversal.recursion_depth == 0 {
            self.quantifier_state.clear_synthesized_triggers();
        }
        self.assertion_pipeline.mark_encoded();
        // Only scan if register_sort_hints hasn't been called already (verify.rs
        // callers pre-register all expressions up front, making per-call scans redundant).
        if !self.are_sort_hints_registered() {
            self.register_sort_hints(std::slice::from_ref(expr));
        }
        self.encode_pure_impl(expr, None)
    }

    /// Encode an expression in Bool formula context for postcondition/assertion
    /// encoding.
    ///
    /// Like [`encode_pure`] but with Bool-context awareness: seeds Bool context
    /// hints and routes Mapping/FMap predicate lookups (`index_logic`, `get`,
    /// etc.) through semantic dispatch with Bool coercion. This prevents sort
    /// mismatches when negating postconditions that contain predicate
    /// applications like `predicate[-y@ - 1]`. (#2245)
    pub(crate) fn encode_formula(&mut self, expr: &PureExpr) -> Result<Term, EncodingError> {
        if self.traversal.recursion_depth == 0 {
            self.quantifier_state.clear_synthesized_triggers();
        }
        self.assertion_pipeline.mark_encoded();
        if !self.are_sort_hints_registered() {
            self.register_sort_hints(std::slice::from_ref(expr));
        }
        self.encode_bool_context_operand(expr, None)
    }

    // `axiom_apply` and `safe_apply` moved to `ay_api.rs` (#2131).

    // `propagate_seq_value` and `propagate_body_view_seq_value_to_result`
    // moved to `shell/seq_propagation.rs` (#2655).
}

impl Default for AYEncoder {
    fn default() -> Self {
        Self::new()
    }
}
