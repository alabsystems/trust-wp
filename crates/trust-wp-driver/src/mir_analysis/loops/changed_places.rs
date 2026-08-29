// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Changed-place tracking for loop body analysis (#1816).
//!
//! Tracks sub-place granularity of modifications (fields, derefs) so unchanged
//! siblings of a modified struct can retain their pre-loop value as auto-inferred
//! invariants.

use std::collections::{HashMap, HashSet};

use rustc_middle::{
    mir::{Body, Local, Operand, ProjectionElem, Rvalue, StatementKind, TerminatorKind},
    ty::TyKind,
};
use trust_wp_core::formula::{NamedBindingValue, PureExpr};

use super::{detection::LoopInfo, UnresolvedPreLoopCall};

/// Tree of sub-place changes (#1816).
///
/// Mirrors Creusot's `ChangedPlacesTree` from `invariants.rs`. Tracks writes at
/// sub-place granularity (fields, derefs) so unchanged siblings of a modified
/// struct can retain their pre-loop value as auto-inferred invariants.
///
/// Conservative: any unsupported projection (Index, Downcast, etc.) falls back
/// to `Changed` at the current level, which marks the entire sub-tree as modified.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ChangedPlacesTree {
    /// The entire place (and all sub-places) is modified.
    Changed,
    /// Only the pointee behind a dereference is modified.
    Deref(Box<ChangedPlacesTree>),
    /// Only specific fields are modified. Unmentioned fields are unchanged.
    Fields(std::collections::BTreeMap<u32, ChangedPlacesTree>),
}

impl ChangedPlacesTree {
    /// Merge another tree into this one (union of changed places).
    pub(super) fn merge(&mut self, other: &ChangedPlacesTree) {
        match (self, other) {
            (s, ChangedPlacesTree::Changed) => *s = ChangedPlacesTree::Changed,
            (ChangedPlacesTree::Changed, _) => {}
            (ChangedPlacesTree::Deref(ref mut inner), ChangedPlacesTree::Deref(other_inner)) => {
                inner.merge(other_inner);
            }
            (
                ChangedPlacesTree::Fields(ref mut fields),
                ChangedPlacesTree::Fields(other_fields),
            ) => {
                for (idx, other_tree) in other_fields {
                    fields
                        .entry(*idx)
                        .and_modify(|existing| existing.merge(other_tree))
                        .or_insert_with(|| other_tree.clone());
                }
            }
            // Incompatible shapes → conservative fallback
            (s, _) => *s = ChangedPlacesTree::Changed,
        }
    }

    /// Returns true if this place is fully changed (no sub-structure to exploit).
    #[cfg(test)]
    pub(crate) fn is_fully_changed(&self) -> bool {
        matches!(self, ChangedPlacesTree::Changed)
    }

    /// Returns true if a specific field index is unchanged.
    #[cfg(test)]
    pub(crate) fn is_field_unchanged(&self, field_idx: u32) -> bool {
        match self {
            ChangedPlacesTree::Changed => false,
            ChangedPlacesTree::Deref(_) => true, // deref change doesn't affect fields
            ChangedPlacesTree::Fields(fields) => !fields.contains_key(&field_idx),
        }
    }
}

/// Per-variable changed-place trees for a loop body (#1816 Phase 2).
///
/// Wraps `HashMap<String, ChangedPlacesTree>` keyed by variable name. Variables
/// not present in the map are entirely unchanged. Variables whose tree is
/// `Changed` are fully modified (equivalent to the current flat `modified_vars`).
#[derive(Debug, Clone, Default)]
pub(crate) struct ChangedPlaces(pub(crate) HashMap<String, ChangedPlacesTree>);

#[cfg(test)]
impl ChangedPlaces {
    /// Returns true if the named variable has any changes at all.
    pub(crate) fn is_modified(&self, name: &str) -> bool {
        self.0.contains_key(name)
    }

    /// Returns true if the named variable is entirely unchanged.
    pub(crate) fn is_unchanged(&self, name: &str) -> bool {
        !self.0.contains_key(name)
    }

    /// Produce a conservative flat list of modified variable names (compatibility
    /// with existing `modified_vars: Vec<String>` API).
    pub(crate) fn to_modified_vars(&self) -> Vec<String> {
        self.0.keys().cloned().collect()
    }
}

/// Grouped for-loop ghost state extracted from MIR analysis (#2171).
///
/// For Creusot-style `for x in iter` loops, bundles all the ghost-variable
/// expressions needed to synthesize the structural invariant
/// `iter_old.produces(produced, iter_state)`, the initialization bindings
/// that tie the synthetic iterator-state variables back to MIR, and the
/// one-step transition fact used during preservation. (#2171)
#[derive(Debug, Clone)]
pub(crate) struct ForLoopGhostState {
    /// Name of the `produced` ghost variable (usually `"produced"`).
    pub(crate) produced_name: String,
    /// Snapshot of the iterator at loop entry (synthetic stable variable).
    pub(crate) iter_old: PureExpr,
    /// Synthetic current-state variable used in loop invariants/body effects.
    pub(crate) iter_state: PureExpr,
    /// MIR-recovered iterator expression at loop entry.
    pub(crate) iter_state_binding: PureExpr,
    /// Synthetic post-step iterator-state witness for one loop iteration.
    pub(crate) iter_state_next: PureExpr,
    /// Yielded loop element for the current `Iterator::next` step.
    pub(crate) loop_elem: PureExpr,
    /// The original iterable expression from `IntoIterator::into_iter(iterable)`,
    /// when it can be represented as a sequence-valued payload.
    pub(crate) iterable: Option<PureExpr>,
    /// Range bounds for `for elem in start..end` loops.
    ///
    /// When the iterator is a range type, these hold the (start, end) expressions
    /// recovered from the MIR pre-header. Used to synthesize element bounds like
    /// `elem >= start` as loop invariants for nested loop inheritance. (#1709)
    pub(crate) range_bounds: Option<(PureExpr, PureExpr)>,
}

/// Expression components of a loop body for verification.
#[derive(Debug, Clone)]
pub(crate) struct LoopBodyExpr {
    /// Loop condition (if extractable)
    pub(crate) condition: Option<PureExpr>,
    /// Whether the condition was extracted from a body-break pattern (not the header).
    ///
    /// For `loop { body; if cond { break; } }`, the break condition is checked
    /// AFTER the body effects execute. In preservation, the condition should be
    /// applied to primed (post-body) variables, not the pre-body state. (#1295)
    pub(crate) condition_is_body_break: bool,
    /// Variables modified in the loop
    pub(crate) modified_vars: Vec<String>,
    /// Projection-aware changed-place trees for sub-place granularity (#1816).
    ///
    /// Augments `modified_vars` with structural information about which sub-places
    /// (fields, derefs) are actually written. Variables absent from this map are
    /// entirely unchanged. The flat `modified_vars` field is preserved for backward
    /// compatibility with the ay encoder.
    pub(crate) changed_places: ChangedPlaces,
    /// Body effects: maps variable name to its updated expression after one iteration
    pub(crate) body_effects: HashMap<String, PureExpr>,
    /// Deref body effects: maps variable name to the value written through `*var`.
    ///
    /// For `*x = 0` in a loop body, contains `{"x": Int(0)}`. The ay encoder
    /// uses this to constrain `x_prime_current = 0` during preservation, instead
    /// of havocing `x_prime` (which would make preservation fail spuriously). (#1295)
    pub(crate) deref_body_effects: HashMap<String, PureExpr>,
    /// Double-deref body effects: maps variable name to the value written through
    /// `**var`. For `**x = 0` where `x: &mut &mut i32`, the ay encoder constrains
    /// `x_prime_current_current = 0` during preservation. (#1295)
    pub(crate) double_deref_body_effects: HashMap<String, PureExpr>,
    /// Pre-loop assignments: maps variable name to its binding value at loop entry.
    ///
    /// For `let mut i = 0;` before a `while` loop, contains `{"i": NamedBindingValue { sort: Some(Int), value: Int(0) }}`.
    /// The `NamedBindingValue` preserves the MIR-derived sort of the symbolic
    /// variable so that loop VC builders can reconstruct typed equality constraints
    /// instead of falling back to `Var(name, None)`. (#2053)
    pub(crate) pre_loop_assignments: HashMap<String, NamedBindingValue>,
    /// Function parameters that are reassigned before loop entry (#2095).
    ///
    /// For `fn f(mut x: i32) { x += 1; while ... }`, contains `{"x"}`.
    /// Used by `rewrite_loop_postcondition_old` to reject `old(x)` when `x`
    /// no longer holds its function-entry value at loop entry.
    pub(crate) pre_loop_written_params: HashSet<String>,
    /// Unresolved pre-loop function calls that need TyCtxt to resolve. (#1295)
    ///
    /// Collected during MIR analysis (inside `MIR_BODIES.with`), then resolved
    /// by the caller using `resolve_pre_loop_calls(tcx, ...)` and merged into
    /// `pre_loop_assignments`.
    pub(crate) unresolved_pre_loop_calls: Vec<UnresolvedPreLoopCall>,
    /// Ref-chain source locals for borrow-chain resolution in pre-loop calls. (#2665)
    ///
    /// When MIR has `_ref = &_call_result`, records `_ref → _call_result` so the
    /// multi-pass resolver can follow borrows through to the underlying call result.
    /// Used by `resolve_pre_loop_call_locals_inner` to resolve chains like
    /// `view(x) → &view_result → Snapshot::capture(&view_result)`.
    pub(crate) ref_source_locals: HashMap<Local, Local>,
    /// Named `&mut`-borrow → backing-local name map (e.g. `bor_k → k` for
    /// `let bor_k = &mut k`). Derived from `ref_source_locals` restricted to
    /// pairs where both the borrow and its referent are named locals. Used by
    /// the FMap single-entry identity bridge to resolve a backing local's
    /// post-loop value to its borrow's prophecy (`k == ^bor_k`). (cc/fmap layer d)
    pub(crate) borrow_backing_names: HashMap<String, String>,
    /// Pre-loop postcondition facts from calls before loop entry.
    ///
    /// Unlike `pre_loop_assignments`, these facts are predicate-style
    /// postconditions such as `result@.len() == count@`. The loop verifier
    /// threads them only into the initialization VC via `init_extra_facts`.
    pub(crate) pre_loop_init_facts: Vec<PureExpr>,
    /// Return expression: the value assigned to `_0` (return place) in post-loop blocks.
    ///
    /// For `fn count_to_n(n: i32) -> i32 { while i < n { i += 1; } i }`,
    /// this is `Var("i")`. Used to bind `result` in postcondition checking (#622).
    pub(crate) return_expr: Option<PureExpr>,
    /// Variables whose pointee is mutated after loop exit and before return.
    ///
    /// For `while *v < 10 { *v += 1; } *v = 42;`, this contains `{"v"}`.
    /// Loop-level postcondition checks must not resolve `v_final == v_current`
    /// in this case because function-level code mutates `*v` after the loop. (#1823)
    pub(crate) post_loop_deref_writes: HashSet<String>,
    /// Symbolic final values for post-loop deref writes (#2085).
    ///
    /// Maps `&mut` parameter names to the expression assigned through their pointee
    /// after the loop exits. For `*x = n` after the loop, contains `{"x" -> Var("n")}`.
    /// Used to synthesize `final_values` for `verify_mut_borrow_function_with_modes`
    /// when `extract_mut_borrow_body` bails due to loop cycle detection.
    pub(crate) post_loop_deref_final_values: HashMap<String, PureExpr>,
    /// For Creusot-style for-loops: grouped ghost state for structural invariant
    /// synthesis and init/completion facts (#2171).
    ///
    /// Contains the `produced` name, synthetic iterator-state variables, and
    /// the iterable payload. When `Some`, the loop verifier can synthesize the
    /// structural invariant plus the one-step iterator transition fact.
    pub(crate) for_loop_state: Option<ForLoopGhostState>,
}

/// Collect variable names modified by assignments and call destinations in the
/// loop body.
///
/// Also follows reborrow chains so writes through temporaries produced by
/// `IndexMut::index_mut`, `&mut` reborrows, or `move`/`copy` of a named local
/// are attributed to the underlying named local (#1816, Wave 7A).
pub(super) fn extract_modified_vars(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    local_to_name: &HashMap<Local, String>,
) -> Vec<String> {
    let mut modified_locals: HashSet<Local> = HashSet::new();
    let alias_map = build_borrow_alias_map(body, loop_info, local_to_name);
    for &bb in &loop_info.body_blocks {
        let bb_data = &body.basic_blocks[bb];
        for stmt in &bb_data.statements {
            if let StatementKind::Assign(box (place, _)) = &stmt.kind {
                modified_locals.insert(place.local);
                // Writes through a borrow temp (`*_tmp = ...`) should attribute
                // to the underlying named local. (#1816, Wave 7A)
                if has_leading_deref(place.projection) && !local_to_name.contains_key(&place.local)
                {
                    if let Some(target) = alias_map.get(&place.local) {
                        modified_locals.insert(*target);
                    }
                }
            }
        }
        if let TerminatorKind::Call { destination, .. } = &bb_data.terminator().kind {
            modified_locals.insert(destination.local);
        }
    }
    modified_locals
        .iter()
        .filter_map(|local| local_to_name.get(local).cloned())
        .collect()
}

/// Extract projection-aware changed-place trees from loop body assignments (#1816).
///
/// Walks all assignments and call destinations in the loop body, recording the
/// projection path (Field, Deref) as a `ChangedPlacesTree`. This provides sub-place
/// granularity: if only `x.field_0` is written, `x.field_1` remains unchanged.
///
/// Also follows reborrow chains: when `_tmp = IndexMut::index_mut(&mut v, i)`
/// (or any mutable reborrow) is followed by `*_tmp = ...`, the write is attributed
/// to `v` as `Deref(Changed)` so `v` is correctly marked as modified even though
/// the deref-write goes through an unnamed temporary. (Wave 7A)
///
/// Unsupported projections (Index, Downcast, ConstantIndex, Subslice) fall back
/// to `ChangedPlacesTree::Changed` at the current level (conservative).
pub(super) fn extract_changed_places(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    local_to_name: &HashMap<Local, String>,
) -> ChangedPlaces {
    let mut trees: HashMap<String, ChangedPlacesTree> = HashMap::new();
    let alias_map = build_borrow_alias_map(body, loop_info, local_to_name);

    let record = |local: Local,
                  projection: &[ProjectionElem<Local, rustc_middle::ty::Ty<'_>>],
                  trees: &mut HashMap<String, ChangedPlacesTree>| {
        if let Some(name) = local_to_name.get(&local) {
            let tree = place_projection_to_tree(projection);
            trees
                .entry(name.clone())
                .and_modify(|existing| existing.merge(&tree))
                .or_insert(tree);
            return;
        }
        // Unnamed local — if it's a deref-write through a tracked borrow temp,
        // attribute the change to the underlying named local. (Wave 7A)
        if !has_leading_deref(projection) {
            return;
        }
        let Some(target) = alias_map.get(&local) else {
            return;
        };
        let Some(name) = local_to_name.get(target) else {
            return;
        };
        // Strip the leading Deref since the alias already accounts for the
        // borrow indirection (the write is effectively `Deref(...)` at the
        // named-local level).
        let inner_tree = place_projection_to_tree(&projection[1..]);
        let tree = ChangedPlacesTree::Deref(Box::new(inner_tree));
        trees
            .entry(name.clone())
            .and_modify(|existing| existing.merge(&tree))
            .or_insert(tree);
    };

    for &bb in &loop_info.body_blocks {
        let bb_data = &body.basic_blocks[bb];
        for stmt in &bb_data.statements {
            if let StatementKind::Assign(box (place, _)) = &stmt.kind {
                record(place.local, place.projection, &mut trees);
            }
        }
        if let TerminatorKind::Call { destination, .. } = &bb_data.terminator().kind {
            record(destination.local, destination.projection, &mut trees);
        }
    }

    ChangedPlaces(trees)
}

/// Returns true when the projection starts with a `Deref` step.
fn has_leading_deref(projection: &[ProjectionElem<Local, rustc_middle::ty::Ty<'_>>]) -> bool {
    matches!(projection.first(), Some(ProjectionElem::Deref))
}

/// Build a map from unnamed reborrow temporaries to the underlying named local.
///
/// Tracks three reborrow patterns inside the loop body:
///
/// 1. `_tmp = &mut <named>` (or `&named`) — direct borrow of a named place.
/// 2. `_tmp = move/copy _src` (no projection) or `_tmp = move/copy (*_src)` —
///    alias copy or reborrow through an existing alias.
/// 3. Call terminator `_tmp = call(arg0, ..)` where the destination has a
///    reference/pointer return type and any argument resolves to a tracked
///    base. This conservatively captures `IndexMut::index_mut`,
///    `Index::index`, `DerefMut::deref_mut`, and similar borrow-returning
///    methods without requiring call resolution.
///
/// We iterate to a small fixed bound to propagate transitive aliases (a single
/// reborrow chain in MIR rarely exceeds 4 hops).
fn build_borrow_alias_map(
    body: &Body<'_>,
    loop_info: &LoopInfo,
    local_to_name: &HashMap<Local, String>,
) -> HashMap<Local, Local> {
    let mut alias: HashMap<Local, Local> = HashMap::new();

    let resolve = |alias: &HashMap<Local, Local>,
                   local: Local,
                   local_to_name: &HashMap<Local, String>|
     -> Option<Local> {
        if local_to_name.contains_key(&local) {
            return Some(local);
        }
        alias.get(&local).copied()
    };

    // Up to 8 passes to propagate transitively through reborrow chains.
    for _ in 0..8 {
        let mut changed = false;
        for &bb in &loop_info.body_blocks {
            let bb_data = &body.basic_blocks[bb];
            for stmt in &bb_data.statements {
                let StatementKind::Assign(box (place, rvalue)) = &stmt.kind else {
                    continue;
                };
                if !place.projection.is_empty() {
                    continue;
                }
                let dst = place.local;
                if local_to_name.contains_key(&dst) {
                    continue;
                }
                let target = match rvalue {
                    // _tmp = &(mut)? <place>
                    Rvalue::Ref(_, _, src_place) | Rvalue::RawPtr(_, src_place) => {
                        resolve(&alias, src_place.local, local_to_name)
                    }
                    // _tmp = move/copy <place> (no projection or single Deref)
                    Rvalue::Use(Operand::Copy(src_place) | Operand::Move(src_place), _)
                        if src_place.projection.is_empty()
                            || (src_place.projection.len() == 1
                                && matches!(
                                    src_place.projection.first(),
                                    Some(ProjectionElem::Deref)
                                )) =>
                    {
                        resolve(&alias, src_place.local, local_to_name)
                    }
                    _ => None,
                };
                if let Some(t) = target {
                    if alias.get(&dst) != Some(&t) {
                        alias.insert(dst, t);
                        changed = true;
                    }
                }
            }

            // Call terminator: `_tmp = f(arg0, ..)` where `_tmp` has reference/
            // pointer return type. Attribute the borrow to whichever argument
            // resolves to a tracked base.
            if let TerminatorKind::Call {
                args, destination, ..
            } = &bb_data.terminator().kind
            {
                if !destination.projection.is_empty() {
                    continue;
                }
                let dst = destination.local;
                if local_to_name.contains_key(&dst) {
                    continue;
                }
                let dst_ty = body.local_decls[dst].ty;
                if !is_borrow_like_ty(dst_ty) {
                    continue;
                }
                let target = args.iter().find_map(|spanned| match &spanned.node {
                    Operand::Copy(p) | Operand::Move(p) => resolve(&alias, p.local, local_to_name),
                    Operand::Constant(_) | Operand::RuntimeChecks(_) => None,
                });
                if let Some(t) = target {
                    if alias.get(&dst) != Some(&t) {
                        alias.insert(dst, t);
                        changed = true;
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    alias
}

/// Returns true when the given type is a reference or raw pointer.
fn is_borrow_like_ty(ty: rustc_middle::ty::Ty<'_>) -> bool {
    matches!(ty.kind(), TyKind::Ref(..) | TyKind::RawPtr(..))
}

/// Convert a MIR projection list to a `ChangedPlacesTree`.
///
/// Empty projection → `Changed` (whole-variable assignment).
/// `[Field(idx)]` → `Fields({idx: Changed})`.
/// `[Deref]` → `Deref(Changed)`.
/// `[Deref, Field(idx)]` → `Deref(Fields({idx: Changed}))`.
/// Unsupported projections → `Changed` (conservative fallback).
pub(super) fn place_projection_to_tree(
    projection: &[ProjectionElem<Local, rustc_middle::ty::Ty<'_>>],
) -> ChangedPlacesTree {
    if projection.is_empty() {
        return ChangedPlacesTree::Changed;
    }

    // Build from innermost to outermost
    let mut tree = ChangedPlacesTree::Changed;
    for elem in projection.iter().rev() {
        tree = match elem {
            ProjectionElem::Field(field_idx, _ty) => {
                let mut fields = std::collections::BTreeMap::new();
                fields.insert(field_idx.as_u32(), tree);
                ChangedPlacesTree::Fields(fields)
            }
            ProjectionElem::Deref => ChangedPlacesTree::Deref(Box::new(tree)),
            // Index, Downcast, ConstantIndex, Subslice, OpaqueCast, Subtype —
            // conservatively mark as fully changed.
            _ => ChangedPlacesTree::Changed,
        };
    }
    tree
}
