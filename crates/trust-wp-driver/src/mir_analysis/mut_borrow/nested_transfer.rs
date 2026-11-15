// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Nested-reborrow transfer call recognition (rusthorn `inc_max_3` class).
//!
//! A *transfer call* moves whole mutable borrows between rebindable mut-ref
//! parameter slots without touching their pointees, e.g. Creusot's
//!
//! ```text
//! #[ensures(^mma == *mmb && ^mmb == *mma)]
//! fn swap<'a, 'b>(mma: &'a mut &'b mut u32, mmb: &'a mut &'b mut u32);
//! ```
//!
//! called as `swap(&mut ma, &mut mb)` where `ma`/`mb` are `&mut u32` parameter
//! locals. RustHorn semantics: the call-scoped reborrows `&mut ma`/`&mut mb`
//! expire immediately after the call, so `^mma` (the value of the LOCAL `ma`
//! after the call) is `*mmb` = the borrow that local `mb` held before — the
//! contract is exactly a permutation of the slots' contents, at the WHOLE
//! borrow level (current, prophecy, and identity travel together).
//!
//! The legacy instantiation path collapses the two reference levels
//! (`^mma` ↦ `Final(Var("ma"))` = the prophecy of the *entry* borrow), which
//! both mis-states the fact and drops the final-value chaining for the entry
//! borrows. This module recognizes the shape so the traversal can instead
//! forward-simulate the permutation on tracked slot contents
//! (`state.slot_exprs`) and pointee values (`state.deref_exprs`), from which
//! the exact per-path expiry resolutions are emitted at function exit (see
//! `entry.rs`). The recognizer is deliberately strict — any deviation returns
//! `None` and the legacy (conservative) path is used.

use rustc_middle::mir::Operand;
use trust_wp_core::formula::{BinOp, PureExpr};
use trust_wp_driver::StdSpec;

use super::{
    data::{MutBorrowBlockContext, MutBorrowTraversalState},
    spec_advancement::lookup_call_spec,
};
use crate::mir_analysis::call_resolve::{arg_names_for_def_id, extract_call_def_id};

/// Parse a spec's ensures clauses as a pure whole-borrow transfer permutation
/// over the callee's parameter `names`.
///
/// Returns `perm` such that after the call, the slot passed for param `i`
/// holds the borrow previously held by the slot passed for param `perm[i]`.
///
/// Requirements (all must hold, else `None`):
/// - the spec has no preconditions;
/// - every ensures conjunct (clauses are `&&`-flattened) is exactly
///   `^p == *q` (either orientation) with `p`, `q` spec params;
/// - every spec param appears exactly once as a `^`-target and exactly once
///   as a `*`-source (a total permutation — fixed points `^p == *p` allowed).
pub(super) fn transfer_permutation(spec: &StdSpec, names: &[String]) -> Option<Vec<usize>> {
    if !spec.requires.is_empty() {
        return None;
    }
    let n = names.len();
    if n < 2 {
        return None;
    }
    let index_of = |name: &str| names.iter().position(|p| p == name);

    let mut perm: Vec<Option<usize>> = vec![None; n];
    let mut used_source: Vec<bool> = vec![false; n];
    let mut conjuncts: Vec<PureExpr> = Vec::new();
    for ensures_str in &spec.ensures {
        let parsed = trust_wp_core::contract_parser::parse_contract(ensures_str).ok()?;
        flatten_and(&parsed, &mut conjuncts);
    }
    if conjuncts.is_empty() {
        return None;
    }
    for conjunct in &conjuncts {
        let (target, source) = as_transfer_equation(conjunct)?;
        let ti = index_of(target)?;
        let si = index_of(source)?;
        if perm[ti].is_some() || used_source[si] {
            // Duplicate target/source constraint — not a clean permutation.
            return None;
        }
        perm[ti] = Some(si);
        used_source[si] = true;
    }
    // Total: every param's final is pinned by the permutation.
    perm.into_iter().collect()
}

/// Flatten `a && b && c` into individual conjuncts.
fn flatten_and(expr: &PureExpr, out: &mut Vec<PureExpr>) {
    if let PureExpr::BinOp(lhs, BinOp::And, rhs) = expr {
        flatten_and(lhs, out);
        flatten_and(rhs, out);
    } else {
        out.push(expr.clone());
    }
}

/// Match `Final(Var(p)) == Deref(Var(q))` (either orientation), returning
/// `(p, q)`.
fn as_transfer_equation(expr: &PureExpr) -> Option<(&str, &str)> {
    let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = expr else {
        return None;
    };
    if let (Some(t), Some(s)) = (final_var_name(lhs), deref_var_name(rhs)) {
        return Some((t, s));
    }
    if let (Some(t), Some(s)) = (final_var_name(rhs), deref_var_name(lhs)) {
        return Some((t, s));
    }
    None
}

fn final_var_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Final(inner) => match inner.as_ref() {
            PureExpr::Var(name, _) => Some(name),
            _ => None,
        },
        _ => None,
    }
}

fn deref_var_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Deref(inner) => match inner.as_ref() {
            PureExpr::Var(name, _) => Some(name),
            _ => None,
        },
        _ => None,
    }
}

/// Recognize a nested-reborrow transfer call at a `Call` terminator.
///
/// Returns `(dst_slot, src_slot)` pairs: after the call, `dst_slot` holds the
/// borrow previously held by `src_slot`. `None` when the call is not the
/// exact recognized shape (every argument a projection-less move/copy of a
/// tracked nested slot borrow from `state.slot_borrow_map`, distinct slots,
/// callee spec a pure transfer permutation over exactly those params).
pub(super) fn try_nested_transfer_advancement<'tcx>(
    ctx: &MutBorrowBlockContext<'_, 'tcx>,
    func: &Operand<'tcx>,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
    state: &MutBorrowTraversalState,
) -> Option<Vec<(rustc_middle::mir::Local, rustc_middle::mir::Local)>> {
    let def_id = extract_call_def_id(func)?;
    let spec = lookup_call_spec(ctx, func, def_id)?;
    // User/trait spec tables carry `param_names: None`; resolve the callee's
    // parameter names from its DefId in that case (local fns only — external
    // fns without stored names are rejected, keeping the gate strict).
    let names = spec
        .param_names
        .clone()
        .or_else(|| arg_names_for_def_id(ctx.tcx, def_id))?;
    let perm = transfer_permutation(&spec, &names)?;
    if args.len() != perm.len() {
        return None;
    }

    let mut slots = Vec::with_capacity(args.len());
    for arg in args {
        let local = match &arg.node {
            Operand::Copy(place) | Operand::Move(place) if place.projection.is_empty() => {
                place.local
            }
            _ => return None,
        };
        let slot = *state.slot_borrow_map.get(&local)?;
        if slots.contains(&slot) {
            return None;
        }
        slots.push(slot);
    }

    Some(
        perm.iter()
            .enumerate()
            .map(|(i, &src)| (slots[i], slots[src]))
            .collect(),
    )
}

/// Whether any call argument is a tracked nested slot borrow. Used to poison
/// nested-slot content tracking when such a borrow escapes into a call the
/// transfer recognizer did not handle (the callee could rebind the slot in
/// ways the analysis does not model).
pub(super) fn args_touch_nested_slots<'tcx>(
    args: &[rustc_span::Spanned<Operand<'tcx>>],
    state: &MutBorrowTraversalState,
) -> bool {
    args.iter().any(|arg| match &arg.node {
        Operand::Copy(place) | Operand::Move(place) => {
            state.slot_borrow_map.contains_key(&place.local)
        }
        Operand::Constant(_) | Operand::RuntimeChecks(_) => false,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn spec(ensures: &[&str], requires: &[&str]) -> StdSpec {
        StdSpec {
            inv_requires: Vec::new(),
            capture_inv_requires: Vec::new(),
            requires: requires.iter().map(|s| (*s).to_string()).collect(),
            ensures: ensures.iter().map(|s| (*s).to_string()).collect(),
            param_names: None,
        }
    }

    fn names(params: &[&str]) -> Vec<String> {
        params.iter().map(|s| (*s).to_string()).collect()
    }

    #[test]
    fn recognizes_creusot_swap_contract() {
        let s = spec(&["^mma == *mmb && ^mmb == *mma"], &[]);
        assert_eq!(
            transfer_permutation(&s, &names(&["mma", "mmb"])),
            Some(vec![1, 0])
        );
    }

    #[test]
    fn recognizes_split_clause_swap_contract() {
        let s = spec(&["^mma == *mmb", "^mmb == *mma"], &[]);
        assert_eq!(
            transfer_permutation(&s, &names(&["mma", "mmb"])),
            Some(vec![1, 0])
        );
    }

    #[test]
    fn recognizes_reversed_orientation() {
        let s = spec(&["*mmb == ^mma", "*mma == ^mmb"], &[]);
        assert_eq!(
            transfer_permutation(&s, &names(&["mma", "mmb"])),
            Some(vec![1, 0])
        );
    }

    #[test]
    fn rejects_partial_permutation() {
        // Only one param's final pinned — mmb's final unconstrained.
        let s = spec(&["^mma == *mmb"], &[]);
        assert_eq!(transfer_permutation(&s, &names(&["mma", "mmb"])), None);
    }

    #[test]
    fn rejects_value_level_contract() {
        // Value-level (view) swap `(^mma)@ == (*mmb)@` is not a whole-borrow
        // transfer (parses as View(..) == View(..), not Final == Deref).
        let s = spec(&["(^mma)@ == (*mmb)@ && (^mmb)@ == (*mma)@"], &[]);
        assert_eq!(transfer_permutation(&s, &names(&["mma", "mmb"])), None);
    }

    #[test]
    fn rejects_extra_clauses() {
        let s = spec(&["^mma == *mmb && ^mmb == *mma", "result == 0"], &[]);
        assert_eq!(transfer_permutation(&s, &names(&["mma", "mmb"])), None);
    }

    #[test]
    fn rejects_spec_with_preconditions() {
        let s = spec(&["^mma == *mmb && ^mmb == *mma"], &["*mma != *mmb"]);
        assert_eq!(transfer_permutation(&s, &names(&["mma", "mmb"])), None);
    }

    #[test]
    fn rejects_duplicate_source() {
        let s = spec(&["^mma == *mmb && ^mmb == *mmb"], &[]);
        assert_eq!(transfer_permutation(&s, &names(&["mma", "mmb"])), None);
    }

    #[test]
    fn accepts_identity_fixed_points() {
        let s = spec(&["^mma == *mma", "^mmb == *mmb"], &[]);
        assert_eq!(
            transfer_permutation(&s, &names(&["mma", "mmb"])),
            Some(vec![0, 1])
        );
    }

    #[test]
    fn recognizes_three_way_rotation() {
        let s = spec(&["^a == *b", "^b == *c", "^c == *a"], &[]);
        assert_eq!(
            transfer_permutation(&s, &names(&["a", "b", "c"])),
            Some(vec![1, 2, 0])
        );
    }
}
