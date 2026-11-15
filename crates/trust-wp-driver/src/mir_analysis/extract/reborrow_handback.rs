// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Call-site handback of a fresh `&mut` reborrow's prophecy, for the
//! arithmetic-panic region walk.
//!
//! The region walk re-binds every address-taken local to fresh havoc at a
//! call return, because the callee may have written it through a `&mut`. For
//! a callee WITH a contract that is a loss of information the contract
//! already closes: when the argument is a reborrow `&mut L` (or `&mut *L`)
//! created for this call and the call's result can carry no borrow, the
//! reborrow expires when the callee returns, so the callee's `^p` IS the
//! value of `L` (of `*L`) right after the call — the havoc symbol — and its
//! `*p` is the value passed in. Instantiating the callee's `ensures` under
//! that mapping and assuming them on the path is a literal consequence of the
//! contract plus the expiry of the reborrow at the return: no allowlist, no
//! callee name, no new trust. Without it, `inc_max_3` (three `&mut &mut u32`
//! swaps with `#[ensures(^mma == *mmb && ^mmb == *mma)]`) owes
//! `*ma + 2` in range with `*ma` an unconstrained havoc, and is refused.
//!
//! What is deliberately NOT assumed: a clause mentioning `result`, `old(..)`,
//! a bare `p` (the reference itself), or any parameter this mapping does not
//! resolve — each is dropped, never approximated. A local that the walk did
//! not actually re-bind gets no handback either (its binding is already the
//! pre-call value, and `^p == *p + 1` over one symbol would be a
//! contradiction, not a fact).

use std::collections::{HashMap, HashSet};

use rustc_middle::{
    mir::{
        AggregateKind, Body, BorrowKind, InlineAsmOperand, Local, Operand, Place, ProjectionElem,
        Rvalue, StatementKind, TerminatorKind,
    },
    ty::{Mutability, TyCtxt, TyKind},
};
use rustc_span::Spanned;
use trust_wp_core::formula::{elaborate::Signature, ExprSort, PureExpr};

use super::super::spec_apply::{clause_read_as_written, TranslatedArg};

/// One call argument that is a fresh mutable reborrow of caller local `local`.
struct ReborrowArg {
    /// The callee's parameter bound to it.
    param: String,
    /// `true` for `&mut *L` (the pointee is lent), `false` for `&mut L`.
    through_deref: bool,
    /// `L`'s binding before the call.
    pre: PureExpr,
    /// `L`'s fresh binding after the call.
    post: PureExpr,
}

/// Push onto `path_conditions` every callee `ensures` clause that the
/// reborrow handback fully resolves. `pre_exprs` is the walk state at the
/// call, `post_exprs` the state after the address-taken re-binding.
#[allow(clippy::too_many_arguments)]
pub(super) fn assume_reborrow_handbacks<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    destination: &Place<'tcx>,
    ensures: &[String],
    callee: &Signature,
    param_names: Option<&[String]>,
    translated_args: &[TranslatedArg],
    pre_exprs: &HashMap<Local, PureExpr>,
    post_exprs: &HashMap<Local, PureExpr>,
    path_conditions: &mut Vec<PureExpr>,
) {
    if ensures.is_empty() || call_result_may_carry_borrow(tcx, body, destination) {
        return;
    }
    let Some(param_names) = param_names else {
        return;
    };
    let mut reborrows: HashMap<String, ReborrowArg> = HashMap::new();
    for (idx, arg) in args.iter().enumerate() {
        let Some(param) = param_names.get(idx) else {
            continue;
        };
        let Some((local, through_deref)) = fresh_mut_reborrow_source(body, &arg.node) else {
            continue;
        };
        let (Some(pre), Some(post)) = (pre_exprs.get(&local), post_exprs.get(&local)) else {
            continue;
        };
        // Only a local the walk re-bound at this call has a post-state to hand
        // back; an unchanged binding would make `^p` and `*p` one symbol.
        if pre == post || !matches!(post, PureExpr::Var(..)) {
            continue;
        }
        reborrows.insert(
            param.clone(),
            ReborrowArg {
                param: param.clone(),
                through_deref,
                pre: pre.clone(),
                post: post.clone(),
            },
        );
    }
    if reborrows.is_empty() {
        return;
    }
    // Every other parameter with an exactly translated argument is a plain
    // value here; the reborrowed ones are resolved structurally below.
    let by_value: HashMap<String, PureExpr> = param_names
        .iter()
        .enumerate()
        .filter(|(_, name)| !reborrows.contains_key(*name))
        .filter_map(|(idx, name)| {
            let arg = translated_args.get(idx)?;
            (!arg.is_fallback).then(|| (name.clone(), arg.expr.clone()))
        })
        .collect();
    let param_set: HashSet<&String> = param_names.iter().collect();

    for clause in ensures {
        let Some(parsed) = clause_read_as_written(clause, callee) else {
            continue;
        };
        let mut mentions_old = false;
        parsed.for_each_recursive(|node| {
            if matches!(node, PureExpr::Old(_)) {
                mentions_old = true;
            }
        });
        if mentions_old {
            continue;
        }
        let resolved = parsed
            .rewrite_bottom_up(|node| resolve_reborrow_projection(node, &reborrows))
            .substitute(&by_value)
            .rewrite_bottom_up(weaken_mut_ref_equality_to_currents);
        let free = resolved.free_vars();
        if free.contains("result") || free.iter().any(|v| param_set.contains(v)) {
            continue;
        }
        if !path_conditions.contains(&resolved) {
            path_conditions.push(resolved);
        }
    }
}

/// `^p` -> the post-call binding, `*p` -> the pre-call binding, for a
/// reborrowed parameter `p`; anything else is returned unchanged.
fn resolve_reborrow_projection(
    node: PureExpr,
    reborrows: &HashMap<String, ReborrowArg>,
) -> PureExpr {
    let (is_final, inner) = match &node {
        PureExpr::Final(inner) => (true, inner),
        PureExpr::Deref(inner) => (false, inner),
        _ => return node,
    };
    let PureExpr::Var(name, _) = inner.as_ref() else {
        return node;
    };
    let Some(reborrow) = reborrows.get(name) else {
        return node;
    };
    debug_assert_eq!(&reborrow.param, name);
    let state = if is_final {
        reborrow.post.clone()
    } else {
        reborrow.pre.clone()
    };
    if reborrow.through_deref {
        PureExpr::Deref(std::sync::Arc::new(state))
    } else {
        state
    }
}

/// `a == b` over two `&mut` reference values (swap's `^mma == *mmb`) becomes
/// `*a == *b`: the walk's obligations read a re-bound reference only through
/// `Deref`, which the encoder binds to its own current-value symbol, so the
/// reference-level equality would not reach them. Equal references have equal
/// currents, so this is a weaker consequence, never a new fact.
fn weaken_mut_ref_equality_to_currents(node: PureExpr) -> PureExpr {
    let PureExpr::BinOp(lhs, trust_wp_core::formula::BinOp::Eq, rhs) = &node else {
        return node;
    };
    let is_mut_ref_var = |e: &PureExpr| matches!(e, PureExpr::Var(_, Some(ExprSort::MutRef(_))));
    if !(is_mut_ref_var(lhs) && is_mut_ref_var(rhs)) {
        return node;
    }
    PureExpr::BinOp(
        std::sync::Arc::new(PureExpr::Deref(lhs.clone())),
        trust_wp_core::formula::BinOp::Eq,
        std::sync::Arc::new(PureExpr::Deref(rhs.clone())),
    )
}

/// When `operand` moves or copies a temporary whose single definition is a
/// mutable reborrow, the reborrowed local and whether the reborrow goes
/// through a `&mut` deref (`&mut *L` with `L: &mut T`) rather than taking `L`
/// itself (`&mut L`). A chain of reborrow temporaries is followed:
/// `&mut *(&mut L)` is `&mut L`, and `&mut *(&mut *L)` is `&mut *L`, which is
/// how MIR spells the argument of `swap(&mut ma, ..)` (`_18 = &mut _1;
/// _19 = &mut (*_18); swap(move _19, ..)`).
fn fresh_mut_reborrow_source<'tcx>(
    body: &Body<'tcx>,
    operand: &Operand<'tcx>,
) -> Option<(Local, bool)> {
    let (Operand::Move(place) | Operand::Copy(place)) = operand else {
        return None;
    };
    if !place.projection.is_empty() || place.local.as_usize() <= body.arg_count {
        return None;
    }
    let borrowed = single_mut_borrow_definition(body, place.local)?;
    reborrow_source(body, borrowed, 0)
}

/// The local a mutable borrow of `place` lends, and whether it lends the
/// local's pointee (`&mut *L`) rather than the local (`&mut L`).
fn reborrow_source<'tcx>(
    body: &Body<'tcx>,
    place: &Place<'tcx>,
    depth: usize,
) -> Option<(Local, bool)> {
    const MAX_REBORROW_CHAIN: usize = 8;
    if depth > MAX_REBORROW_CHAIN {
        return None;
    }
    match place.projection.as_slice() {
        [] => Some((place.local, false)),
        [ProjectionElem::Deref]
            if matches!(
                body.local_decls[place.local].ty.kind(),
                TyKind::Ref(_, _, Mutability::Mut)
            ) =>
        {
            // `&mut *S` where `S` itself is a single mutable borrow `&mut Q`
            // that nothing can reassign behind this body's back lends exactly
            // what `S` lends. Otherwise the reborrow lends `S`'s pointee,
            // whatever `S` holds at the call (`(S, true)`), which stays
            // correct when `S` was redirected through a borrow of it.
            match single_mut_borrow_definition(body, place.local) {
                Some(inner) => reborrow_source(body, inner, depth + 1),
                None => Some((place.local, true)),
            }
        }
        _ => None,
    }
}

/// The place `local` mutably borrows, when its ONLY write in the body is a
/// whole-local `local = &mut <place>` AND `local` never escapes by reference.
///
/// Both halves are needed before `local`'s VALUE at the call may be read off
/// its definition. A local that is itself borrowed (`tt = &mut t`), pointed
/// to (`&raw mut t`) or captured by a closure can be reassigned through that
/// borrow (`*tt = &mut y`) without any write naming `t` in this body, so its
/// one visible definition says nothing about where it points at the call —
/// `zero(t)` would zero `y` while the handback credited `x`. Such a local is
/// refused, never tracked: the caller falls back to speaking about `*t` (the
/// pointee of whatever `t` holds), which is correct under redirection. A
/// borrow of `t`'s POINTEE (`&mut *t`, `&(*t).f`) is not an escape of `t`: it
/// cannot reassign `t`, and it is how MIR spells the reborrow this module is
/// looking for.
fn single_mut_borrow_definition<'a, 'tcx>(
    body: &'a Body<'tcx>,
    local: Local,
) -> Option<&'a Place<'tcx>> {
    let mut source = None;
    let mut writes = 0usize;
    for bb_data in body.basic_blocks.iter() {
        for stmt in &bb_data.statements {
            match &stmt.kind {
                StatementKind::Assign((dst, rvalue)) => {
                    if dst.local == local {
                        writes += 1;
                        if dst.projection.is_empty() {
                            if let Rvalue::Ref(_, BorrowKind::Mut { .. }, src) = rvalue {
                                source = Some(src);
                            }
                        }
                    }
                    if rvalue_lets_local_escape(rvalue, local) {
                        return None;
                    }
                }
                StatementKind::SetDiscriminant { place, .. } if place.local == local => {
                    writes += 1;
                }
                _ => {}
            }
        }
        match &bb_data.terminator().kind {
            TerminatorKind::Call { destination, .. } if destination.local == local => {
                writes += 1;
            }
            TerminatorKind::Yield { resume_arg, .. } if resume_arg.local == local => {
                writes += 1;
            }
            // Inline assembly writes its outputs by means this walk cannot
            // read; a local it names is not a fresh reborrow source.
            TerminatorKind::InlineAsm { operands, .. }
                if operands.iter().any(|op| match op {
                    InlineAsmOperand::Out { place, .. } => place.is_some_and(|p| p.local == local),
                    InlineAsmOperand::InOut { out_place, .. } => {
                        out_place.is_some_and(|p| p.local == local)
                    }
                    _ => false,
                }) =>
            {
                return None;
            }
            _ => {}
        }
    }
    (writes == 1).then_some(source).flatten()
}

/// Whether evaluating `rvalue` lets `local` escape by reference — any borrow
/// or raw pointer of `local` itself (or of a field/index of it, not of its
/// pointee), of any kind, or a closure/coroutine capturing it by value. A
/// borrow through `Deref` first (`&mut *local`) lends the pointee only.
pub(super) fn rvalue_lets_local_escape<'tcx>(rvalue: &Rvalue<'tcx>, local: Local) -> bool {
    let names_local_itself = |place: &Place<'tcx>| {
        place.local == local && !matches!(place.projection.first(), Some(ProjectionElem::Deref))
    };
    match rvalue {
        Rvalue::Ref(_, _, place) | Rvalue::RawPtr(_, place) => names_local_itself(place),
        Rvalue::Aggregate(kind, operands)
            if matches!(
                **kind,
                AggregateKind::Closure(..)
                    | AggregateKind::Coroutine(..)
                    | AggregateKind::CoroutineClosure(..)
            ) =>
        {
            operands.iter().any(|op| match op {
                Operand::Move(place) | Operand::Copy(place) => place.local == local,
                _ => false,
            })
        }
        _ => false,
    }
}

/// Whether the call's result type could hold a borrow (so a reborrowed
/// argument might be lent into it and outlive the call): the predicate the
/// callee's own lane frees a lent parameter's final value by
/// (`mut_borrow::may_carry_borrow`), which also counts a type whose fields
/// reach a raw pointer (`Rc<T>`, `Vec<T>`) and a shared reference to a
/// referent with interior mutability.
fn call_result_may_carry_borrow<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    destination: &Place<'tcx>,
) -> bool {
    let ty = destination.ty(&body.local_decls, tcx).ty;
    crate::mir_analysis::mut_borrow::may_carry_borrow(tcx, body.typing_env(tcx), ty, 0)
}
