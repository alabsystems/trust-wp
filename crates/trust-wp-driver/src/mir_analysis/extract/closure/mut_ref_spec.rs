// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::{HashMap, HashSet};

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{BasicBlock, Body, Local, Operand},
    ty::TyCtxt,
};
use rustc_span::Spanned;
use trust_wp_core::formula::PureExpr;
use trust_wp_driver::StdSpec;

use super::mut_ref_local_for_operand;
use crate::mir_analysis::{
    call_resolve::{arg_names_for_def_id, extract_closure_def_id_from_fn_call},
    effects::fail_closed_marker,
    extract::call_resolve_shared::{resolve_call, ResolvedCallKind},
    translate::ExprLookup,
};

pub(in crate::mir_analysis::extract) fn spec_mutates_closure_state(spec: &StdSpec) -> bool {
    spec.ensures.iter().any(|ens| {
        ens.contains("postcondition_mut(")
            || ens.contains("postcondition_once(")
            || ens.contains(".postcondition_mut(")
            || ens.contains(".postcondition_once(")
    })
}

fn param_aliases_for_arg_index(param_names: Option<&[String]>, arg_index: usize) -> Vec<String> {
    let mut aliases = vec![format!("arg{arg_index}")];
    if arg_index == 0 {
        aliases.push("self".to_string());
    }
    if let Some(name) = param_names.and_then(|names| names.get(arg_index)) {
        if !aliases.iter().any(|alias| alias == name) {
            aliases.push(name.clone());
        }
    }
    aliases
}

fn expr_root_var_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Deref(inner) | PureExpr::Final(inner) | PureExpr::View(inner) => {
            expr_root_var_name(inner)
        }
        _ => None,
    }
}

fn deref_root_var_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Deref(inner) => expr_root_var_name(inner),
        PureExpr::Final(inner) | PureExpr::View(inner) => deref_root_var_name(inner),
        _ => None,
    }
}

fn collect_mutating_ref_aliases(expr: &PureExpr, vars: &mut HashSet<String>) {
    expr.for_each_recursive(|node| match node {
        PureExpr::Final(inner) => {
            if let Some(name) = expr_root_var_name(inner) {
                vars.insert(name.to_string());
            }
        }
        PureExpr::Old(inner) => {
            if let Some(name) = deref_root_var_name(inner) {
                vars.insert(name.to_string());
            }
        }
        _ => {}
    });
}

pub(in crate::mir_analysis::extract) fn spec_mentions_post_state_for_aliases(
    spec: &StdSpec,
    aliases: &[String],
) -> bool {
    if aliases.is_empty() {
        return false;
    }

    if spec_mutates_closure_state(spec)
        && aliases
            .iter()
            .any(|alias| alias == "self" || alias == "arg0")
    {
        return true;
    }

    let mut parse_failed = false;
    let mut mutating_aliases = HashSet::new();
    for ensures in &spec.ensures {
        if let Ok(expr) = trust_wp_core::contract_parser::parse_contract(ensures) {
            collect_mutating_ref_aliases(&expr, &mut mutating_aliases);
        } else {
            parse_failed = true;
            break;
        }
    }

    if parse_failed {
        return true;
    }

    aliases
        .iter()
        .any(|alias| mutating_aliases.contains(alias.as_str()))
}

pub(in crate::mir_analysis::extract) fn all_mut_ref_arg_positions(
    body: &Body<'_>,
    args: &[Spanned<Operand<'_>>],
) -> Vec<usize> {
    args.iter()
        .enumerate()
        .filter_map(|(idx, arg)| mut_ref_local_for_operand(body, &arg.node).map(|_| idx))
        .collect()
}

/// Positions of arguments passed as a SHARED reference `&T` to a `!Freeze`
/// type `T` (rustc's `Freeze` query: `Cell`, `RefCell`, `UnsafeCell`,
/// atomics, and anything containing an `UnsafeCell`).
///
/// A shared reference to interior-mutable memory is a write capability: the
/// callee may change every place reachable from it (`Cell::set` through
/// `&Cell`). Such an argument is treated exactly like a `&mut` argument, so
/// values read through it after the call are fresh post-call state, never the
/// pre-call value. SOUND: advancing the state only removes the identification
/// of the pre- and post-call contents.
///
/// Generic type parameters are decided by their STRUCTURE, not by rustc's
/// answer for an unbounded parameter (`T: Freeze` is never provable, so every
/// `&T` would be a write, and every `&self` trait call on a generic receiver
/// would forget the receiver). This matches Creusot, which models `&T` as the
/// value of `T`: a generic body only observes a `T` through its bounds'
/// logic functions, which read a value, and no logic function observes the
/// contents of an unknown `T`'s interior-mutable memory. Parameters are
/// replaced by `()` and the resulting type is queried; a type that still
/// cannot be decided (an alias that does not normalize, a trait object)
/// is treated as interior-mutable (fail closed).
pub(in crate::mir_analysis::extract) fn interior_mutable_ref_arg_positions<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    body: &Body<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
) -> Vec<usize> {
    let typing_env = body.typing_env(tcx);
    args.iter()
        .enumerate()
        .filter_map(|(idx, arg)| {
            let ty = arg.node.ty(&body.local_decls, tcx);
            (top_level_interior_mutable_ref(tcx, typing_env, ty)
                || ty_carries_interior_write_capability(
                    tcx,
                    typing_env,
                    ty,
                    &mut HashSet::new(),
                    0,
                ))
            .then_some(idx)
        })
        .collect()
}

/// `ty` is `&T` with `T` interior-mutable (the direct shape the receiver-state
/// propagation advances by the reference's own variable).
fn top_level_interior_mutable_ref<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    typing_env: rustc_middle::ty::TypingEnv<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> bool {
    matches!(
        ty.kind(),
        rustc_middle::ty::TyKind::Ref(_, pointee, rustc_middle::ty::Mutability::Not)
            if pointee_may_be_interior_mutable(tcx, typing_env, *pointee)
    )
}

/// Positions whose argument is NOT a direct `&T` to interior-mutable memory
/// but whose TYPE still carries a write capability to such memory: a nested
/// reference (`&&Cell`), a struct, enum or tuple holding one (`S { c: &Cell }`,
/// `(&Cell, u8)`), a closure whose upvars capture one, a std container or
/// pointer over one (`Rc<RefCell<_>>`, `Option<&Cell>`), or an opaque value
/// (`Box<dyn Fn()>`, whose captures are unknown). See
/// [`ty_carries_interior_write_capability`]. The receiver-state propagation
/// only advances a reference's own variable, so the call sites havoc every
/// variable root of such an argument ([`interior_capability_roots`],
/// [`havoc_interior_capability_roots`]).
pub(in crate::mir_analysis::extract) fn nested_interior_capability_arg_positions<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    body: &Body<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
) -> Vec<usize> {
    let typing_env = body.typing_env(tcx);
    args.iter()
        .enumerate()
        .filter_map(|(idx, arg)| {
            let ty = arg.node.ty(&body.local_decls, tcx);
            (!top_level_interior_mutable_ref(tcx, typing_env, ty)
                && ty_carries_interior_write_capability(
                    tcx,
                    typing_env,
                    ty,
                    &mut HashSet::new(),
                    0,
                ))
            .then_some(idx)
        })
        .collect()
}

/// Whether a value of type `ty` gives its holder a way to write
/// interior-mutable memory that is NOT exclusively owned by that value:
/// memory reachable through a shared reference, a raw pointer, or a std
/// type's type argument (`Rc`, `Arc`, `Box`, `Vec`, `Option`, ...).
///
/// The walk is structural: references through their pointee, user ADTs
/// through their fields (instantiated), std/core/alloc ADTs through their
/// type arguments only (never their private fields), tuples, arrays and
/// slices through their elements, closures through their upvars. Trait
/// objects and coroutines are opaque and count as a capability (fail
/// closed). Generic type parameters (and aliases built from them) follow the
/// same structural rule as [`pointee_may_be_interior_mutable`]: they are not
/// a capability by themselves. Permission-modelled cells never are.
/// Over-reporting is SOUND: it only forgets pre-call state.
fn ty_carries_interior_write_capability<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    typing_env: rustc_middle::ty::TypingEnv<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    visited: &mut HashSet<rustc_middle::ty::Ty<'tcx>>,
    depth: usize,
) -> bool {
    use rustc_middle::ty::{TyKind, TypeVisitableExt};
    if depth > 32 {
        return true;
    }
    if !visited.insert(ty) {
        return false;
    }
    let recurse = |t: rustc_middle::ty::Ty<'tcx>, visited: &mut HashSet<_>| {
        ty_carries_interior_write_capability(tcx, typing_env, t, visited, depth + 1)
    };
    match ty.kind() {
        TyKind::Ref(_, pointee, rustc_middle::ty::Mutability::Not) | TyKind::RawPtr(pointee, _) => {
            pointee_may_be_interior_mutable(tcx, typing_env, *pointee) || recurse(*pointee, visited)
        }
        // Same rule as the shared/raw arm above. `&mut Cell<u8>` is itself
        // `Freeze`, so the whole-type `pointee_may_be_interior_mutable` test in
        // `ty_exposes_interior_mutability` does not see the cell either, and
        // `recurse(Cell<u8>)` reaches the core/alloc/std `Adt` arm, which
        // inspects only the type arguments (`[u8]`). Without the direct test a
        // cell reachable through a `&mut` hop is invisible to both gates.
        TyKind::Ref(_, pointee, rustc_middle::ty::Mutability::Mut) => {
            pointee_may_be_interior_mutable(tcx, typing_env, *pointee) || recurse(*pointee, visited)
        }
        TyKind::Adt(adt, adt_args) => {
            if is_permission_modelled_cell(tcx, adt.did()) {
                return false;
            }
            if matches!(
                tcx.crate_name(adt.did().krate).as_str(),
                "core" | "alloc" | "std"
            ) {
                adt_args.types().any(|arg| {
                    pointee_may_be_interior_mutable(tcx, typing_env, arg) || recurse(arg, visited)
                })
            } else {
                adt.all_fields()
                    .any(|field| recurse(field.ty(tcx, *adt_args).skip_norm_wip(), visited))
            }
        }
        TyKind::Tuple(tys) => tys.iter().any(|t| recurse(t, visited)),
        TyKind::Array(elem, _) | TyKind::Slice(elem) => recurse(*elem, visited),
        TyKind::Closure(_, closure_args) => closure_args
            .as_closure()
            .upvar_tys()
            .iter()
            .any(|t| recurse(t, visited)),
        TyKind::Dynamic(..)
        | TyKind::Coroutine(..)
        | TyKind::CoroutineClosure(..)
        | TyKind::CoroutineWitness(..)
        | TyKind::Infer(..)
        | TyKind::Error(..)
        | TyKind::Bound(..)
        | TyKind::Placeholder(..) => true,
        TyKind::Alias(..) => !ty.has_param(),
        _ => false,
    }
}

/// Whether a value of type `ty` exposes interior-mutable memory that a generic
/// body would treat as an unchanging value: `ty` is itself interior-mutable
/// (a non-permission cell once generic parameters are replaced by `()`), or it
/// carries a write capability to such memory
/// ([`ty_carries_interior_write_capability`]).
///
/// A generic body models a value of a type parameter `T` (and `&T`) as its
/// logical value, which calls through shared access never change (the
/// structural rule of [`pointee_may_be_interior_mutable`]). Instantiating `T`
/// at a type for which this returns `true` breaks that model, so the
/// instantiation sites fail closed.
pub(crate) fn ty_exposes_interior_mutability<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    typing_env: rustc_middle::ty::TypingEnv<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> bool {
    use rustc_middle::ty::TypeVisitableExt;
    (!ty.has_param() && pointee_may_be_interior_mutable(tcx, typing_env, ty))
        || ty_carries_interior_write_capability(tcx, typing_env, ty, &mut HashSet::new(), 0)
}

/// The variable roots of the PRE-call translation of every argument at
/// `positions`, or `None` when one of them does not translate.
pub(in crate::mir_analysis::extract) fn interior_capability_roots<'tcx>(
    local_exprs: &HashMap<Local, PureExpr>,
    args: &[Spanned<Operand<'tcx>>],
    positions: &[usize],
) -> Option<Vec<String>> {
    let mut roots = Vec::new();
    for arg in positions.iter().filter_map(|idx| args.get(*idx)) {
        let expr = crate::mir_analysis::translate::translate_operand(&arg.node, local_exprs)?;
        expr.for_each_recursive(|node| {
            if let PureExpr::Var(name, _) = node {
                if !roots.contains(name) {
                    roots.push(name.clone());
                }
            }
        });
    }
    Some(roots)
}

static INTERIOR_CAPABILITY_HAVOC_SERIAL: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

/// Havoc every variable root of a call argument that carries an interior
/// write capability (see [`nested_interior_capability_arg_positions`]): every
/// local expression mentioning a root is rebuilt over a fresh, unconstrained
/// symbol, so nothing read through the capability before the call is
/// identified with anything read after it. `roots == None` (an argument did
/// not translate, so its roots are unknown) fails closed with a `false`
/// obligation. SOUND: a fresh symbol only forgets information.
pub(in crate::mir_analysis::extract) fn havoc_interior_capability_roots(
    local_exprs: &mut HashMap<Local, PureExpr>,
    roots: Option<Vec<String>>,
    obligations: &mut Vec<PureExpr>,
) {
    let Some(roots) = roots else {
        obligations.push(fail_closed_marker("mut-ref-spec-no-roots"));
        return;
    };
    for root in roots {
        let serial =
            INTERIOR_CAPABILITY_HAVOC_SERIAL.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let fresh = format!("$havoc_icap_{serial}");
        for expr in local_exprs.values_mut() {
            let mut mentions = false;
            expr.for_each_recursive(|node| {
                mentions |= matches!(node, PureExpr::Var(name, _) if *name == root);
            });
            if mentions {
                *expr = expr.clone().rewrite_bottom_up(|node| match node {
                    PureExpr::Var(name, sort) if name == root => PureExpr::Var(fresh.clone(), sort),
                    other => other,
                });
            }
        }
    }
}

/// THE interior-mutability decision about a call's RESULT, shared by every
/// extraction lane (primary return-expression walk, proof-assert substitution
/// walk).
///
/// A call that receives a shared reference to interior-mutable memory
/// (`Cell::get`, `RefCell::borrow`, an atomic load, ...) returns a value
/// observed at THIS program point. Its destination must therefore be bound to
/// the call's fresh result symbol — whose relation to the pre-call state the
/// primary lane states as an ASSUMPTION — and never to the substituted
/// postcondition expression, which is written in terms of the pre-call
/// receiver and which a later write through the same shared reference
/// silently advances. Two reads around one write would otherwise be one term.
///
/// SOUND in both directions: this only replaces a derived expression by an
/// opaque symbol, i.e. removes an identification. Both lanes mint that symbol
/// with the same `call_result_symbol`, so a fact the primary lane states about
/// it is still available to a goal the substitution lane builds. (s44, s63)
pub(in crate::mir_analysis::extract) fn call_result_for_interior_mutable_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    result_expr: PureExpr,
    result_var: &PureExpr,
) -> PureExpr {
    if interior_mutable_ref_arg_positions(tcx, body, args).is_empty() {
        result_expr
    } else {
        result_var.clone()
    }
}

/// THE interior-mutability decision about a call's ARGUMENTS, shared by every
/// extraction lane: a shared reference to interior-mutable memory is a write
/// capability, so its position joins the `&mut` positions the spec lane
/// computed. Advancing an argument only removes the identification of its
/// pre- and post-call state. (s44, s63)
pub(in crate::mir_analysis::extract) fn union_interior_mutable_write_positions<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    positions: &mut Vec<usize>,
) {
    union_arg_positions(
        positions,
        interior_mutable_ref_arg_positions(tcx, body, args),
    );
}

/// `true` unless `pointee` is known `Freeze` once its generic type parameters
/// and its permission-modelled cells are replaced by `()` (see
/// [`interior_mutable_ref_arg_positions`]).
///
/// Permission-modelled cells (`PermCell`, `PredCell`, `NonAtomicInvariant`,
/// `AtomicInvariant` from `trust_wp_std` / `creusot_std`) keep their contents
/// out of their logical value: a `PermCell`'s value is its identity (the
/// contents live in a ghost `Perm`, written only through `&mut Perm`), a
/// `PredCell`'s value is its fixed predicate (`get` ensures only
/// `self@[result]`), and an invariant's namespace and public value are fixed
/// at construction. A write through `&` to such a cell changes nothing its
/// logical value exposes, so it is not a write for this rule.
fn pointee_may_be_interior_mutable<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    typing_env: rustc_middle::ty::TypingEnv<'tcx>,
    pointee: rustc_middle::ty::Ty<'tcx>,
) -> bool {
    use rustc_middle::ty::TypeFoldable;
    let pointee = region_free_query_ty(tcx, pointee);
    if pointee.is_freeze(tcx, typing_env) {
        return false;
    }
    let unit = tcx.types.unit;
    let erased = pointee.fold_with(&mut rustc_middle::ty::BottomUpFolder {
        tcx,
        ty_op: |t: rustc_middle::ty::Ty<'tcx>| match t.kind() {
            rustc_middle::ty::TyKind::Param(_) => unit,
            rustc_middle::ty::TyKind::Adt(adt, _)
                if is_permission_modelled_cell(tcx, adt.did()) =>
            {
                unit
            }
            _ => t,
        },
        lt_op: |r| r,
        ct_op: |c| c,
    });
    let Ok(normalized) = tcx.try_normalize_erasing_regions(
        typing_env,
        rustc_middle::ty::set_aliases_to_non_rigid(tcx, erased),
    ) else {
        return true;
    };
    {
        use rustc_middle::ty::TypeVisitableExt;
        if normalized.has_aliases() {
            return true;
        }
    }
    !normalized.is_freeze(tcx, typing_env)
}

/// `ty` with every region erased, for use as a trait-query key.
///
/// Operand types of the borrow-checked body carry inference regions (`'?N`),
/// and a query key containing one cannot be hashed (rustc panics with
/// "region variables should not be hashed"). Erasing them is EXACT for the
/// queries asked here: `Freeze` is an auto trait, and auto-trait impls cannot
/// be specialized on lifetimes (rustc requires them to be generic over every
/// lifetime), so `T: Freeze` holds for one choice of regions iff it holds for
/// all. rustc's own callers (`needs_drop`, `try_normalize_erasing_regions`,
/// `Instance::try_resolve`) erase the same way before querying.
pub(in crate::mir_analysis::extract) fn region_free_query_ty<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> rustc_middle::ty::Ty<'tcx> {
    tcx.erase_and_anonymize_regions(ty)
}

fn is_permission_modelled_cell(tcx: rustc_middle::ty::TyCtxt<'_>, did: DefId) -> bool {
    let krate = tcx.crate_name(did.krate);
    if !matches!(krate.as_str(), "trust_wp_std" | "creusot_std") {
        return false;
    }
    matches!(
        tcx.item_name(did).as_str(),
        "PermCell" | "PredCell" | "NonAtomicInvariant" | "AtomicInvariant"
    )
}

/// Union `extra` positions into `positions`, keeping order and uniqueness.
pub(in crate::mir_analysis::extract) fn union_arg_positions(
    positions: &mut Vec<usize>,
    extra: Vec<usize>,
) {
    for idx in extra {
        if !positions.contains(&idx) {
            positions.push(idx);
        }
    }
}

/// `Some(depth)` when `expr` is `name` under `depth` `Deref` layers.
fn deref_depth_of_var(expr: &PureExpr, name: &str) -> Option<usize> {
    match expr {
        PureExpr::Var(var, _) if var == name => Some(0),
        PureExpr::Deref(inner) => deref_depth_of_var(inner, name).map(|d| d + 1),
        _ => None,
    }
}

/// The names a std spec clause may use for argument `idx`, beyond the callee's
/// own parameter name: the positional `argN`/`self` aliases and the symbolic
/// `value`/`default`/`arg`/`rhs` aliases that
/// `spec_apply::insert_std_symbolic_substitutions` binds to the first non-self
/// argument (position 1 for a method call, position 0 otherwise).
pub(in crate::mir_analysis::extract) fn spec_clause_aliases_for_arg_index(
    param_names: Option<&[String]>,
    arg_count: usize,
    idx: usize,
) -> Vec<String> {
    let mut aliases = param_aliases_for_arg_index(param_names, idx);
    let value_idx = usize::from(arg_count > 1);
    if idx == value_idx {
        for name in ["value", "default", "arg", "rhs"] {
            aliases.push(name.to_string());
        }
    }
    aliases
}

/// Does the contract hand this `&mut` argument back as (part of) the result —
/// `result == p` or `*result == p`?
///
/// This is only ONE half of the borrow-forwarding test; on its own it is NOT
/// a reason to skip the advance, and it must never be used without
/// [`callee_forwards_mut_borrow`]. An earlier revision of this file justified
/// the exception by "a callee that wrote through `p` would contradict its own
/// contract"; that is a claim trust-wp NEVER CHECKS —
/// `#[ensures(result == p)] fn f(p: &mut u32) -> &mut u32 { *p = 9; p }`
/// verifies today although `*result` is 9 and the entry pointee is not. So the
/// clause shape says only WHICH argument a borrow-forwarding callee forwards;
/// the licence to skip the advance comes from the callee itself.
///
/// Only the REFERENCE-level shapes count. A pointee-level equality
/// `*result == *p` (`Box::deref_mut`'s first clause) pins the entry value of
/// the pointee and says nothing about `^p`, so it does NOT suppress the
/// advance. (s48)
pub(in crate::mir_analysis::extract) fn spec_result_carries_arg_reference(
    spec: &StdSpec,
    aliases: &[String],
) -> bool {
    if aliases.is_empty() {
        return false;
    }
    spec.ensures.iter().any(|ensures| {
        let Ok(expr) = trust_wp_core::contract_parser::parse_contract(ensures) else {
            // An unparsed clause claims nothing: the argument stays advanced.
            return false;
        };
        let PureExpr::BinOp(lhs, trust_wp_core::formula::BinOp::Eq, rhs) = &expr else {
            return false;
        };
        [(lhs, rhs), (rhs, lhs)]
            .iter()
            .any(|(result_side, arg_side)| {
                let Some(result_depth) = deref_depth_of_var(result_side, "result") else {
                    return false;
                };
                if result_depth > 1 {
                    return false;
                }
                aliases
                    .iter()
                    .any(|alias| deref_depth_of_var(arg_side, alias) == Some(0))
            })
    })
}

/// Positions of the `&mut` arguments whose pointee a call to a spec'd callee
/// may change.
///
/// Every `&mut` argument, unless `callee_forwards_borrows` says the callee is
/// one of the fixed library items from whose RESULT no live `&mut` reborrow of
/// the argument can be reached ([`callee_forwards_mut_borrow`]) — and then only
/// for the argument that item's contract names as the one it forwards
/// ([`spec_result_carries_arg_reference`]). Both halves are required: the
/// contract shape alone is not evidence, because trust-wp never checks that a
/// body honours it. Note that "the callee moved the argument into its result"
/// is NOT that criterion and never was a safe reading of it: a `&mut` moved
/// into a container is handed back by `*b`, `**b`, `get_mut` or `into_inner`
/// (s48 v4).
///
/// Creusot semantics (soundness): a callee's contract is the only authority on
/// `^p`. A contract that says nothing about `^p` (no `ensures` at all, or only
/// `ensures(true)`, or clauses over the entry value `*p`) leaves the final
/// value UNCONSTRAINED; it never frames `^p == *p`. This used to advance only
/// the arguments whose `ensures` mentioned a post-state, so
/// `fn push_one(v: &mut Vec<i32>) { v.push(1) }` with no contract framed its
/// argument unchanged and `let n = v.len(); push_one(&mut v);
/// proof_assert!(n@ == v@.len())` verified. Advancing an argument only removes
/// the identification of its pre- and post-call state, so this can cost
/// completeness but never soundness; a contract that does state `^p` still
/// binds it.
pub(in crate::mir_analysis::extract) fn spec_mutating_ref_arg_positions<'tcx>(
    body: &Body<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    spec: &StdSpec,
    param_names: Option<&[String]>,
    callee_forwards_borrows: bool,
) -> Vec<usize> {
    let positions = all_mut_ref_arg_positions(body, args);
    if !callee_forwards_borrows {
        return positions;
    }
    positions
        .into_iter()
        .filter(|idx| {
            let aliases = spec_clause_aliases_for_arg_index(param_names, args.len(), *idx);
            !spec_result_carries_arg_reference(spec, &aliases)
        })
        .collect()
}

/// Library items that hand a `&mut` argument onward instead of writing
/// through it. Matched on the FULL def path with generic arguments stripped,
/// never on a bare item name: `deref_mut`, `borrow_mut`, `into_inner` and
/// `new` are all names many other std items carry.
///
/// THE SOUNDNESS CRITERION FOR EVERY LIST BELOW — corrected in s48 v4 after a
/// probe refuted the v3 wording (see [`callee_forwards_mut_borrow`] for the
/// argument, and `docs/soundness.md` K1 for the ledger):
///
/// > An item may suppress the advance of a `&mut` argument ONLY IF no live
/// > `&mut` reborrow of that argument is REACHABLE FROM THE CALL'S RESULT —
/// > by any projection, deref, unwrapping method, field read, iterator item
/// > or later call the caller can apply to the result.
///
/// "The argument is MOVED into the result" does NOT satisfy the criterion,
/// and v3 shipped that sentence as if it did. Moving a `&mut` into a
/// container does not end the reborrow; the container hands it straight back,
/// and the caller's write through what it got back is not propagated to the
/// argument. Measured at the v3 head (`~/wpcamp/s48/probes4/`, logs
/// `*.rs.base.log`), each of these accepted a FALSE `proof_assert` at exit 0:
///
/// - `let b = Box::new(&mut x); let r: &mut i32 = *b; *r = 7;`
///   then `proof_assert!(x == 5i32)` — `p1_box_deref_out.rs`.
/// - `let b = Box::new(&mut v); (**b).push(1);`
///   then `proof_assert!(v@.len() == n@)` — `p2_box_vec_push.rs`.
/// - `ghost! { let h = Ghost::new(&mut x); *h.into_inner() = 7; }`
///   then `proof_assert!(x == 5i32)` — `p6b_ghost_new_program_ref.rs`.
///
/// `Rc::new` / `Arc::new` have the same shape — `Rc::get_mut` hands back a
/// `&mut &mut T` that `**` writes through — and `Snapshot::capture` /
/// `Snapshot::into_inner` / `Ghost::into_inner` return the payload by value,
/// so a captured `&mut T` comes back as a `&mut T`. I could not turn those
/// four into an exit-0 accept (`p3_rc_getmut.rs`, `p4_arc_getmut.rs` are
/// `unknown`/exit 2; `p5b`, `p7b` are refuted), so no live hole is CLAIMED for
/// them — they fail the criterion by signature, and deleting them is free
/// (below).
///
/// Only two shapes pass the criterion: a result that cannot carry the
/// argument at all, and a result that carries it only behind a SHARED
/// reference, since Rust's aliasing rules forbid deriving a `&mut` from a
/// `&`.
///
/// MEASURED (s48 v3 audit, 2026-09-14 — the evidence stands even though v3's
/// criterion did not). An instrumented driver logged every match of this rule
/// across all three corpora: the full Creusot `should_succeed` lane (278), the
/// full `should_fail` lane (99) and the 656-case adversarial corpus. Nineteen
/// of the twenty-eight entries the list then carried matched NOTHING in any of
/// them and were deleted. Of the nine survivors, only THREE were ever measured
/// to change a `&mut` position set: `std::ops::DerefMut::deref_mut` (11
/// suppressing matches), `std::boxed::Box::new` (4) and `::Ghost::new` (4).
/// Removing an entry can only ADD `&mut` advances, so every deletion narrows
/// acceptance; the six that never suppressed anything cost nothing measurable.
///
/// s48 v4 re-audited all nine survivors against the corrected criterion, with
/// a probe per entry in the `*b` / `**b` / `get_mut` / `into_inner` handback
/// shape. NONE of them passes it, so every tier below is EMPTY.
///
/// `std` smart-pointer constructors — EMPTY (s48 v4).
pub(in crate::mir_analysis::extract) const FORWARDING_STD_CALLEES: &[&str] = &[];

/// Ghost-level identities in a spec library, matched as a path SUFFIX because
/// the same items are re-exported under `trust_wp_std`, `creusot_std` and
/// `creusot_contracts` — EMPTY (s48 v4).
///
/// In the SMT encoding `Ghost<T>` IS `T`, which is exactly why these fail the
/// criterion: `Ghost::new(&mut x)` stores the reborrow and `into_inner` /
/// `inner_mut` hand it back, so the caller writes through a borrow whose
/// target the encoding still believes is frozen (`p6b_ghost_new_program_ref.rs`
/// above). The eight reference-returning ghost entries deleted in v3 —
/// `::Ghost::inner`, `::Ghost::inner_mut`, `::Ghost::deref`,
/// `::Ghost::deref_mut`, `::Ghost::borrow`, `::Ghost::borrow_mut`,
/// `::Snapshot::inner`, `::Snapshot::deref` — matched NOTHING in any of the
/// three corpora, and the `*_mut` ones among them were live exit-0 false
/// accepts on their own.
pub(in crate::mir_analysis::extract) const FORWARDING_SPEC_LIBRARY_SUFFIXES: &[&str] = &[];

/// `core`/`std` projection TRAIT methods that return a SHARED reference —
/// EMPTY (s48 v4).
///
/// `std::ops::Deref::deref` is the one entry the corrected criterion does NOT
/// condemn: its result is a `&T`, and no `&mut` can be derived from a `&`. It
/// is deleted anyway, because its receiver is `&Self` and so can never occupy
/// a `&mut` argument position: the instrumented run measured it matching
/// nothing and suppressing nothing in 1033 corpus cases. An allowlist entry
/// that cannot be shown doing any work is an accept path with no evidence
/// behind it, and deleting it can only add advances.
pub(in crate::mir_analysis::extract) const FORWARDING_SHARED_PROJECTION_TRAIT_PATHS: &[&str] = &[];

/// Items admitted AGAINST the soundness criterion — EMPTY.
///
/// This tier once carried `std::ops::DerefMut::deref_mut` for a ghost
/// receiver. `<Ghost<T> as DerefMut>::deref_mut` returns `&mut self.0`, a live
/// `&mut` reborrow of the receiver reachable from the result by definition, so
/// suppressing the receiver's advance is sound only if the caller's write
/// THROUGH the returned borrow is propagated back to the receiver. trust-wp
/// does not do that: `let r = g.deref_mut(); *r = 7;` followed by
/// `proof_assert!(*g == 5i32)` was accepted at exit 0 while the program leaves
/// `g == 7` — a positive false accept, not an `unknown`. The entry bought
/// Creusot coverage on ghost cells that are read through `*g` after a `&mut`
/// of the cell was taken, and `docs/GOAL.md` §3 decides that trade: soundness
/// beats coverage, always. The completeness it bought comes back from the
/// real fix — the substitution lane now chains the borrow a ghost cell's
/// `deref_mut` hands back to the cell, so the write flows back — never from
/// an entry here.
///
/// ADDING AN ENTRY HERE is adding a known false accept. It takes a probe of
/// the handback shape showing the entry cannot credit a false contract, a
/// `docs/soundness.md` entry naming the exposure, and a deliberate edit of
/// `forwarding_allowlist_carries_no_argument_handback_outside_quarantine`,
/// which pins this list empty.
pub(in crate::mir_analysis::extract) const MUT_REBORROW_PROJECTION_PATHS_KNOWN_UNSOUND: &[&str] =
    &[];

/// Does this printed def path name one of the borrow-forwarding library items?
///
/// Split out from [`callee_forwards_mut_borrow`] so the path rule is testable
/// without a `TyCtxt`. `is_std` / `is_spec_library` come from
/// [`crate::provenance::item_provenance`] and are what keeps a LOCAL item, or
/// any other foreign crate, from matching a path it merely spells the same.
pub(in crate::mir_analysis::extract) fn path_forwards_mut_borrow(
    stripped_path: &str,
    is_std: bool,
    is_spec_library: bool,
    receiver_is_ghost_like: bool,
) -> bool {
    if is_std && FORWARDING_STD_CALLEES.contains(&stripped_path) {
        return true;
    }
    if is_std
        && receiver_is_ghost_like
        && (FORWARDING_SHARED_PROJECTION_TRAIT_PATHS.contains(&stripped_path)
            || MUT_REBORROW_PROJECTION_PATHS_KNOWN_UNSOUND.contains(&stripped_path))
    {
        return true;
    }
    is_spec_library
        && FORWARDING_SPEC_LIBRARY_SUFFIXES
            .iter()
            .any(|suffix| stripped_path.ends_with(suffix))
}

/// Is this callee one of the fixed library items whose result cannot carry a
/// live `&mut` reborrow of the argument, so that suppressing the argument's
/// advance drops nothing the caller can later write through?
///
/// Skipping the advance for an argument asserts something about the callee's
/// BODY — that the caller's view of `*p` at the call's exit is still the entry
/// value, because the borrow was neither used nor handed back. trust-wp checks
/// no such thing about a user body, so the licence cannot come from the
/// contract text (see [`spec_result_carries_arg_reference`]). It comes from the
/// callee being one of a CLOSED list of library items whose body is a known
/// quantity — [`FORWARDING_STD_CALLEES`], [`FORWARDING_SPEC_LIBRARY_SUFFIXES`]
/// and, for a ghost-typed receiver only,
/// [`FORWARDING_SHARED_PROJECTION_TRAIT_PATHS`] — plus
/// [`MUT_REBORROW_PROJECTION_PATHS_KNOWN_UNSOUND`], the tier for entries
/// admitted against the criterion. All four are EMPTY.
///
/// WHAT MAKES AN ENTRY UNSOUND — corrected twice, and the second correction is
/// the one that matters:
///
/// - the ORIGINAL wording named "a body that writes through the `&mut`
///   argument". Wrong: an item that writes nothing can still be unsound.
/// - s48 v3 replaced it with "an item that RETURNS a live `&mut` reborrow of
///   the argument", and then read that narrowly, as if MOVING the argument
///   into the result made it safe. Also wrong, and refuted by probe:
///   `Box::new(&mut x)` moves the borrow into the box and `*b` hands it
///   straight back, `(**b)` reaches it in place, and the write through it was
///   accepted at exit 0 against a false `proof_assert`
///   (`~/wpcamp/s48/probes4/p1_box_deref_out.rs`, `p2_box_vec_push.rs`). The
///   same for `ghost! { Ghost::new(&mut x) }` + `into_inner`
///   (`p6b_ghost_new_program_ref.rs`).
///
/// THE CRITERION (s48 v4): an entry is sound only if NO LIVE `&mut` REBORROW
/// OF THE ARGUMENT IS REACHABLE FROM THE RESULT — by any projection, deref,
/// unwrapping method, field read, iterator item or later call the caller can
/// apply to the result. Whether the argument was moved is irrelevant; what
/// matters is whether the caller can get a writable borrow of it back. A
/// result that cannot carry the argument at all passes, and so does a result
/// that carries it only behind a SHARED reference, because Rust forbids
/// deriving a `&mut` from a `&`. A container of any kind — `Box`, `Rc`,
/// `Arc`, `Ghost`, `Snapshot`, a tuple, a struct field — fails, because
/// containers exist to hand their contents back.
///
/// Every entry the list ever carried failed that test, including the
/// `<Ghost<T> as DerefMut>::deref_mut` entry that was carried against it for a
/// time as a ledgered false accept: all four tiers are EMPTY, and this
/// function currently returns `false` for every callee. It stays as the single
/// gate through which an entry would have to be re-admitted.
///
/// Two guards keep the rule off any other body:
///
/// - the match is on the full def path, not an item name, so no unrelated
///   `new` / `deref_mut` / `borrow_mut` / `into_inner` can reach it; and
/// - [`crate::provenance::item_provenance`] must independently say the item is
///   defined in `core`/`alloc`/`std` (for the exact paths) or in a spec library
///   (for the ghost suffixes). A LOCAL item — including the trait-method and
///   trait-default callees that reach the `ExternSpec` arm through step 8c of
///   `resolve_call` — can therefore never match, whatever it is called and
///   whatever its contract says.
///
/// A user `#[extern_spec]` that shadows one of these std paths does not widen
/// anything: the running callee is still the library item, and the argument
/// above is about that item's code, not about the spec that was written for it.
///
/// So: adding an item whose result can hand a `&mut` reborrow of an argument
/// back, or relaxing either guard so the list can be reached by a callee whose
/// body trust-wp does not fix, makes this unsound. That is pinned by
/// `forwarding_allowlist_carries_no_argument_handback_outside_quarantine` in
/// `extract/tests/closure_state.rs`, which requires the sound tiers to stay
/// empty and pins the quarantine's contents exactly. (s48 v4)
pub(in crate::mir_analysis::extract) fn callee_forwards_mut_borrow<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    body: &Body<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
) -> bool {
    let provenance = crate::provenance::item_provenance(tcx, def_id);
    let stripped = crate::mir_analysis::mut_borrow::strip_generics(&tcx.def_path_str(def_id));
    // The receiver of a projection trait method. `peel_refs` inside
    // `is_ghost_like_type` sees through the `&mut`.
    let receiver_is_ghost_like = args.first().is_some_and(|arg| {
        crate::ghost::type_helpers::is_ghost_like_type(tcx, arg.node.ty(&body.local_decls, tcx))
    });
    path_forwards_mut_borrow(
        &stripped,
        provenance == crate::provenance::ItemProvenance::Std,
        provenance == crate::provenance::ItemProvenance::SpecLibrary,
        receiver_is_ghost_like,
    )
}

#[allow(clippy::too_many_arguments)]
pub(in crate::mir_analysis::extract) fn resolved_call_mutating_ref_arg_positions<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
    func: &Operand<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    destination: Local,
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
    local_exprs: &impl ExprLookup,
) -> Vec<usize> {
    let mut positions = resolved_call_spec_mutating_ref_arg_positions(
        tcx,
        body,
        bb,
        func,
        args,
        destination,
        user_specs,
        trait_specs,
        extern_specs,
        local_exprs,
    );
    // The primary lane applies the same union at each of its own spec lanes
    // (`call_spec/spec_resolution.rs`, `call_spec/fallback.rs`). (s63)
    union_interior_mutable_write_positions(tcx, body, args, &mut positions);
    positions
}

/// The spec-derived half of [`resolved_call_mutating_ref_arg_positions`]:
/// which `&mut` positions the resolved callee may write through. Interior
/// mutability is decided by the caller above, for every resolution kind at
/// once — a per-kind decision is what drifted. (s63)
#[allow(clippy::too_many_arguments)]
fn resolved_call_spec_mutating_ref_arg_positions<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    bb: BasicBlock,
    func: &Operand<'tcx>,
    args: &[Spanned<Operand<'tcx>>],
    destination: Local,
    user_specs: &HashMap<DefId, StdSpec>,
    trait_specs: &HashMap<DefId, StdSpec>,
    extern_specs: &HashMap<String, StdSpec>,
    local_exprs: &impl ExprLookup,
) -> Vec<usize> {
    if let Some(closure_def_id) = extract_closure_def_id_from_fn_call(func) {
        if let Some(spec) = user_specs.get(&closure_def_id) {
            return if args
                .first()
                .and_then(|arg| mut_ref_local_for_operand(body, &arg.node))
                .is_some()
                && spec_mutates_closure_state(spec)
            {
                vec![0]
            } else {
                Vec::new()
            };
        }
    }

    let resolved = resolve_call(
        tcx,
        body,
        bb,
        func,
        args,
        destination,
        user_specs,
        trait_specs,
        extern_specs,
        None,
        local_exprs,
    );
    // A call with no resolvable callee, or an opaque callee (no contract),
    // may write through every `&mut` argument: advance them all (Creusot: an
    // unspecified callee leaves `^p` unconstrained). (soundness)
    let Some(def_id) = resolved.def_id else {
        return all_mut_ref_arg_positions(body, args);
    };

    match resolved.kind {
        ResolvedCallKind::Opaque => all_mut_ref_arg_positions(body, args),
        // A user/trait contract is NOT evidence that the callee left `*p`
        // alone: trust-wp never checks that a body honours a `result == p`
        // clause, and `#[ensures(result == p)] fn f(p: &mut u32) -> &mut u32
        // { *p = 9; p }` verifies today. So the borrow-forwarding exception
        // never applies in this lane — advance every `&mut` argument. (s48)
        ResolvedCallKind::DirectSpec(_) => all_mut_ref_arg_positions(body, args),
        ResolvedCallKind::ExternSpec(spec) => {
            let param_names =
                arg_names_for_def_id(tcx, def_id).or_else(|| spec.param_names.clone());
            spec_mutating_ref_arg_positions(
                body,
                args,
                &spec,
                param_names.as_deref(),
                callee_forwards_mut_borrow(tcx, def_id, body, args),
            )
        }
        // The remaining kinds are IDENTITIES on the call's RESULT — `dest :=
        // inner` for `Box::new`, the array length, the `?` branch value, an
        // `Int` passthrough, a layout constant, a `Mapping` built from a
        // closure. An identity on the result says nothing about the pointee
        // of a `&mut` ARGUMENT, and the s48 v4 audit showed why that
        // distinction is not academic: `Box::new(&mut x)` hands the reborrow
        // straight back (`*b`, `**b`), so suppressing `x`'s advance drops the
        // caller's write through it — three exit-0 false accepts on the
        // allowlist lane, which resolves the same callee through
        // `ExternSpec`. This arm is the OTHER lane onto the same callee
        // (`resolve_call` step 8's `Box::new` fallback, reached when the
        // extern spec does not apply), so it advances every `&mut` argument
        // too. Where an arm cannot receive a `&mut` argument at all — the
        // by-value and shared-receiver shapes — this is exactly the empty
        // vector it returned before. (s48 v4 soundness)
        ResolvedCallKind::ArrayLen(_)
        | ResolvedCallKind::TryBranch
        | ResolvedCallKind::BoxNew
        | ResolvedCallKind::IntPassthrough(_)
        | ResolvedCallKind::LayoutIntrinsic(_)
        | ResolvedCallKind::MappingFromClosure
        | ResolvedCallKind::MapInvFromClosure => all_mut_ref_arg_positions(body, args),
    }
}
