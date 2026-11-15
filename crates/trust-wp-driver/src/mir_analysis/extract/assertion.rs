// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Assertion terminator helpers shared by extraction variants.

use std::sync::Arc;

use rustc_hir::def_id::DefId;
use rustc_middle::{
    mir::{AssertKind, BinOp as MirBinOp, Body, Operand},
    ty::{TyCtxt, TyKind},
};
use trust_wp_core::formula::{
    int_bounds::{signed_bounds_expr, unsigned_max_expr},
    BinOp, PureExpr, UnOp,
};

use super::super::{
    effects::{fail_closed_marker, CallEffects},
    spanned::SpannedBodyExpr,
    translate::ExprLookup,
};
use crate::mir_analysis::translate::translate_operand;

/// Whether `msg` is a machine-integer arithmetic panic assert: checked
/// `+`/`-`/`*` overflow, signed `MIN / -1` and `MIN % -1` overflow, signed
/// negation overflow, division/remainder by zero, or an out-of-range shift
/// amount (`<<`/`>>` panic in debug builds unless `0 <= amount < BITS`).
///
/// Creusot models each of these operations as a PROGRAM function whose
/// precondition is exactly the assert's success condition
/// (`prelude-generator/int.in.coma`: `add`/`sub`/`mul` require
/// `in_bounds (a op b)`, `neg` requires `a <> min_int`, `div`/`rem` require
/// `b <> 0` and, signed, `not (a = min_int /\ b = -1)`), so each is a PROOF
/// obligation, never an assumable fact. See [`arithmetic_panic_obligation`].
pub(super) fn is_arithmetic_panic_assert(msg: &AssertKind<Operand<'_>>) -> bool {
    matches!(
        msg,
        AssertKind::Overflow(
            MirBinOp::Add
                | MirBinOp::Sub
                | MirBinOp::Mul
                | MirBinOp::Div
                | MirBinOp::Rem
                | MirBinOp::Shl
                | MirBinOp::Shr,
            ..
        ) | AssertKind::OverflowNeg(_)
            | AssertKind::DivisionByZero(_)
            | AssertKind::RemainderByZero(_)
    )
}

/// Whether `msg` is an assert whose goal an obligation lane charges at its
/// program point: an arithmetic panic assert ([`arithmetic_panic_obligation`])
/// or a built-in index bounds check ([`bounds_check_obligation`]).
///
/// Two structural checks key on exactly this predicate, in opposite
/// directions: `unwalked_charged_assert_sites` demotes a `verified` verdict
/// when a reachable site of this class had no obligation stated for it by a
/// kept lane, and `unchecked_panic_sites` exempts this class from the
/// clause-free cap BECAUSE the first check owns it. A kind added here without
/// a lane that records it demotes every body containing it; a kind removed
/// moves under the cap. Neither direction can verify an unstated goal.
pub(super) fn is_charged_assert(msg: &AssertKind<Operand<'_>>) -> bool {
    is_arithmetic_panic_assert(msg) || matches!(msg, AssertKind::BoundsCheck { .. })
}

/// Machine-integer width/signedness of an assert operand, from its MIR type.
fn assert_operand_int_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    operand: &Operand<'tcx>,
    body: &Body<'tcx>,
) -> Option<(bool, u32)> {
    let pointer_bits = u32::try_from(tcx.data_layout.pointer_size().bits()).ok()?;
    match operand.ty(&body.local_decls, tcx).kind() {
        TyKind::Int(int_ty) => {
            let bits = int_ty
                .bit_width()
                .map_or(Some(pointer_bits), |b| u32::try_from(b).ok())?;
            Some((true, bits))
        }
        TyKind::Uint(uint_ty) => {
            let bits = uint_ty
                .bit_width()
                .map_or(Some(pointer_bits), |b| u32::try_from(b).ok())?;
            Some((false, bits))
        }
        _ => None,
    }
}

/// `min(ty) <= value && value <= max(ty)` when `ty` is a machine integer —
/// a literal consequence of Rust's type semantics for any value of `ty`.
pub(crate) fn machine_int_range_fact<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    value: PureExpr,
) -> Option<PureExpr> {
    let pointer_bits = u32::try_from(tcx.data_layout.pointer_size().bits()).ok()?;
    let (signed, bits) = match ty.kind() {
        TyKind::Int(int_ty) => (
            true,
            int_ty
                .bit_width()
                .map_or(Some(pointer_bits), |b| u32::try_from(b).ok())?,
        ),
        TyKind::Uint(uint_ty) => (
            false,
            uint_ty
                .bit_width()
                .map_or(Some(pointer_bits), |b| u32::try_from(b).ok())?,
        ),
        _ => return None,
    };
    Some(machine_int_in_bounds(value, signed, bits))
}

fn arith_binop(left: PureExpr, op: BinOp, right: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(left), op, Arc::new(right))
}

/// `min(ty) <= value && value <= max(ty)` for a machine integer type.
fn machine_int_in_bounds(value: PureExpr, signed: bool, bits: u32) -> PureExpr {
    let (lo, hi) = if signed {
        signed_bounds_expr(bits)
    } else {
        (PureExpr::Int(0), unsigned_max_expr(bits))
    };
    arith_binop(
        arith_binop(lo, BinOp::Le, value.clone()),
        BinOp::And,
        arith_binop(value, BinOp::Le, hi),
    )
}

/// Translate an assert operand, falling back to the body-typed field-place
/// translation (`a.0` of a struct translated as a tuple) that the untyped
/// operand translator cannot resolve. Both denote the operand's value.
fn translate_assert_operand<'tcx>(
    tcx: TyCtxt<'tcx>,
    operand: &Operand<'tcx>,
    local_exprs: &impl ExprLookup,
    body: &Body<'tcx>,
) -> Option<PureExpr> {
    translate_operand(operand, local_exprs).or_else(|| match operand {
        Operand::Copy(place) | Operand::Move(place) if !place.projection.is_empty() => {
            crate::mir_analysis::translate::translate_typed_field_place(
                tcx,
                body,
                place,
                local_exprs,
            )
        }
        _ => None,
    })
}

fn build_arithmetic_panic_obligation<'tcx>(
    tcx: TyCtxt<'tcx>,
    cond: &Operand<'tcx>,
    expected: bool,
    msg: &AssertKind<Operand<'tcx>>,
    local_exprs: &impl ExprLookup,
    body: &Body<'tcx>,
) -> Option<PureExpr> {
    match msg {
        AssertKind::Overflow(op @ (MirBinOp::Add | MirBinOp::Sub | MirBinOp::Mul), left, right) => {
            let (signed, bits) = assert_operand_int_ty(tcx, left, body)?;
            let op = match op {
                MirBinOp::Add => BinOp::Add,
                MirBinOp::Sub => BinOp::Sub,
                _ => BinOp::Mul,
            };
            let value = arith_binop(
                translate_assert_operand(tcx, left, local_exprs, body)?,
                op,
                translate_assert_operand(tcx, right, local_exprs, body)?,
            );
            Some(machine_int_in_bounds(value, signed, bits))
        }
        // rustc's shift check is `(amount as unsigned) < BITS` over the
        // SHIFTED operand's width: for any amount type that is exactly
        // `0 <= amount < BITS`.
        AssertKind::Overflow(MirBinOp::Shl | MirBinOp::Shr, left, right) => {
            let (_, bits) = assert_operand_int_ty(tcx, left, body)?;
            let amount = translate_assert_operand(tcx, right, local_exprs, body)?;
            Some(arith_binop(
                arith_binop(PureExpr::Int(0), BinOp::Le, amount.clone()),
                BinOp::And,
                arith_binop(amount, BinOp::Lt, PureExpr::Int(i64::from(bits))),
            ))
        }
        AssertKind::Overflow(MirBinOp::Div | MirBinOp::Rem, left, right) => {
            let (signed, bits) = assert_operand_int_ty(tcx, left, body)?;
            if !signed {
                // Unsigned `/` and `%` cannot overflow (rustc emits no such
                // assert; Creusot's UInt `div`/`rem` carry no overflow goal).
                return Some(PureExpr::Bool(true));
            }
            let (min, _) = signed_bounds_expr(bits);
            let is_min = arith_binop(
                translate_assert_operand(tcx, left, local_exprs, body)?,
                BinOp::Eq,
                min,
            );
            let is_minus_one = arith_binop(
                translate_assert_operand(tcx, right, local_exprs, body)?,
                BinOp::Eq,
                PureExpr::Int(-1),
            );
            Some(PureExpr::UnOp(
                UnOp::Not,
                Arc::new(arith_binop(is_min, BinOp::And, is_minus_one)),
            ))
        }
        AssertKind::OverflowNeg(operand) => {
            let (signed, bits) = assert_operand_int_ty(tcx, operand, body)?;
            if !signed {
                return None;
            }
            let (min, _) = signed_bounds_expr(bits);
            Some(arith_binop(
                translate_assert_operand(tcx, operand, local_exprs, body)?,
                BinOp::Ne,
                min,
            ))
        }
        // rustc's `DivisionByZero(op)` / `RemainderByZero(op)` carry the
        // DIVIDEND (for the panic message), not the divisor: the success
        // condition is the assert's own `cond == expected` (`!(rhs == 0)`).
        AssertKind::DivisionByZero(_) | AssertKind::RemainderByZero(_) => {
            let cond_expr = translate_operand(cond, local_exprs)?;
            Some(match (expected, cond_expr) {
                (true, cond_expr) => cond_expr,
                // rustc's divisor check is `Eq(rhs, 0)` expected `false`:
                // state it as `rhs != 0`, the shape the encoder's own
                // divisor obligation uses.
                (false, PureExpr::BinOp(lhs, BinOp::Eq, rhs)) => {
                    PureExpr::BinOp(lhs, BinOp::Ne, rhs)
                }
                (false, cond_expr) => PureExpr::UnOp(UnOp::Not, Arc::new(cond_expr)),
            })
        }
        _ => None,
    }
}

/// The proof obligation owed by a machine-integer arithmetic panic assert
/// (see [`is_arithmetic_panic_assert`]), stated over the assert's own
/// operands at the assert's program point.
///
/// Returns `None` for every other assert kind. When the operands cannot be
/// translated the obligation is `false` (fail closed): an arithmetic panic
/// site the extractor cannot state is an unproved panic site, never a
/// silently dropped one — the same fallback call preconditions use
/// (`call_spec/fallback.rs`).
///
/// The overflow flag the MIR assert actually tests (`_t.1` of a
/// `*WithOverflow` tuple) is not modelled by the translator, so the goal is
/// rebuilt from the operands carried by the `AssertKind`: for
/// `Overflow(Add, a, b)` it is `MIN <= a + b <= MAX` over `a`'s type,
/// exactly Creusot's `in_bounds (t'int a + t'int b)`.
pub(super) fn arithmetic_panic_obligation<'tcx>(
    tcx: TyCtxt<'tcx>,
    cond: &Operand<'tcx>,
    expected: bool,
    msg: &AssertKind<Operand<'tcx>>,
    local_exprs: &impl ExprLookup,
    body: &Body<'tcx>,
) -> Option<PureExpr> {
    if !is_arithmetic_panic_assert(msg) {
        return None;
    }
    let Some(obligation) =
        build_arithmetic_panic_obligation(tcx, cond, expected, msg, local_exprs, body)
    else {
        return Some(fail_closed_marker("arith-panic-untranslated"));
    };
    Some(guard_with_operand_type_ranges(
        tcx,
        msg,
        local_exprs,
        body,
        obligation,
    ))
}

/// Core operator traits on primitive integers: (trait, primitive op, `*Assign`).
const OPERATOR_TRAITS: [(rustc_attr_ir::LangItem, Option<MirBinOp>, bool); 15] = {
    use rustc_attr_ir::LangItem;
    [
        (LangItem::Add, Some(MirBinOp::Add), false),
        (LangItem::Sub, Some(MirBinOp::Sub), false),
        (LangItem::Mul, Some(MirBinOp::Mul), false),
        (LangItem::Div, Some(MirBinOp::Div), false),
        (LangItem::Rem, Some(MirBinOp::Rem), false),
        (LangItem::Shl, Some(MirBinOp::Shl), false),
        (LangItem::Shr, Some(MirBinOp::Shr), false),
        (LangItem::Neg, None, false),
        (LangItem::AddAssign, Some(MirBinOp::Add), true),
        (LangItem::SubAssign, Some(MirBinOp::Sub), true),
        (LangItem::MulAssign, Some(MirBinOp::Mul), true),
        (LangItem::DivAssign, Some(MirBinOp::Div), true),
        (LangItem::RemAssign, Some(MirBinOp::Rem), true),
        (LangItem::ShlAssign, Some(MirBinOp::Shl), true),
        (LangItem::ShrAssign, Some(MirBinOp::Shr), true),
    ]
};

/// Whether `def_id` (with `generic_args`) is a core operator-trait method on a
/// primitive integer (by value or through a reference): a call whose panic
/// condition `operator_call_obligation` states.
pub(super) fn is_integer_operator_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: rustc_hir::def_id::DefId,
    generic_args: rustc_middle::ty::GenericArgs<'tcx>,
) -> bool {
    let Some(trait_id) = tcx.trait_of_assoc(def_id) else {
        return false;
    };
    let Some((_, _, assign)) = OPERATOR_TRAITS
        .iter()
        .copied()
        .find(|(item, _, _)| tcx.is_lang_item(trait_id, *item))
    else {
        return false;
    };
    let is_int =
        |ty: rustc_middle::ty::Ty<'tcx>| matches!(ty.kind(), TyKind::Int(_) | TyKind::Uint(_));
    let int_or_ref = |ty: rustc_middle::ty::Ty<'tcx>| match ty.kind() {
        TyKind::Ref(_, inner, _) => is_int(*inner),
        _ => is_int(ty),
    };
    let Some(self_ty) = generic_args.types().next() else {
        return false;
    };
    if assign {
        is_int(self_ty)
    } else {
        int_or_ref(self_ty)
    }
}

/// `Iterator::sum`/`product` or `Sum::sum`/`Product::product` producing a
/// primitive integer.
fn is_integer_fold_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: rustc_hir::def_id::DefId,
    destination_ty: rustc_middle::ty::Ty<'tcx>,
) -> bool {
    if !matches!(destination_ty.kind(), TyKind::Int(_) | TyKind::Uint(_)) {
        return false;
    }
    if tcx.crate_name(def_id.krate).as_str() != "core" {
        return false;
    }
    let Some(trait_id) = tcx.trait_of_assoc(def_id) else {
        return false;
    };
    matches!(
        (
            tcx.item_name(trait_id).as_str(),
            tcx.item_name(def_id).as_str()
        ),
        ("Iterator", "sum" | "product") | ("Sum", "sum") | ("Product", "product")
    )
}

/// The proof obligation owed by a call to a core operator-trait method on
/// primitive integers: `<&u8 as Add<u8>>::add`, `<u8 as Sub<&u8>>::sub`,
/// `<u8 as AddAssign<&u8>>::add_assign`, `<&i8 as Neg>::neg`, `<u8 as
/// Div>::div`, ... (by value or through a reference on either side).
///
/// These calls carry no MIR `Assert` in the caller, but core's by-value
/// impls are `#[rustc_inherit_overflow_checks] fn add(self, o) { self + o }`
/// (and `/`, `%` always check the divisor), and the by-reference impls
/// (`forward_ref_binop!`, `forward_ref_unop!`, `forward_ref_op_assign!`)
/// only dereference and forward. With `-C overflow-checks=on`,
/// `&255u8 + 1`, `&0u8 - &1u8`, `255u8 += &1`,
/// `-&i8::MIN` and `&1u8 << 8` panic; `&1u8 / 0` panics without overflow
/// checks too. So each call owes exactly the primitive operation's
/// obligation, stated over the dereferenced operands. An operand this
/// function cannot state (e.g. a promoted `&1` constant) makes the
/// obligation `false`.
///
/// The target is resolved through fn-pointer locals as well
/// (`let f: fn(u8, u8) -> u8 = <u8 as Add>::add; f(x, 1)` owes exactly what
/// `x + 1` owes; see `resolve_unique_call_fn_def`).
///
/// `Iterator::sum`/`Iterator::product` (and `Sum::sum`/`Product::product`)
/// into a primitive integer are `#[rustc_inherit_overflow_checks]` folds of
/// `+`/`*` over every produced element: no obligation over the iterator's
/// elements is stated, so such a call owes `false` (fail closed).
pub(super) fn operator_call_obligation<'tcx>(
    tcx: TyCtxt<'tcx>,
    func: &Operand<'tcx>,
    args: &[rustc_span::Spanned<Operand<'tcx>>],
    destination_ty: rustc_middle::ty::Ty<'tcx>,
    local_exprs: &impl ExprLookup,
    body: &Body<'tcx>,
) -> Option<PureExpr> {
    use rustc_middle::mir::ProjectionElem;

    let (def_id, generic_args) = super::call_resolve_util::resolve_unique_call_fn_def(body, func)?;
    if is_integer_fold_call(tcx, def_id, destination_ty) {
        return Some(fail_closed_marker("integer-fold-call"));
    }
    let trait_id = tcx.trait_of_assoc(def_id)?;
    let (_, op, assign) = OPERATOR_TRAITS
        .iter()
        .copied()
        .find(|(item, _, _)| tcx.is_lang_item(trait_id, *item))?;

    // `Some(Some(operand))`: the integer operand; `Some(None)`: an integer
    // operand this function cannot state; `None`: not a primitive integer.
    let deref = |operand: &Operand<'tcx>| match operand {
        Operand::Copy(place) | Operand::Move(place) => Some(Operand::Copy(
            place.project_deeper(&[ProjectionElem::Deref], tcx),
        )),
        _ => None,
    };
    let integer_operand = |ty: rustc_middle::ty::Ty<'tcx>, operand: &Operand<'tcx>| match ty.kind()
    {
        TyKind::Int(_) | TyKind::Uint(_) => Some(Some(operand.clone())),
        TyKind::Ref(_, inner, _) if matches!(inner.kind(), TyKind::Int(_) | TyKind::Uint(_)) => {
            Some(deref(operand))
        }
        _ => None,
    };

    let self_ty = generic_args.type_at(0);
    let first = &args.first()?.node;
    let lhs = if assign {
        // `fn add_assign(&mut self, rhs)`: the operand is `*arg0`.
        if !matches!(self_ty.kind(), TyKind::Int(_) | TyKind::Uint(_)) {
            return None;
        }
        deref(first)
    } else {
        integer_operand(self_ty, first)?
    };
    let Some(op) = op else {
        let Some(lhs) = lhs else {
            return Some(fail_closed_marker("checked-op-lhs-untranslated"));
        };
        return arithmetic_panic_obligation(
            tcx,
            &lhs,
            true,
            &AssertKind::OverflowNeg(lhs.clone()),
            local_exprs,
            body,
        );
    };
    let rhs_ty = generic_args.types().nth(1)?;
    let rhs = integer_operand(rhs_ty, &args.get(1)?.node)?;
    let (Some(lhs), Some(rhs)) = (lhs, rhs) else {
        return Some(fail_closed_marker("checked-op-operand-untranslated"));
    };
    let overflow = arithmetic_panic_obligation(
        tcx,
        &lhs,
        true,
        &AssertKind::Overflow(op, lhs.clone(), rhs.clone()),
        local_exprs,
        body,
    )
    .unwrap_or_else(|| fail_closed_marker("checked-op-overflow-untranslated"));
    if !matches!(op, MirBinOp::Div | MirBinOp::Rem) {
        return Some(overflow);
    }
    let Some(divisor) = translate_assert_operand(tcx, &rhs, local_exprs, body) else {
        return Some(fail_closed_marker("divisor-untranslated"));
    };
    let nonzero = arith_binop(divisor, BinOp::Ne, PureExpr::Int(0));
    Some(arith_binop(nonzero, BinOp::And, overflow))
}

/// Guard an arithmetic obligation with the machine-int range of each of the
/// assert's operands (`MIN(T) <= operand <= MAX(T)` for its MIR type `T`).
///
/// Every operand of a machine-int operation IS a value of its type, so the
/// hypothesis is a literal consequence of Rust's type semantics. It matters
/// whenever the translated operand is an otherwise unconstrained symbol — a
/// const-generic parameter (`const { N + 1 }` with `N: u32` must be refuted
/// by `N = u32::MAX`, never by a meaningless `N = -2`) or a havocked
/// loop-carried local.
fn guard_with_operand_type_ranges<'tcx>(
    tcx: TyCtxt<'tcx>,
    msg: &AssertKind<Operand<'tcx>>,
    local_exprs: &impl ExprLookup,
    body: &Body<'tcx>,
    obligation: PureExpr,
) -> PureExpr {
    let operands: Vec<&Operand<'tcx>> = match msg {
        AssertKind::Overflow(_, left, right) => vec![left, right],
        AssertKind::OverflowNeg(operand) => vec![operand],
        _ => Vec::new(),
    };
    let mut facts = Vec::new();
    for operand in operands {
        let Some(value) = translate_assert_operand(tcx, operand, local_exprs, body) else {
            continue;
        };
        if matches!(value, PureExpr::Int(_)) {
            continue;
        }
        if let Some(fact) = machine_int_range_fact(tcx, operand.ty(&body.local_decls, tcx), value) {
            if !facts.contains(&fact) {
                facts.push(fact);
            }
        }
    }
    // Const-generic parameters (`const N: u32`) are values of their declared
    // machine-int type in every instantiation. A binding or parameter can
    // never shadow a const parameter (E0530), so a free `Var` carrying the
    // parameter's name IS that parameter.
    let free_vars = obligation.free_vars();
    let mut generics = tcx.generics_of(body.source.def_id());
    loop {
        for param in &generics.own_params {
            if !matches!(
                param.kind,
                rustc_middle::ty::GenericParamDefKind::Const { .. }
            ) {
                continue;
            }
            let name = param.name.to_string();
            if !free_vars.contains(&name) {
                continue;
            }
            let ty = tcx
                .type_of(param.def_id)
                .instantiate_identity()
                .skip_norm_wip();
            let sort = crate::mir_analysis::translate::ty_to_expr_sort_enriched(tcx, ty);
            if let Some(fact) = machine_int_range_fact(tcx, ty, PureExpr::Var(name, sort)) {
                if !facts.contains(&fact) {
                    facts.push(fact);
                }
            }
        }
        match generics.parent {
            Some(parent) => generics = tcx.generics_of(parent),
            None => break,
        }
    }
    let Some(guard) = facts
        .into_iter()
        .reduce(|acc, fact| arith_binop(acc, BinOp::And, fact))
    else {
        return obligation;
    };
    arith_binop(guard, BinOp::Implies, obligation)
}

/// The proof obligation owed by a MIR `Assert` that lies on a path which can
/// only DIVERGE (every path from its success target diverges, e.g. an arm that
/// ends in a trusted inert spin `fn spin() -> ! { loop {} }`).
///
/// Such a path has no continuation that the result expression could carry, so
/// the assert's check would otherwise be dropped with the arm: the arm is
/// assumed unreachable for the returning path, but execution still reaches the
/// assert first, and a failing check panics. Creusot models each check as a
/// program-function precondition (`int.in.coma`: `add`/`sub`/`mul` require
/// `in_bounds`, `neg` requires `a <> min`, `div`/`rem` require `b <> 0` and,
/// signed, `not (a = min /\ b = -1)`, shifts require `0 <= amount < BITS`;
/// slice/array `Index` requires `ix < len`), so each is an OBLIGATION here.
///
/// Every operand read must be value stable (see
/// `switch_discr_is_value_stable`); an unstable or untranslatable operand, an
/// unknown integer type, or an assert kind not listed above yields `false`
/// (fail closed). Returning `false` costs completeness, never soundness.
pub(super) fn diverging_path_assert_obligation<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    cond: &Operand<'tcx>,
    expected: bool,
    msg: &AssertKind<Operand<'tcx>>,
    local_exprs: &impl ExprLookup,
    flow_insensitive: bool,
) -> PureExpr {
    build_diverging_path_assert_obligation(
        tcx,
        body,
        cond,
        expected,
        msg,
        local_exprs,
        flow_insensitive,
    )
    .unwrap_or_else(|| fail_closed_marker("diverging-assert-untranslated"))
}

fn build_diverging_path_assert_obligation<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    cond: &Operand<'tcx>,
    expected: bool,
    msg: &AssertKind<Operand<'tcx>>,
    local_exprs: &impl ExprLookup,
    flow_insensitive: bool,
) -> Option<PureExpr> {
    use trust_wp_core::formula::{
        int_bounds::{signed_bounds_expr, unsigned_max_expr},
        BinOp,
    };
    let bin = |l: PureExpr, op: BinOp, r: PureExpr| PureExpr::BinOp(Arc::new(l), op, Arc::new(r));
    // A stable, translated operand value.
    let value = |operand: &Operand<'tcx>| -> Option<PureExpr> {
        super::helpers::switch_discr_is_value_stable(tcx, body, operand, flow_insensitive)
            .then(|| translate_operand(operand, local_exprs))
            .flatten()
    };
    // (signed, bits) of a machine-integer operand.
    let int_ty = |operand: &Operand<'tcx>| -> Option<(bool, u32)> {
        let pointer_bits = u32::try_from(tcx.data_layout.pointer_size().bits()).ok()?;
        match operand.ty(&body.local_decls, tcx).kind() {
            rustc_middle::ty::TyKind::Int(t) => Some((
                true,
                t.bit_width()
                    .map_or(Some(pointer_bits), |b| u32::try_from(b).ok())?,
            )),
            rustc_middle::ty::TyKind::Uint(t) => Some((
                false,
                t.bit_width()
                    .map_or(Some(pointer_bits), |b| u32::try_from(b).ok())?,
            )),
            _ => None,
        }
    };
    let in_bounds = |v: PureExpr, signed: bool, bits: u32| {
        let (lo, hi) = if signed {
            signed_bounds_expr(bits)
        } else {
            (PureExpr::Int(0), unsigned_max_expr(bits))
        };
        bin(
            bin(lo, BinOp::Le, v.clone()),
            BinOp::And,
            bin(v, BinOp::Le, hi),
        )
    };
    match msg {
        AssertKind::Overflow(op @ (MirBinOp::Add | MirBinOp::Sub | MirBinOp::Mul), left, right) => {
            let (signed, bits) = int_ty(left)?;
            let op = match op {
                MirBinOp::Add => BinOp::Add,
                MirBinOp::Sub => BinOp::Sub,
                _ => BinOp::Mul,
            };
            Some(in_bounds(
                bin(value(left)?, op, value(right)?),
                signed,
                bits,
            ))
        }
        AssertKind::Overflow(MirBinOp::Shl | MirBinOp::Shr, left, right) => {
            let (_, bits) = int_ty(left)?;
            int_ty(right)?;
            let amount = value(right)?;
            Some(bin(
                bin(PureExpr::Int(0), BinOp::Le, amount.clone()),
                BinOp::And,
                bin(amount, BinOp::Lt, PureExpr::Int(i64::from(bits))),
            ))
        }
        AssertKind::Overflow(MirBinOp::Div | MirBinOp::Rem, left, right) => {
            let (signed, bits) = int_ty(left)?;
            if !signed {
                return None;
            }
            let (min, _) = signed_bounds_expr(bits);
            Some(PureExpr::UnOp(
                UnOp::Not,
                Arc::new(bin(
                    bin(value(left)?, BinOp::Eq, min),
                    BinOp::And,
                    bin(value(right)?, BinOp::Eq, PureExpr::Int(-1)),
                )),
            ))
        }
        AssertKind::OverflowNeg(operand) => {
            let (signed, bits) = int_ty(operand)?;
            if !signed {
                return None;
            }
            let (min, _) = signed_bounds_expr(bits);
            Some(bin(value(operand)?, BinOp::Ne, min))
        }
        // The by-zero kinds carry the DIVIDEND (for the message), not the
        // divisor, so the obligation is the assert's own condition
        // (`!(divisor == 0)`), exactly like the bounds check (`index < len`).
        AssertKind::DivisionByZero(_)
        | AssertKind::RemainderByZero(_)
        | AssertKind::BoundsCheck { .. } => {
            let cond = value(cond)?;
            Some(if expected {
                cond
            } else {
                PureExpr::UnOp(UnOp::Not, Arc::new(cond))
            })
        }
        _ => None,
    }
}

/// The proof obligation owed by a built-in index bounds check
/// (`AssertKind::BoundsCheck`, emitted for `a[i]` on arrays and slices).
///
/// Creusot's `Index` spec for `[T]`/`[T; N]` requires `ix.in_bounds(self@)`,
/// i.e. `ix@ < self@.len()`, and the MIR assert condition is exactly
/// `Lt(ix, len)`. The obligation is that condition at the assert's program
/// point. When the condition may read a stale value (see
/// `switch_discr_is_value_stable`) or does not translate, the obligation is
/// `false` (fail closed). Returns `None` for every other assert kind.
pub(super) fn bounds_check_obligation<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    cond: &Operand<'tcx>,
    expected: bool,
    msg: &AssertKind<Operand<'tcx>>,
    local_exprs: &impl ExprLookup,
    body: &rustc_middle::mir::Body<'tcx>,
    flow_insensitive: bool,
) -> Option<PureExpr> {
    if !matches!(msg, AssertKind::BoundsCheck { .. }) {
        return None;
    }
    if !super::helpers::switch_discr_is_value_stable(tcx, body, cond, flow_insensitive) {
        return Some(fail_closed_marker("bounds-check-unstable"));
    }
    Some(
        translate_operand(cond, local_exprs)
            .map(|cond_expr| {
                if expected {
                    cond_expr
                } else {
                    PureExpr::UnOp(UnOp::Not, Arc::new(cond_expr))
                }
            })
            .unwrap_or_else(|| fail_closed_marker("bounds-check-untranslated")),
    )
}

/// The obligation owed by a MIR `Drop` of `place` whose drop glue runs a
/// user `Drop::drop` that is not known to be panic-free.
///
/// Creusot lowers `Drop` to a jump and checks each `Drop` impl's body as its
/// own program function. trust-wp does not examine contract-free `Drop`
/// bodies, so a drop site whose glue reaches a LOCAL `Drop::drop` impl without
/// a contract (or with a non-trivial `requires`, which the call site cannot
/// state) owes `false`. A contracted impl with trivial `requires` is verified
/// as its own item and owes nothing here. A type defined in `core`/`alloc`/
/// `std` does not panic by itself when dropped; only its generic type
/// arguments (the values it owns and drops) are walked, never its private
/// fields (a `HashSet<T>` is a `hashbrown` table internally, a sysroot crate
/// whose destructor is part of std's own). Destructors of other foreign crates
/// are unknown and fail closed.
///
/// Generic parameters, trait objects and opaque types are NOT decided here
/// (their glue is only known at instantiation, and Creusot owes no goal at
/// the drop site): such drops rely on every `Drop` impl body being checked as
/// an item.
pub(super) fn drop_glue_obligation<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    place: &rustc_middle::mir::Place<'tcx>,
    user_specs: &std::collections::HashMap<rustc_hir::def_id::DefId, trust_wp_driver::StdSpec>,
) -> Option<PureExpr> {
    let ty = place.ty(&body.local_decls, tcx).ty;
    let typing_env = body.typing_env(tcx);
    let mut visited = std::collections::HashSet::new();
    drop_glue_runs_unchecked_user_drop(tcx, typing_env, ty, user_specs, &mut visited, 0)
        .then(|| fail_closed_marker("drop-glue-unchecked-user-drop"))
}

/// The obligation owed by a CALL that may drop values of the types it is
/// instantiated with: `false` when one of the callee's generic type arguments
/// (the `Self` type of a method included) has drop glue that runs an unchecked
/// user `Drop::drop` (see [`drop_glue_obligation`]), unless the callee is a
/// core/alloc/std function known NOT to drop values of its type arguments
/// ([`std_callee_never_drops_type_args`]).
///
/// A std container method drops elements inside std (`Vec::<D>::clear`,
/// `truncate`, `retain`, `dedup`, a shrinking `resize`, `HashMap::insert` of an
/// existing key, `Option::insert`, `Cell::set`, an iterator adapter that
/// discards items), and a generic local or foreign callee instantiated at such
/// a type (`fn g<T>(v: Vec<T>) {}` at `T = D`) drops it in a body whose drop
/// sites were checked only for the generic `T`. Neither drop is a MIR `Drop`
/// of the caller, so the call site owes the obligation. Classification is by
/// `DefId` provenance (crate name, owning type or trait, item name), never by
/// a printed path; an unlisted callee fails closed. Over-approximating only
/// costs completeness for programs with an unchecked panicking destructor.
///
/// The callee is resolved by [`resolved_callee`], the same chain that decides
/// whose contract is credited here, so a fn-pointer coercion
/// (`let f: fn(Vec<D>) = sink::<D>; f(v)`) owes what the direct call owes.
pub(super) fn call_drop_obligation<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    bb: rustc_middle::mir::BasicBlock,
    func: &Operand<'tcx>,
    user_specs: &std::collections::HashMap<rustc_hir::def_id::DefId, trust_wp_driver::StdSpec>,
) -> Option<PureExpr> {
    let (def_id, generic_args) = resolved_callee(tcx, body, bb, func)?;
    let typing_env = body.typing_env(tcx);
    let drops_unchecked = generic_args.types().any(|ty| {
        let ty = tcx
            .try_normalize_erasing_regions(
                typing_env,
                rustc_middle::ty::set_aliases_to_non_rigid(tcx, ty),
            )
            .unwrap_or(ty);
        let mut visited = std::collections::HashSet::new();
        drop_glue_runs_unchecked_user_drop(tcx, typing_env, ty, user_specs, &mut visited, 0)
    });
    if !drops_unchecked || call_never_drops_type_args(tcx, body, def_id, generic_args) {
        return None;
    }
    Some(fail_closed_marker("std-callee-drops-unchecked"))
}

/// Every type-driven obligation a call site owes before its callee runs:
/// [`call_drop_obligation`] and [`call_interior_instantiation_obligation`].
pub(super) fn call_type_obligation<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    bb: rustc_middle::mir::BasicBlock,
    func: &Operand<'tcx>,
    user_specs: &std::collections::HashMap<rustc_hir::def_id::DefId, trust_wp_driver::StdSpec>,
) -> Option<PureExpr> {
    call_drop_obligation(tcx, body, bb, func, user_specs)
        .or_else(|| call_interior_instantiation_obligation(tcx, body, bb, func))
}

/// The callee a call site's `func` operand denotes — resolved by the UNION of
/// every chain any lane walks before it credits that callee's contract at the
/// site:
///
/// 1. the `FnDef` the operand's own type carries;
/// 2. the `FnDef` constant the BLOCK-LOCAL call-target backtracker reaches
///    from the operand's local ([`resolve_call_fn_def`]), which is what the
///    primary extractor's `resolve_call` credits from;
/// 3. the `FnDef` constant the WHOLE-BODY backtracker reaches
///    ([`resolve_unique_call_fn_def`]), which is what the loop lanes'
///    `classify_loop_call_target` credits from.
///
/// Both type-driven call obligations key on this one helper so the obligation
/// and the credit can never diverge: *if a callee's postcondition is credited
/// at a call site — by ANY lane — every obligation that callee's instantiation
/// owes is owed at that same site*. The union is what makes that hold; either
/// half alone leaves a shape where credit is granted and nothing is owed:
///
/// * Keyed on `TyKind::FnDef` alone, a single
///   `let f: fn(&Cell<u8>) -> bool = conflate::<Cell<u8>>; f(c)` coercion —
///   inside ONE fully verified crate — credits `conflate`'s postcondition while
///   the gates see a `FnPtr` operand and owe nothing
///   (`cp_cell_generic_instantiation_fnptr`).
/// * Keyed on (1)+(2) alone, the same hole is one loop wider: (2) scans
///   only `body.basic_blocks[bb].statements`, so a fn pointer assigned BEFORE
///   a loop and called inside it is invisible to it, while the loop lanes
///   resolve it through (3) and assume the callee's postcondition. `fn evil(n:
///   u32) { let f: fn(D) -> u32 = make::<D>; while i < n { need7(f(D)) } }`
///   verifies with `D::drop` panicking on every iteration
///   (`s62v2_preloop_fnptr_credit_no_owe`).
///
/// (3) never guesses — every local on the way must have exactly one assignment
/// in the whole body and must never be mutably or raw-borrowed — so adding it
/// only ever resolves MORE sites, and a resolved site can only gain a `false`
/// obligation. Widening it is monotone in the safe direction.
///
/// `None` means no chain pins the target down (a fn-pointer parameter, a `dyn`
/// vtable, a reassigned local). Every lane reaches `None` too and credits no
/// contract there, so no obligation is owed for a credit that is not granted.
///
/// [`resolve_call_fn_def`]: super::call_resolve_util::resolve_call_fn_def
/// [`resolve_unique_call_fn_def`]: super::call_resolve_util::resolve_unique_call_fn_def
/// [`resolve_obligation_callee`]: super::call_resolve_util::resolve_obligation_callee
fn resolved_callee<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    bb: rustc_middle::mir::BasicBlock,
    func: &Operand<'tcx>,
) -> Option<(DefId, rustc_middle::ty::GenericArgs<'tcx>)> {
    super::call_resolve_util::resolve_obligation_callee(tcx, body, bb, func)
}

/// `false` for a call to a LOCAL generic function (or method of a local
/// generic impl/trait) that instantiates one of its type parameters at a type
/// exposing interior mutability ([`ty_exposes_interior_mutability`]): a
/// `T = Cell<u8>`, a closure capturing `&Cell` for `F: Fn`, `T = &Cell`.
///
/// The callee was verified for an arbitrary `T` under the model that shared
/// access to a `T` never changes its logical value (the structural generic
/// rule of the `!Freeze` write lane), so its contract says nothing about such
/// an instantiation: `conflate<T: Rd>(t: &T)` proves `rd() == rd()` around
/// `wr()`. Foreign callees (std, creusot_std) are value-model specifications
/// and are not affected. Fail closed.
///
/// The callee is resolved by [`resolved_callee`], which follows a fn-POINTER
/// local to the `FnDef` it can only hold, exactly as spec resolution does
/// before crediting that callee's postcondition. `go(c: &Cell<u8>) -> bool {
/// let f: fn(&Cell<u8>) -> bool = conflate::<Cell<u8>>; f(c) }` therefore owes
/// the same `false` the direct call owes; matched on `TyKind::FnDef` alone,
/// that one coercion lets a program returning `false` for every cell verify
/// under `#[ensures(result == true)]` (`cp_cell_generic_instantiation_fnptr`).
///
/// [`ty_exposes_interior_mutability`]: super::closure::ty_exposes_interior_mutability
pub(super) fn call_interior_instantiation_obligation<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    body: &rustc_middle::mir::Body<'tcx>,
    bb: rustc_middle::mir::BasicBlock,
    func: &Operand<'tcx>,
) -> Option<PureExpr> {
    let (def_id, generic_args) = resolved_callee(tcx, body, bb, func)?;
    if !def_id.is_local() {
        return None;
    }
    let typing_env = body.typing_env(tcx);
    let exposes_interior_mutability = generic_args
        .types()
        .any(|ty| super::closure::ty_exposes_interior_mutability(tcx, typing_env, ty));
    exposes_interior_mutability.then(|| fail_closed_marker("interior-mutable-generic-arg"))
}

/// core/alloc/std callees that never drop a value of their type arguments:
/// they only read, move values in or out (returning what they remove), or
/// build references. Keyed by (owner, item): the owner is the `Self` ADT of
/// an inherent impl (`slice` for `[T]`), the trait of a trait method or trait
/// impl method, or the parent module of a free function.
///
/// A TRAIT-keyed entry claims the property for EVERY impl of that trait in
/// core/alloc/std, because the key cannot see the impl's `Self` type. So an
/// entry may only name a trait method that no sysroot impl implements by
/// dropping. `("Iterator", &["next"])` does not clear that bar: `Skip::next`
/// drops the elements it skips and `Filter::next` drops the elements the
/// predicate rejects, both inside core, so `it.skip(1).next()` over a type
/// with an unchecked user `Drop` runs that destructor at a call site that
/// would claim nothing is dropped. `("DoubleEndedIterator", &["next_back"])`
/// has the identical defect (`Skip::next_back`, `Filter::next_back`).
///
/// Completeness cost: `Iterator::next` / `next_back` at a type argument whose
/// drop glue runs an unchecked user `Drop::drop` owes `false` — including for
/// `slice::Iter::next`, which genuinely never drops. No Creusot should_succeed
/// test is affected (the corpus contains no `impl Drop` at all), and the
/// obligation is unreachable for any program without such a destructor.
/// Narrowing that cost would take a Self-type key, not a trait key.
///
/// Two classes of the remaining trait keys clear the bar by SIGNATURE, which
/// is stronger than an impl-by-impl survey:
/// `Deref`/`DerefMut`/`Index`/`IndexMut`/`Borrow`/`BorrowMut`/`AsRef`/`AsMut`
/// take `&self` (or `&mut self`) and return a reference derived from it, and
/// `PartialEq::eq`/`ne`, `PartialOrd`, `Ord::cmp` take two shared references
/// and return a scalar: no impl can consume a value of a type argument
/// because no impl is given one. `Clone::clone` takes `&self` and returns a
/// fresh value; `IntoIterator::into_iter` takes `self` by value but every
/// core/alloc/std impl moves the receiver's contents into the returned
/// iterator rather than dropping them.
///
/// The residual risk in that argument is a `&self` method that drops
/// something it reaches through interior mutability, and `core::cell::LazyCell`
/// is exactly that: `<LazyCell<T, F> as Deref>::deref` forces the cell, which
/// CALLS the stored `F` and drops it. Neither probe shape below reaches it as
/// a false accept, because the surrounding obligations fire first:
/// constructing the cell in the body (`LazyCell::new(move || { let _ = d;
/// 7u8 })`, then `*l`, then `mem::forget(l)`, with `D: Drop` panicking) fails
/// even under `#[ensures(true)]` — `LazyCell::new` is not on this list and
/// its type argument is the capturing closure, so a `false` obligation is
/// live; taking the cell as a parameter (`h(l: &LazyCell<u8, Box<dyn FnOnce()
/// -> u8>>) -> u8 { **l }`, no construction in the body, so `deref` is the
/// only call that can drop) also fails under `#[ensures(true)]`. Those two
/// shapes certify only themselves: no live defect is demonstrated for any
/// remaining key, and none is removed. Removing a key is a pure narrowing and
/// stays available, but it costs completeness, so it is paid for by a shape
/// that ACCEPTS wrongly, not by the signature survey alone.
///
/// Every argument above is about a core/alloc/std body. A call site asks
/// [`call_never_drops_type_args`], which reads this list for the impl the call
/// enters, never for a trait method's declaration.
pub(super) fn std_callee_never_drops_type_args(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    def_id: DefId,
) -> bool {
    use rustc_hir::def::DefKind;
    if def_id.is_local()
        || !matches!(
            tcx.crate_name(def_id.krate).as_str(),
            "core" | "alloc" | "std"
        )
    {
        return false;
    }
    let item = tcx.item_name(def_id);
    let Some(parent) = tcx.opt_parent(def_id) else {
        return false;
    };
    let owner = match tcx.def_kind(parent) {
        DefKind::Trait => tcx.item_name(parent),
        DefKind::Impl { of_trait: true } => match tcx.impl_opt_trait_id(parent) {
            Some(trait_id) => tcx.item_name(trait_id),
            None => return false,
        },
        DefKind::Impl { of_trait: false } => {
            match tcx
                .type_of(parent)
                .instantiate_identity()
                .skip_norm_wip()
                .kind()
            {
                rustc_middle::ty::TyKind::Adt(adt, _) => tcx.item_name(adt.did()),
                rustc_middle::ty::TyKind::Slice(_) => rustc_span::Symbol::intern("slice"),
                _ => return false,
            }
        }
        DefKind::Mod => tcx.item_name(parent),
        _ => return false,
    };
    const NEVER_DROPS: &[(&str, &[&str])] = &[
        (
            "Vec",
            &[
                "new",
                "with_capacity",
                "push",
                "pop",
                "insert",
                "remove",
                "swap_remove",
                "len",
                "is_empty",
                "capacity",
                "reserve",
                "reserve_exact",
                "as_slice",
                "as_mut_slice",
                "split_off",
                "append",
            ],
        ),
        (
            "slice",
            &[
                "len",
                "is_empty",
                "get",
                "get_mut",
                "first",
                "last",
                "first_mut",
                "last_mut",
                "iter",
                "iter_mut",
                "swap",
                "reverse",
                "split_at",
                "split_at_mut",
            ],
        ),
        (
            "VecDeque",
            &[
                "new",
                "with_capacity",
                "push_back",
                "push_front",
                "pop_back",
                "pop_front",
                "len",
                "is_empty",
                "get",
                "get_mut",
                "front",
                "back",
                "iter",
                "iter_mut",
                "insert",
                "remove",
            ],
        ),
        (
            "Option",
            &[
                "take",
                "replace",
                "is_some",
                "is_none",
                "as_ref",
                "as_mut",
                "as_deref",
                "as_deref_mut",
                "iter",
                "iter_mut",
            ],
        ),
        ("Box", &["new"]),
        ("Rc", &["new", "clone"]),
        ("Arc", &["new", "clone"]),
        ("Cell", &["new", "replace", "get"]),
        (
            "mem",
            &[
                "replace",
                "swap",
                "take",
                "forget",
                "size_of",
                "size_of_val",
                "align_of",
            ],
        ),
        ("Deref", &["deref"]),
        ("DerefMut", &["deref_mut"]),
        ("Index", &["index"]),
        ("IndexMut", &["index_mut"]),
        ("Borrow", &["borrow"]),
        ("BorrowMut", &["borrow_mut"]),
        ("AsRef", &["as_ref"]),
        ("AsMut", &["as_mut"]),
        ("PartialEq", &["eq", "ne"]),
        ("PartialOrd", &["partial_cmp", "lt", "le", "gt", "ge"]),
        ("Ord", &["cmp"]),
        ("Clone", &["clone"]),
        ("IntoIterator", &["into_iter"]),
    ];
    NEVER_DROPS.iter().any(|(listed_owner, items)| {
        owner.as_str() == *listed_owner && items.contains(&item.as_str())
    })
}

/// Whether the body a call of `callee` at `args` enters is a standard-library
/// function known never to drop a value of its type arguments
/// ([`std_callee_never_drops_type_args`]).
///
/// The list keys a trait method by its trait's name, and the operand of a
/// trait-method call names the trait's declaration in `core` whoever
/// implements it. A USER impl of a listed method runs user code: its
/// `into_iter(self)` may drop `self`, its `index(&self, i)` may drop the
/// index it was handed, and its `deref_mut` may drop what `self` holds in
/// place (drop_glue_user_into_iter_impl_read_as_std_pinned.rs). So a trait
/// method is asked of the implementation rustc resolves it to in the host's
/// environment, and one the environment cannot name (a type parameter's, a
/// `dyn` receiver's) is not on the list.
pub(super) fn call_never_drops_type_args<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    callee: DefId,
    args: rustc_middle::ty::GenericArgs<'tcx>,
) -> bool {
    use rustc_middle::ty::{Instance, InstanceKind, TypeVisitableExt, TypingEnv};
    let declared_by_trait = matches!(
        tcx.opt_associated_item(callee).map(|assoc| assoc.container),
        Some(rustc_middle::ty::AssocContainer::Trait)
    );
    if !declared_by_trait {
        return std_callee_never_drops_type_args(tcx, callee);
    }
    // Resolution normalizes, and an unnormalizable projection can ICE; such
    // a call is answered as off the list.
    if args.has_aliases() || args.has_escaping_bound_vars() {
        return false;
    }
    let args = tcx.erase_and_anonymize_regions(args);
    let typing_env = TypingEnv::post_analysis(tcx, body.source.def_id());
    match Instance::try_resolve(tcx, typing_env, callee, args) {
        Ok(Some(Instance {
            def: InstanceKind::Item(resolved),
            ..
        })) => std_callee_never_drops_type_args(tcx, resolved),
        _ => false,
    }
}

fn drop_glue_runs_unchecked_user_drop<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    typing_env: rustc_middle::ty::TypingEnv<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
    user_specs: &std::collections::HashMap<rustc_hir::def_id::DefId, trust_wp_driver::StdSpec>,
    visited: &mut std::collections::HashSet<rustc_middle::ty::Ty<'tcx>>,
    depth: usize,
) -> bool {
    use rustc_middle::ty::TyKind;
    if !ty.needs_drop(tcx, typing_env) || !visited.insert(ty) {
        return false;
    }
    if depth > 64 {
        return true;
    }
    let recurse = |t: rustc_middle::ty::Ty<'tcx>, visited: &mut std::collections::HashSet<_>| {
        drop_glue_runs_unchecked_user_drop(tcx, typing_env, t, user_specs, visited, depth + 1)
    };
    match ty.kind() {
        TyKind::Adt(adt, args) => {
            if matches!(
                tcx.crate_name(adt.did().krate).as_str(),
                "core" | "alloc" | "std"
            ) {
                // A std type drops the values of its type arguments.
                return args.types().any(|arg| recurse(arg, visited));
            }
            if let Some(dtor) = tcx.adt_destructor(adt.did()) {
                if dtor.did.is_local() {
                    let checked = user_specs.get(&dtor.did).is_some_and(|spec| {
                        spec.requires.iter().all(|clause| clause.trim() == "true")
                    });
                    if !checked {
                        return true;
                    }
                } else {
                    let krate = tcx.crate_name(dtor.did.krate);
                    if !matches!(krate.as_str(), "core" | "alloc" | "std") {
                        return true;
                    }
                    // A std container drops the values of its type arguments.
                    for arg in args.types() {
                        if recurse(arg, visited) {
                            return true;
                        }
                    }
                }
            }
            for field in adt.all_fields() {
                if recurse(field.ty(tcx, *args).skip_norm_wip(), visited) {
                    return true;
                }
            }
            false
        }
        TyKind::Tuple(tys) => tys.iter().any(|t| recurse(t, visited)),
        TyKind::Array(elem, _) | TyKind::Slice(elem) => recurse(*elem, visited),
        TyKind::Closure(_, args) => args
            .as_closure()
            .upvar_tys()
            .iter()
            .any(|t| recurse(t, visited)),
        // Glue not decidable at this site (see the function doc).
        _ => false,
    }
}

pub(super) fn assert_fact_from_condition<'tcx>(
    cond: &Operand<'tcx>,
    expected: bool,
    msg: &AssertKind<Operand<'tcx>>,
    local_exprs: &impl ExprLookup,
) -> Option<PureExpr> {
    // Shift-overflow asserts guard exactly the `0 <= amount < BITS` range
    // that the shift lowering emits as a PROOF obligation (the
    // `__trust_wp_shift_amount_in_range_{bits}` marker, ledger
    // int-shift-full). Assuming the assert condition here would inject the
    // very fact under proof into the VC context — for an over-wide shift the
    // "fact" is false (e.g. `8 < 8` for `1u8 >> 8`), which makes the whole
    // context inconsistent and every obligation, including the shift-range
    // obligation itself, pass vacuously. Skip the fact: the range knowledge
    // is re-derivable from the proved obligation, so downstream reasoning
    // loses nothing that was soundly available.
    if matches!(msg, AssertKind::Overflow(MirBinOp::Shl | MirBinOp::Shr, ..)) {
        return None;
    }
    // Arithmetic panic asserts (checked `+ - *`, signed `MIN / -1`, signed
    // negation, division/remainder by zero) are PROVED through
    // `arithmetic_panic_obligation`, which the extractors push as side
    // obligations. Those obligations are merged into the postcondition goal
    // and checked against the extracted body, so assuming the assert
    // condition here would put the very fact under proof into its own
    // context and discharge it vacuously (otherwise `#[ensures(true)] fn
    // f(a: u32, b: u32) -> u32 { a / b }` verifies). Skip the fact.
    if is_arithmetic_panic_assert(msg) {
        return None;
    }
    // A bounds check is a PROOF obligation (`bounds_check_obligation`). Its
    // condition is not re-assumed for the continuation: ay hoists a
    // result-position `LetAssume` into the unconditional premise set, which
    // would make the obligation circular.
    if matches!(msg, AssertKind::BoundsCheck { .. }) {
        return None;
    }
    translate_operand(cond, local_exprs).map(|cond_expr| {
        if expected {
            cond_expr
        } else {
            PureExpr::UnOp(UnOp::Not, Arc::new(cond_expr))
        }
    })
}

/// Wrap a continuation with an assert fact as `LetAssume`.
///
/// When continuation extraction fails (`None`) but the assert condition was
/// translated successfully, we still push the fact into the explicit
/// `CallEffects` so it constrains downstream verification context.
pub(super) fn wrap_continuation_with_assert_fact(
    assert_fact: Option<PureExpr>,
    continuation: Option<PureExpr>,
    effects: &mut CallEffects,
) -> Option<PureExpr> {
    match (assert_fact, continuation) {
        (Some(fact), Some(body)) => Some(PureExpr::LetAssume {
            assumption: Arc::new(fact),
            body: Arc::new(body),
        }),
        (Some(fact), None) => {
            effects.assumptions.push(fact);
            None
        }
        (None, continuation) => continuation,
    }
}

pub(super) fn wrap_spanned_continuation_with_assert_fact(
    assert_fact: Option<PureExpr>,
    continuation: Option<SpannedBodyExpr>,
) -> Option<SpannedBodyExpr> {
    match assert_fact {
        Some(fact) => continuation.map(|mut spanned| {
            spanned.expr = PureExpr::LetAssume {
                assumption: Arc::new(fact),
                body: Arc::new(spanned.expr),
            };
            spanned
        }),
        None => continuation,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bool_var(name: &str) -> PureExpr {
        PureExpr::Var(
            name.to_string(),
            Some(trust_wp_core::formula::ExprSort::Bool),
        )
    }

    // --- wrap_continuation_with_assert_fact ---

    #[test]
    fn test_wrap_both_some_creates_let_assume() {
        let fact = bool_var("cond");
        let body = PureExpr::Int(42);
        let mut effects = CallEffects::new();

        let result = wrap_continuation_with_assert_fact(
            Some(fact.clone()),
            Some(body.clone()),
            &mut effects,
        );

        match result {
            Some(PureExpr::LetAssume {
                assumption,
                body: inner,
            }) => {
                assert_eq!(*assumption, fact);
                assert_eq!(*inner, body);
            }
            other => panic!("expected LetAssume, got {other:?}"),
        }
        // No side effects on CallEffects
        assert!(effects.assumptions.is_empty());
    }

    #[test]
    fn test_wrap_fact_some_continuation_none_pushes_to_effects() {
        let fact = bool_var("precondition");
        let mut effects = CallEffects::new();

        let result = wrap_continuation_with_assert_fact(Some(fact.clone()), None, &mut effects);

        assert!(result.is_none());
        assert_eq!(effects.assumptions.len(), 1);
        assert_eq!(effects.assumptions[0], fact);
    }

    #[test]
    fn test_wrap_fact_none_returns_continuation_unchanged() {
        let body = PureExpr::Int(7);
        let mut effects = CallEffects::new();

        let result = wrap_continuation_with_assert_fact(None, Some(body.clone()), &mut effects);

        assert_eq!(result, Some(body));
        assert!(effects.assumptions.is_empty());
    }

    #[test]
    fn test_wrap_both_none_returns_none() {
        let mut effects = CallEffects::new();

        let result = wrap_continuation_with_assert_fact(None, None, &mut effects);

        assert!(result.is_none());
        assert!(effects.assumptions.is_empty());
    }

    #[test]
    fn test_wrap_accumulates_multiple_facts() {
        let mut effects = CallEffects::new();

        // First call: fact without continuation pushes to effects
        wrap_continuation_with_assert_fact(Some(bool_var("a")), None, &mut effects);
        wrap_continuation_with_assert_fact(Some(bool_var("b")), None, &mut effects);

        assert_eq!(effects.assumptions.len(), 2);
        assert_eq!(effects.assumptions[0], bool_var("a"));
        assert_eq!(effects.assumptions[1], bool_var("b"));
    }

    /// A dummy operand: `AssertKind` carries operands only for the panic
    /// message, and `is_arithmetic_panic_assert` never inspects them.
    fn dummy_operand<'tcx>() -> Operand<'tcx> {
        Operand::Copy(rustc_middle::mir::Place::from(
            rustc_middle::mir::Local::from_u32(1),
        ))
    }

    /// A MIR `Assert(DivisionByZero)` / `Assert(RemainderByZero)` is an
    /// ARITHMETIC panic site.
    ///
    /// Two structural checks key on `is_charged_assert`, which contains this
    /// predicate, in opposite directions, so the class must never fall out of
    /// it:
    /// - `unwalked_charged_assert_sites` demotes a `verified` verdict when
    ///   a reachable site of this class had no obligation stated for it;
    /// - `unchecked_panic_sites` exempts this class from the "panic site no
    ///   lane discharges" cap, *because* the obligation lane owns it.
    ///
    /// Dropping `DivisionByZero` from the predicate would move every division
    /// out of the obligation lane and into the cap — never into a silent
    /// accept — but it would also silently stop `arithmetic_panic_obligation`
    /// from owing `divisor != 0`, which is the defect
    /// `should_fail_div_zero_discarded` gates end to end.
    #[test]
    fn division_and_remainder_by_zero_are_arithmetic_panic_sites() {
        assert!(is_arithmetic_panic_assert(&AssertKind::DivisionByZero(
            dummy_operand()
        )));
        assert!(is_arithmetic_panic_assert(&AssertKind::RemainderByZero(
            dummy_operand()
        )));
        // A bounds check is NOT an arithmetic site: its goal is owed by
        // `bounds_check_obligation`, never by `arithmetic_panic_obligation`.
        assert!(!is_arithmetic_panic_assert(&AssertKind::BoundsCheck {
            len: dummy_operand(),
            index: dummy_operand(),
        }));
    }

    /// Both charged classes are under the structural coverage check and out
    /// of the clause-free cap; an assert kind no lane charges is neither.
    #[test]
    fn bounds_checks_and_arithmetic_asserts_are_charged_other_kinds_are_not() {
        assert!(is_charged_assert(&AssertKind::BoundsCheck {
            len: dummy_operand(),
            index: dummy_operand(),
        }));
        assert!(is_charged_assert(&AssertKind::DivisionByZero(
            dummy_operand()
        )));
        assert!(!is_charged_assert(&AssertKind::ResumedAfterReturn(
            rustc_hir::CoroutineKind::Coroutine(rustc_hir::Movability::Movable)
        )));
    }
}
