// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! MIR Operand translation helpers.

use rustc_middle::{
    mir::{Body, Operand, Place, ProjectionElem},
    ty::TyKind,
};
use trust_wp_core::formula::PureExpr;

use super::{
    constant::{translate_constant, translate_constant_with_tcx},
    discriminant::translate_ty_const_to_expr,
    place::{translate_place, translate_place_detailed},
    ExprLookup, TranslationDiagContext,
};

/// Translate a MIR Operand to a PureExpr (compatibility shim).
pub(crate) fn translate_operand(
    operand: &Operand<'_>,
    locals: &impl ExprLookup,
) -> Option<PureExpr> {
    translate_operand_detailed(operand, locals, None)
}

/// Translate a MIR Operand to a PureExpr, recording diagnostics for failures.
pub(crate) fn translate_operand_detailed(
    operand: &Operand<'_>,
    locals: &impl ExprLookup,
    diag: Option<&TranslationDiagContext<'_>>,
) -> Option<PureExpr> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            translate_place_detailed(place, locals, diag)
        }
        Operand::Constant(constant) => translate_constant(constant),
        // RuntimeChecks is a compiler runtime-check flag (UbChecks/
        // ContractChecks/OverflowChecks) with no place/local/ghost value.
        // Like a constant we cannot translate, it yields no PureExpr.
        Operand::RuntimeChecks(_) => None,
    }
}

/// Translate a MIR Operand with `TyCtxt` fallback for unevaluated constants.
///
/// Like `translate_operand`, but when `translate_constant` fails on a
/// `Const::Unevaluated` (e.g., promoted references to compound types),
/// falls back to `translate_constant_with_tcx` which can resolve them
/// via `const_eval_resolve_for_typeck`. (#1572 Cause B)
pub(crate) fn translate_operand_with_tcx<'tcx>(
    operand: &Operand<'tcx>,
    locals: &impl ExprLookup,
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
) -> Option<PureExpr> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => translate_place(place, locals),
        Operand::Constant(constant) => {
            translate_constant(constant).or_else(|| translate_constant_with_tcx(constant, tcx))
        }
        // RuntimeChecks is a compiler runtime-check flag with no
        // place/local/ghost value; like an untranslatable constant it
        // yields no PureExpr.
        Operand::RuntimeChecks(_) => None,
    }
}

pub(crate) fn operand_is_bool(operand: &Operand<'_>, body: &Body<'_>) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place_is_bool(place, body),
        Operand::Constant(constant) => matches!(constant.ty().kind(), TyKind::Bool),
        // RuntimeChecks carries no inspectable type; conservatively treat it
        // as not-bool (mirrors the Constant arm's type test failing).
        Operand::RuntimeChecks(_) => false,
    }
}

/// True iff the operand's type is a SIGNED machine integer (`i8..i128`/`isize`).
///
/// Used to lower Rust's signed `%` (which TRUNCATES toward zero, with the
/// remainder taking the sign of the dividend) to `BinOp::RemTrunc`. Unsigned
/// `%` keeps Euclidean `BinOp::Mod` (== truncated for non-negative operands)
/// and, crucially, matches the contract `%` which remains Euclidean (trust-wp's
/// wrapping arithmetic specs reduce a possibly-negative dividend modulo `2^n`
/// and depend on the non-negative Euclidean remainder). Only projection-less
/// places and constants are inspected; anything else stays Euclidean. See
/// `trust-wp-divmod-semantics`.
pub(crate) fn operand_is_signed_int(operand: &Operand<'_>, body: &Body<'_>) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            if !place.projection.is_empty() {
                return false;
            }
            matches!(body.local_decls[place.local].ty.kind(), TyKind::Int(_))
        }
        Operand::Constant(constant) => matches!(constant.ty().kind(), TyKind::Int(_)),
        Operand::RuntimeChecks(_) => false,
    }
}

/// True iff the operand's type is a machine integer — SIGNED (`i8..i128`/
/// `isize`) or UNSIGNED (`u8..u128`/`usize`).
///
/// Used to lower Rust's `/` to the truncated operator `BinOp::DivTrunc`. Both
/// Rust's machine `/` AND Creusot's `Int` `/` operator are
/// `int.ComputerDivision.div` (truncation toward zero), so the body model must
/// be truncated to agree with the parsed contract (which lowers `/` to
/// `DivTrunc`). For unsigned operands truncation coincides with Euclidean
/// (operands are non-negative), so the value is unchanged; using the same
/// truncated UF keeps the body and contract division terms identical, letting
/// `result@ == l@ / r@` discharge reflexively. The no-body / projected-place
/// case is conservative (stays `Div`): only projection-less places and
/// constants are inspected, which covers the common `a / b` operand shapes.
/// Floats are excluded (they keep exact `Div`). See `trust-wp-divmod-semantics`.
pub(crate) fn operand_is_machine_int(operand: &Operand<'_>, body: &Body<'_>) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            if !place.projection.is_empty() {
                return false;
            }
            matches!(
                body.local_decls[place.local].ty.kind(),
                TyKind::Int(_) | TyKind::Uint(_)
            )
        }
        Operand::Constant(constant) => {
            matches!(constant.ty().kind(), TyKind::Int(_) | TyKind::Uint(_))
        }
        Operand::RuntimeChecks(_) => false,
    }
}

fn place_is_bool(place: &Place<'_>, body: &Body<'_>) -> bool {
    if !place.projection.is_empty() {
        if place.projection.len() == 1 {
            if let Some(ProjectionElem::Field(field, _)) = place.projection.first() {
                if field.as_u32() == 0 {
                    return match body.local_decls[place.local].ty.kind() {
                        TyKind::Tuple(fields) => fields
                            .first()
                            .is_some_and(|ty| matches!(ty.kind(), TyKind::Bool)),
                        _ => false,
                    };
                }
            }
        }
        return false;
    }
    matches!(body.local_decls[place.local].ty.kind(), TyKind::Bool)
}

/// Check whether a PtrMetadata operand carries slice/array/str metadata (length)
/// rather than trait-object metadata (vtable pointer). (#952)
///
/// Returns `true` for `&[T]`, `&mut [T]`, `&str`, arrays, and raw pointer
/// equivalents. Returns `false` for `&dyn Trait` and anything else.
pub(super) fn operand_is_slice_ptr_metadata(operand: &Operand<'_>, body: &Body<'_>) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => {
            is_slice_like_ty_kind(body.local_decls[place.local].ty.peel_refs().kind())
        }
        // Constants are unlikely to be PtrMetadata operands, but check anyway.
        Operand::Constant(constant) => is_slice_like_ty_kind(constant.ty().peel_refs().kind()),
        // RuntimeChecks carries no inspectable type; fail closed (not slice-like).
        Operand::RuntimeChecks(_) => false,
    }
}

/// Translate the type-level length for array PtrMetadata operands.
///
/// For operands whose dereferenced type is `[T; N]`, this returns `N` as a
/// `PureExpr` (integer literal when evaluable, symbolic var for const params).
/// Returns `None` for non-array operands.
pub(super) fn operand_array_len_expr<'tcx>(
    operand: &Operand<'tcx>,
    body: &Body<'tcx>,
) -> Option<PureExpr> {
    let ty = match operand {
        Operand::Copy(place) | Operand::Move(place) => body.local_decls[place.local].ty.peel_refs(),
        Operand::Constant(constant) => constant.ty().peel_refs(),
        // RuntimeChecks carries no inspectable type; it is never an array.
        Operand::RuntimeChecks(_) => return None,
    };
    match ty.kind() {
        TyKind::Array(_, len_const) => translate_ty_const_to_expr(*len_const),
        _ => None,
    }
}

/// Returns `true` if the `TyKind` (after peeling refs) is a slice, array, str,
/// or raw pointer to one of those — types whose PtrMetadata is a length.
fn is_slice_like_ty_kind(kind: &TyKind<'_>) -> bool {
    match kind {
        TyKind::Slice(_) | TyKind::Array(_, _) | TyKind::Str => true,
        TyKind::RawPtr(inner, _) => matches!(
            inner.kind(),
            TyKind::Slice(_) | TyKind::Array(_, _) | TyKind::Str
        ),
        _ => false,
    }
}
