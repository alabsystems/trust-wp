// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Discriminant and integer-type helpers for MIR translation.

use rustc_middle::{
    mir::{Body, Operand, Place, ProjectionElem},
    ty::TyKind,
};
use trust_wp_core::formula::{ExprSort, PureExpr};

use super::{
    binop::{int_ty_bits, uint_ty_bits},
    constant::{large_signed_to_expr, large_unsigned_to_expr},
};

/// Extract a usize value from a `ty::Const` (used for array repeat counts).
/// Returns `Some(count as i64)` if the const evaluates to a usize literal,
/// `None` otherwise. (#948)
pub(super) fn translate_ty_const_to_usize(c: rustc_middle::ty::Const<'_>) -> Option<i64> {
    let value = c.try_to_value()?;
    let scalar_int = value
        .try_to_scalar()
        .and_then(|s| s.try_to_scalar_int().ok())?;
    let val = scalar_int.to_uint(scalar_int.size());
    // Repeat counts are usize — they must fit in i64 for PureExpr::Int
    i64::try_from(val).ok()
}

/// Extract a symbolic or concrete integer expression from a type-level const.
///
/// Supports:
/// - concrete evaluable constants (e.g., `5`, `FOO + 1`) -> `PureExpr::Int`
/// - const generic params (e.g., `N`) -> `PureExpr::Var("N")`
pub(super) fn translate_ty_const_to_expr(c: rustc_middle::ty::Const<'_>) -> Option<PureExpr> {
    if let Some(value) = translate_ty_const_to_usize(c) {
        return Some(PureExpr::Int(value));
    }
    match c.kind() {
        rustc_middle::ty::ConstKind::Param(param) => Some(PureExpr::Var(
            param.name.as_str().to_string(),
            Some(ExprSort::Int),
        )),
        _ => None,
    }
}

#[derive(Clone, Copy)]
pub(crate) struct DiscrIntTy {
    pub(crate) signed: bool,
    pub(crate) bits: u32,
}

pub(crate) fn operand_int_ty(operand: &Operand<'_>, body: &Body<'_>) -> Option<DiscrIntTy> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place_int_ty(place, body),
        Operand::Constant(constant) => match constant.ty().kind() {
            TyKind::Int(int_ty) => Some(DiscrIntTy {
                signed: true,
                bits: int_ty_bits(*int_ty),
            }),
            TyKind::Uint(uint_ty) => Some(DiscrIntTy {
                signed: false,
                bits: uint_ty_bits(*uint_ty),
            }),
            _ => None,
        },
        // RuntimeChecks carries no inspectable type; treat as non-integer
        // (mirrors the Constant arm's type test falling through to None).
        Operand::RuntimeChecks(_) => None,
    }
}

fn place_int_ty(place: &Place<'_>, body: &Body<'_>) -> Option<DiscrIntTy> {
    if !place.projection.is_empty() {
        if place.projection.len() == 1 {
            if let Some(ProjectionElem::Field(field, _)) = place.projection.first() {
                if field.as_u32() == 0 {
                    if let TyKind::Tuple(fields) = body.local_decls[place.local].ty.kind() {
                        if let Some(first_ty) = fields.first() {
                            return match first_ty.kind() {
                                TyKind::Int(int_ty) => Some(DiscrIntTy {
                                    signed: true,
                                    bits: int_ty_bits(*int_ty),
                                }),
                                TyKind::Uint(uint_ty) => Some(DiscrIntTy {
                                    signed: false,
                                    bits: uint_ty_bits(*uint_ty),
                                }),
                                _ => None,
                            };
                        }
                    }
                }
            }
        }
        return None;
    }

    match body.local_decls[place.local].ty.kind() {
        TyKind::Int(int_ty) => Some(DiscrIntTy {
            signed: true,
            bits: int_ty_bits(*int_ty),
        }),
        TyKind::Uint(uint_ty) => Some(DiscrIntTy {
            signed: false,
            bits: uint_ty_bits(*uint_ty),
        }),
        _ => None,
    }
}

// Suppress pedantic warnings that don't affect correctness
#[allow(clippy::cast_possible_wrap)] // Deliberate u128->i128 casts for value conversion
#[allow(clippy::cast_possible_truncation)] // Deliberate i128->i64 casts (checked at runtime)
pub(crate) fn switch_value_to_i64(value: u128, discr_ty: DiscrIntTy) -> Option<i64> {
    let bits = discr_ty.bits;
    if bits == 0 || bits > 128 {
        return None;
    }
    let masked = if bits == 128 {
        value
    } else {
        value & ((1u128 << bits) - 1)
    };

    if discr_ty.signed {
        let signed_val = if bits == 128 {
            masked as i128
        } else {
            let sign_bit = 1u128 << (bits - 1);
            if masked & sign_bit != 0 {
                (masked as i128) - (1i128 << bits)
            } else {
                masked as i128
            }
        };
        if signed_val >= i128::from(i64::MIN) && signed_val <= i128::from(i64::MAX) {
            Some(signed_val as i64)
        } else {
            None
        }
    } else if masked <= i64::MAX as u128 {
        Some(masked as i64)
    } else {
        None
    }
}

/// Like [`switch_value_to_i64`] but always succeeds for in-range bit widths,
/// producing a value-exact `PureExpr` even when the (sign-extended) switch
/// value falls outside `i64` range (e.g. `i128::MIN`, `i128::MAX`, `u128::MAX`).
///
/// Small values still collapse to `PureExpr::Int` (via the constant
/// decomposers), so this is a strict superset of the old behavior: it never
/// changes the encoding of a value `switch_value_to_i64` could already handle,
/// it only stops dropping the out-of-`i64`-range guards. Reusing
/// `large_signed_to_expr`/`large_unsigned_to_expr` guarantees the guard's RHS
/// term is byte-for-byte identical to how the match-arm constant on the *value*
/// side is already encoded, so `discr == K` and `K` agree exactly.
///
/// Soundness: the masking + sign-extension below is identical to
/// `switch_value_to_i64`, and the decomposers are value-exact (round-tripped by
/// the `constant.rs` unit tests). Forming `discr == K` only *strengthens* the
/// path condition for that arm — it adds a fact that was previously silently
/// lost when the whole extraction aborted on `None`. It can never make a
/// genuinely-SAT (refutable) obligation appear UNSAT.
#[allow(clippy::cast_possible_wrap)]
pub(crate) fn switch_value_to_expr(value: u128, discr_ty: DiscrIntTy) -> Option<PureExpr> {
    let bits = discr_ty.bits;
    if bits == 0 || bits > 128 {
        return None;
    }
    let masked = if bits == 128 {
        value
    } else {
        value & ((1u128 << bits) - 1)
    };

    if discr_ty.signed {
        let signed_val = if bits == 128 {
            masked as i128
        } else {
            let sign_bit = 1u128 << (bits - 1);
            if masked & sign_bit != 0 {
                (masked as i128) - (1i128 << bits)
            } else {
                masked as i128
            }
        };
        Some(large_signed_to_expr(signed_val))
    } else {
        Some(large_unsigned_to_expr(masked))
    }
}
