// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Float literal helpers for MIR constant translation.

use rustc_middle::ty::FloatTy;
use trust_wp_core::formula::{BinOp, FloatBits, PureExpr, UnOp};

fn concrete_float_expr_f32(value: f32) -> PureExpr {
    PureExpr::Float(FloatBits::from_f32(value))
}

pub(super) fn concrete_float_expr_f64(value: f64) -> PureExpr {
    PureExpr::Float(FloatBits::from_f64(value))
}

/// Decode a float value from a first-class `PureExpr::Float`.
fn decode_concrete_float_f64(expr: &PureExpr) -> Option<f64> {
    match expr {
        PureExpr::Float(bits) => Some(bits.to_f64()),
        _ => None,
    }
}

pub(super) fn translate_float_scalar_bits(float_ty: FloatTy, bits: u128) -> Option<PureExpr> {
    match float_ty {
        FloatTy::F32 => u32::try_from(bits)
            .ok()
            .map(|raw| concrete_float_expr_f32(f32::from_bits(raw))),
        FloatTy::F64 => u64::try_from(bits)
            .ok()
            .map(|raw| concrete_float_expr_f64(f64::from_bits(raw))),
        FloatTy::F16 | FloatTy::F128 => None,
    }
}

pub(super) fn fold_concrete_float_unop(op: UnOp, operand: &PureExpr) -> Option<PureExpr> {
    let value = decode_concrete_float_f64(operand)?;
    match op {
        UnOp::Neg => Some(concrete_float_expr_f64(-value)),
        _ => None,
    }
}

#[allow(clippy::float_cmp)] // Exact IEEE comparison is the behavior being mirrored.
pub(super) fn fold_concrete_float_binop(
    left: &PureExpr,
    op: BinOp,
    right: &PureExpr,
) -> Option<PureExpr> {
    let l = decode_concrete_float_f64(left)?;
    let r = decode_concrete_float_f64(right)?;
    let result = match op {
        BinOp::Eq => Some(l == r),
        BinOp::Ne => Some(l != r),
        BinOp::Lt => Some(l < r),
        BinOp::Le => Some(l <= r),
        BinOp::Gt => Some(l > r),
        BinOp::Ge => Some(l >= r),
        _ => None,
    }?;
    Some(PureExpr::Bool(result))
}
