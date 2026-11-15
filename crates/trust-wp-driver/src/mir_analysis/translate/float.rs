// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Rust's floats in MIR: literals, operators and `as` casts. An `f32`/`f64`
//! is translated to IEEE-754 values and the reserved `__trust_wp_ieee_*`
//! operations; an `f16`/`f128` to the reserved uninterpreted
//! `__trust_wp_opaque_float_*` functions of its operands
//! (`trust_wp_core::formula::ieee`). A float is never translated as a number:
//! an operator over a float operand is either its reserved call or refused.

use std::sync::Arc;

use rustc_middle::{
    mir::{BinOp as MirBinOp, Body, Operand, Place, ProjectionElem},
    ty::{FloatTy, Ty, TyKind},
};
use trust_wp_core::formula::{
    ieee::{IeeeFn, IeeeOp, OpaqueFloatFn, OpaqueFormat, OpaqueOp, OpaquePeer},
    ExprSort, FloatBits, FloatWidth, PureExpr, UnOp,
};

/// How an operand's type relates to the IEEE float model.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum FloatClass {
    /// Not a float type.
    NotFloat,
    /// `f32` or `f64`.
    Float(FloatWidth),
    /// `f16` or `f128`, which have no IEEE model: each operation is an
    /// uninterpreted function of its operands.
    Opaque(OpaqueFormat),
}

/// The sort of a value of a Rust float type.
pub(crate) fn float_ty_sort(float_ty: FloatTy) -> ExprSort {
    match float_ty {
        FloatTy::F32 => ExprSort::Float(FloatWidth::F32),
        FloatTy::F64 => ExprSort::Float(FloatWidth::F64),
        FloatTy::F16 => OpaqueFormat::F16.sort(),
        FloatTy::F128 => OpaqueFormat::F128.sort(),
    }
}

/// Classify a type.
pub(crate) fn float_class(ty: Ty<'_>) -> FloatClass {
    match ty.kind() {
        TyKind::Float(FloatTy::F32) => FloatClass::Float(FloatWidth::F32),
        TyKind::Float(FloatTy::F64) => FloatClass::Float(FloatWidth::F64),
        TyKind::Float(FloatTy::F16) => FloatClass::Opaque(OpaqueFormat::F16),
        TyKind::Float(FloatTy::F128) => FloatClass::Opaque(OpaqueFormat::F128),
        _ => FloatClass::NotFloat,
    }
}

/// The type of `place` from its local's declaration and the types MIR
/// projections carry. No `TyCtxt` is needed: a `Field` projection states its
/// type, `Deref` applies only to references, raw pointers and `Box`, and the
/// indexing projections only to arrays and slices.
fn place_ty<'tcx>(place: &Place<'tcx>, body: &Body<'tcx>) -> Option<Ty<'tcx>> {
    let mut ty = body.local_decls.get(place.local)?.ty;
    for elem in place.projection {
        ty = match elem {
            ProjectionElem::Field(_, field_ty) => field_ty,
            ProjectionElem::Deref => ty.builtin_deref(true)?,
            ProjectionElem::Index(_) | ProjectionElem::ConstantIndex { .. } => match ty.kind() {
                TyKind::Array(elem, _) | TyKind::Slice(elem) => *elem,
                _ => return None,
            },
            ProjectionElem::Subslice { .. } | ProjectionElem::Downcast(..) => ty,
            ProjectionElem::OpaqueCast(cast_ty) => cast_ty,
            _ => return None,
        };
    }
    Some(ty)
}

/// The type of a MIR operand (`None` when a projection is not typed above).
pub(crate) fn operand_ty<'tcx>(operand: &Operand<'tcx>, body: &Body<'tcx>) -> Option<Ty<'tcx>> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place_ty(place, body),
        Operand::Constant(constant) => Some(constant.ty()),
        Operand::RuntimeChecks(_) => None,
    }
}

/// Classify an operand; `None` when its type cannot be computed.
pub(crate) fn operand_float_class<'tcx>(
    operand: &Operand<'tcx>,
    body: &Body<'tcx>,
) -> Option<FloatClass> {
    operand_ty(operand, body).map(float_class)
}

/// True when `expr` is syntactically a float value: used where no MIR body is
/// available to type the operand, so that a float operator is refused rather
/// than read as an integer or logical one.
pub(crate) fn expr_is_syntactically_float(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Float(_) | PureExpr::Var(_, Some(ExprSort::Float(_))) => true,
        PureExpr::Var(_, Some(ExprSort::Datatype(id))) => {
            OpaqueFormat::from_sort_name(&trust_wp_core::formula::resolve_sort_name(*id)).is_some()
        }
        PureExpr::LogicFnCall { name, .. } => {
            IeeeFn::parse(name).is_some_and(|f| matches!(f.result_sort(), ExprSort::Float(_)))
                || OpaqueFloatFn::parse(name).is_some_and(OpaqueFloatFn::yields_float_value)
        }
        _ => false,
    }
}

pub(super) fn translate_float_scalar_bits(float_ty: FloatTy, bits: u128) -> Option<PureExpr> {
    match float_ty {
        FloatTy::F32 => u32::try_from(bits)
            .ok()
            .map(|raw| PureExpr::Float(FloatBits::from_f32(f32::from_bits(raw)))),
        FloatTy::F64 => u64::try_from(bits)
            .ok()
            .map(|raw| PureExpr::Float(FloatBits::from_f64(f64::from_bits(raw)))),
        // A function of the bit pattern: equal patterns are one value, and
        // nothing is claimed of distinct ones.
        FloatTy::F16 => u16::try_from(bits)
            .ok()
            .map(|raw| opaque_literal(OpaqueFormat::F16, u128::from(raw))),
        FloatTy::F128 => Some(opaque_literal(OpaqueFormat::F128, bits)),
    }
}

fn opaque_call(op: OpaqueOp, format: OpaqueFormat, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::LogicFnCall {
        name: OpaqueFloatFn::new(op, format).name(),
        args,
    }
}

fn opaque_literal(format: OpaqueFormat, bits: u128) -> PureExpr {
    use super::constant::large_unsigned_to_expr;
    opaque_call(
        OpaqueOp::Literal,
        format,
        vec![large_unsigned_to_expr(bits)],
    )
}

/// A MIR binary operator over two `format` floats, as the uninterpreted
/// function of its operands. `None` for an operator Rust does not define over
/// floats.
pub(super) fn translate_opaque_binop(
    op: MirBinOp,
    format: OpaqueFormat,
    left: PureExpr,
    right: PureExpr,
) -> Option<PureExpr> {
    let opaque_op = match op {
        MirBinOp::Add => OpaqueOp::Add,
        MirBinOp::Sub => OpaqueOp::Sub,
        MirBinOp::Mul => OpaqueOp::Mul,
        MirBinOp::Div => OpaqueOp::Div,
        MirBinOp::Rem => OpaqueOp::Rem,
        MirBinOp::Eq | MirBinOp::Ne => OpaqueOp::Eq,
        MirBinOp::Lt => OpaqueOp::Lt,
        MirBinOp::Le => OpaqueOp::Le,
        MirBinOp::Gt => OpaqueOp::Gt,
        MirBinOp::Ge => OpaqueOp::Ge,
        _ => return None,
    };
    let call = opaque_call(opaque_op, format, vec![left, right]);
    // IEEE `!=` is the negation of IEEE `==` in every binary format.
    Some(if matches!(op, MirBinOp::Ne) {
        PureExpr::UnOp(UnOp::Not, Arc::new(call))
    } else {
        call
    })
}

/// `-x` over a `format` float.
pub(super) fn translate_opaque_neg(format: OpaqueFormat, operand: PureExpr) -> PureExpr {
    opaque_call(OpaqueOp::Neg, format, vec![operand])
}

/// `x as T` where `x`'s type or `T` is an opaque format: `source` and
/// `target` are the two sides' classes. `None` unless one side is opaque and
/// the other a float or an integer (`int` is the integer side's signedness
/// and width).
pub(super) fn translate_opaque_cast(
    source: FloatClass,
    target: FloatClass,
    int: Option<(bool, u32)>,
    operand: PureExpr,
) -> Option<PureExpr> {
    let int_peer = || int.map(|(signed, bits)| OpaquePeer::Int { signed, bits });
    Some(match (source, target) {
        // A cast within one format changes nothing.
        (FloatClass::Opaque(from), FloatClass::Opaque(to)) if from == to => operand,
        (FloatClass::Opaque(from), FloatClass::Opaque(to)) => {
            opaque_call(OpaqueOp::To(OpaquePeer::Opaque(to)), from, vec![operand])
        }
        (FloatClass::Opaque(from), FloatClass::Float(width)) => {
            opaque_call(OpaqueOp::To(OpaquePeer::Float(width)), from, vec![operand])
        }
        (FloatClass::Opaque(from), FloatClass::NotFloat) => {
            opaque_call(OpaqueOp::To(int_peer()?), from, vec![operand])
        }
        (FloatClass::Float(width), FloatClass::Opaque(to)) => {
            opaque_call(OpaqueOp::From(OpaquePeer::Float(width)), to, vec![operand])
        }
        (FloatClass::NotFloat, FloatClass::Opaque(to)) => {
            opaque_call(OpaqueOp::From(int_peer()?), to, vec![operand])
        }
        _ => return None,
    })
}

fn ieee_call(op: IeeeOp, width: FloatWidth, args: Vec<PureExpr>) -> PureExpr {
    PureExpr::LogicFnCall {
        name: IeeeFn::new(op, width).name(),
        args,
    }
}

/// A literal of `width` (an unsuffixed one cannot come out of MIR).
fn literal_in(expr: &PureExpr, width: FloatWidth) -> Option<f64> {
    match expr {
        PureExpr::Float(bits) if bits.width() == Some(width) => Some(bits.to_f64()),
        _ => None,
    }
}

/// Rust's own comparison of two literals: IEEE-754 in Rust is IEEE-754 here,
/// and an `f32` value compares the same after its exact widening to `f64`.
#[allow(clippy::float_cmp)] // Exact IEEE comparison is the behavior being mirrored.
fn fold_comparison(op: MirBinOp, l: f64, r: f64) -> Option<bool> {
    Some(match op {
        MirBinOp::Eq => l == r,
        MirBinOp::Ne => l != r,
        MirBinOp::Lt => l < r,
        MirBinOp::Le => l <= r,
        MirBinOp::Gt => l > r,
        MirBinOp::Ge => l >= r,
        _ => return None,
    })
}

/// Rust's own arithmetic on two literals of `width`: the host computes the
/// IEEE-754 round-to-nearest-even result the program computes.
#[allow(clippy::cast_possible_truncation)] // an f32 literal's value is an f32 value
fn fold_arithmetic(op: MirBinOp, width: FloatWidth, l: f64, r: f64) -> Option<PureExpr> {
    let bits = match width {
        FloatWidth::F64 => FloatBits::from_f64(match op {
            MirBinOp::Add => l + r,
            MirBinOp::Sub => l - r,
            MirBinOp::Mul => l * r,
            MirBinOp::Div => l / r,
            MirBinOp::Rem => l % r,
            _ => return None,
        }),
        FloatWidth::F32 => {
            let (l, r) = (l as f32, r as f32);
            FloatBits::from_f32(match op {
                MirBinOp::Add => l + r,
                MirBinOp::Sub => l - r,
                MirBinOp::Mul => l * r,
                MirBinOp::Div => l / r,
                MirBinOp::Rem => l % r,
                _ => return None,
            })
        }
    };
    Some(PureExpr::Float(bits))
}

/// A MIR binary operator over two `width` floats. `None` for an operator Rust
/// does not define over floats: an untranslated assignment keeps its
/// destination's source name, which for a parameter is its entry value, so
/// every float operator Rust has must translate here.
pub(super) fn translate_float_binop(
    op: MirBinOp,
    width: FloatWidth,
    left: PureExpr,
    right: PureExpr,
) -> Option<PureExpr> {
    if let (Some(l), Some(r)) = (literal_in(&left, width), literal_in(&right, width)) {
        if let Some(folded) = fold_comparison(op, l, r) {
            return Some(PureExpr::Bool(folded));
        }
        if let Some(folded) = fold_arithmetic(op, width, l, r) {
            return Some(folded);
        }
    }
    let ieee_op = match op {
        MirBinOp::Add => IeeeOp::Add,
        MirBinOp::Sub => IeeeOp::Sub,
        MirBinOp::Mul => IeeeOp::Mul,
        MirBinOp::Div => IeeeOp::Div,
        MirBinOp::Rem => IeeeOp::Rem,
        MirBinOp::Eq | MirBinOp::Ne => IeeeOp::Eq,
        MirBinOp::Lt => IeeeOp::Lt,
        MirBinOp::Le => IeeeOp::Le,
        MirBinOp::Gt => IeeeOp::Gt,
        MirBinOp::Ge => IeeeOp::Ge,
        _ => return None,
    };
    let call = ieee_call(ieee_op, width, vec![left, right]);
    // `a != b` is exactly the negation of IEEE `a == b` (true when either is
    // NaN), unlike `<`/`>=`, which are not each other's negation.
    Some(if matches!(op, MirBinOp::Ne) {
        PureExpr::UnOp(UnOp::Not, Arc::new(call))
    } else {
        call
    })
}

/// `-x` over a `width` float.
#[allow(clippy::cast_possible_truncation)] // an f32 literal's value is an f32 value
pub(super) fn translate_float_neg(width: FloatWidth, operand: PureExpr) -> PureExpr {
    match (literal_in(&operand, width), width) {
        (Some(value), FloatWidth::F64) => PureExpr::Float(FloatBits::from_f64(-value)),
        (Some(value), FloatWidth::F32) => PureExpr::Float(FloatBits::from_f32(-(value as f32))),
        (None, _) => ieee_call(IeeeOp::Neg, width, vec![operand]),
    }
}

/// `x as <float of target>` over a `source` float.
#[allow(clippy::cast_possible_truncation)] // `as f32` IS the rounding being mirrored
pub(super) fn translate_float_to_float(
    source: FloatWidth,
    target: FloatWidth,
    operand: PureExpr,
) -> PureExpr {
    if source == target {
        return operand;
    }
    match (literal_in(&operand, source), target) {
        (Some(value), FloatWidth::F64) => PureExpr::Float(FloatBits::from_f64(value)),
        (Some(value), FloatWidth::F32) => PureExpr::Float(FloatBits::from_f32(value as f32)),
        (None, _) => ieee_call(IeeeOp::ToFloat(target), source, vec![operand]),
    }
}

/// `x as <integer>` over a `source` float.
pub(super) fn translate_float_to_int(
    source: FloatWidth,
    signed: bool,
    bits: u32,
    operand: PureExpr,
) -> PureExpr {
    literal_in(&operand, source)
        .and_then(|value| fold_float_to_int(value, signed, bits))
        .unwrap_or_else(|| ieee_call(IeeeOp::ToInt { signed, bits }, source, vec![operand]))
}

/// Rust's own `as` from a float literal to an integer type: truncation toward
/// zero, saturation at the target's bounds, NaN to `0`. The conversion reads
/// only the value, so an `f32` literal's exact widening to `f64` converts the
/// same.
#[allow(clippy::cast_possible_truncation)] // `as` IS the conversion being mirrored
fn fold_float_to_int(value: f64, signed: bool, bits: u32) -> Option<PureExpr> {
    use super::constant::{large_signed_to_expr, large_unsigned_to_expr};
    Some(match (signed, bits) {
        (true, 8) => PureExpr::Int(i64::from(value as i8)),
        (true, 16) => PureExpr::Int(i64::from(value as i16)),
        (true, 32) => PureExpr::Int(i64::from(value as i32)),
        (true, 64) => PureExpr::Int(value as i64),
        (true, 128) => large_signed_to_expr(value as i128),
        (false, 8) => PureExpr::Int(i64::from(value as u8)),
        (false, 16) => PureExpr::Int(i64::from(value as u16)),
        (false, 32) => PureExpr::Int(i64::from(value as u32)),
        (false, 64) => large_unsigned_to_expr(u128::from(value as u64)),
        (false, 128) => large_unsigned_to_expr(value as u128),
        _ => return None,
    })
}

/// `<integer> as <float of target>`.
pub(super) fn translate_int_to_float(
    signed: bool,
    bits: u32,
    target: FloatWidth,
    operand: PureExpr,
) -> PureExpr {
    match operand {
        // Rust's own rounding of the integer's value into the target format.
        // The rounding reads only the value, so it is folded only for a value
        // the source type can hold.
        PureExpr::Int(value) if int_value_in_type(value, signed, bits) => {
            PureExpr::Float(int_to_float_bits(value, target))
        }
        _ => ieee_call(IeeeOp::FromInt { signed, bits }, target, vec![operand]),
    }
}

fn int_value_in_type(value: i64, signed: bool, bits: u32) -> bool {
    let value = i128::from(value);
    match (signed, bits) {
        (_, 0) | (_, 129..) => false,
        // Every i64 is an i128; the arm below would negate `1 << 127`, which overflows.
        (true, 128) => true,
        (true, bits) => {
            let half = 1_i128 << (bits - 1);
            (-half..half).contains(&value)
        }
        (false, 128) => value >= 0,
        (false, bits) => (0..(1_i128 << bits)).contains(&value),
    }
}

#[allow(clippy::cast_precision_loss)] // the rounding IS the conversion being mirrored
fn int_to_float_bits(value: i64, target: FloatWidth) -> FloatBits {
    match target {
        FloatWidth::F64 => FloatBits::from_f64(value as f64),
        FloatWidth::F32 => FloatBits::from_f32(value as f32),
    }
}
