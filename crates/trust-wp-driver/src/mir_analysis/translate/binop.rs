// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Binary/unary operation translation.

use rustc_middle::{
    mir::{BinOp as MirBinOp, UnOp as MirUnOp},
    ty::{IntTy, UintTy},
};
use trust_wp_core::formula::{BinOp, UnOp};

/// Translate MIR BinOp to trust-wp BinOp.
///
/// `bool_operands`: when true, BitAnd/BitOr map to logical And/Or (correct for
/// boolean operands). When false, BitAnd/BitOr/BitXor/Shl/Shr map to their
/// bitwise PureExpr counterparts, which the ay encoder handles via either
/// UF approximation or native BV theory (when `bitwise_proof_mode` is active).
/// (#490, #2666)
pub(crate) fn translate_binop(op: MirBinOp, bool_operands: bool) -> Option<BinOp> {
    match op {
        MirBinOp::Add | MirBinOp::AddWithOverflow | MirBinOp::AddUnchecked => Some(BinOp::Add),
        MirBinOp::Sub | MirBinOp::SubWithOverflow | MirBinOp::SubUnchecked => Some(BinOp::Sub),
        MirBinOp::Mul | MirBinOp::MulWithOverflow | MirBinOp::MulUnchecked => Some(BinOp::Mul),
        MirBinOp::Div => Some(BinOp::Div),
        MirBinOp::Rem => Some(BinOp::Mod),
        MirBinOp::Eq => Some(BinOp::Eq),
        MirBinOp::Ne => Some(BinOp::Ne),
        MirBinOp::Lt => Some(BinOp::Lt),
        MirBinOp::Le => Some(BinOp::Le),
        MirBinOp::Gt => Some(BinOp::Gt),
        MirBinOp::Ge => Some(BinOp::Ge),
        // Boolean operands: BitAnd/BitOr are logical AND/OR (#490)
        MirBinOp::BitAnd if bool_operands => Some(BinOp::And),
        MirBinOp::BitOr if bool_operands => Some(BinOp::Or),
        // Integer operands: bitwise operations encoded via UF or BV theory (#2666)
        MirBinOp::BitAnd => Some(BinOp::BitAnd),
        MirBinOp::BitOr => Some(BinOp::BitOr),
        MirBinOp::BitXor => Some(BinOp::BitXor),
        MirBinOp::Shl => Some(BinOp::Shl),
        MirBinOp::Shr => Some(BinOp::Shr),
        _ => None,
    }
}

/// Translate MIR UnOp to trust-wp UnOp.
///
/// `bool_operand`: when true, `Not` maps to logical `UnOp::Not` (correct for
/// booleans). When false, `Not` returns None to avoid silently misencoding
/// integer bitwise complement as boolean negation (same class as #490).
/// `Neg` is always valid (arithmetic negation on integers).
pub(crate) fn translate_unop(op: MirUnOp, bool_operand: bool) -> Option<UnOp> {
    match op {
        MirUnOp::Not if bool_operand => Some(UnOp::Not),
        MirUnOp::Not => Some(UnOp::BitNot), // Integer bitwise complement (#2697)
        MirUnOp::Neg => Some(UnOp::Neg),
        MirUnOp::PtrMetadata => None, // Not supported in pure function translation
    }
}

#[allow(clippy::cast_possible_truncation)] // isize size always fits u32
pub(super) fn int_ty_bits(int_ty: IntTy) -> u32 {
    match int_ty {
        IntTy::Isize => (std::mem::size_of::<isize>() * 8) as u32,
        IntTy::I8 => 8,
        IntTy::I16 => 16,
        IntTy::I32 => 32,
        IntTy::I64 => 64,
        IntTy::I128 => 128,
    }
}

#[allow(clippy::cast_possible_truncation)] // usize size always fits u32
pub(super) fn uint_ty_bits(uint_ty: UintTy) -> u32 {
    match uint_ty {
        UintTy::Usize => (std::mem::size_of::<usize>() * 8) as u32,
        UintTy::U8 => 8,
        UintTy::U16 => 16,
        UintTy::U32 => 32,
        UintTy::U64 => 64,
        UintTy::U128 => 128,
    }
}
