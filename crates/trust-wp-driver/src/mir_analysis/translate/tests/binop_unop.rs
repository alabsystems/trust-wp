// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

// Tests for translate_binop - maps MIR binary operators to trust-wp operators
mod translate_binop_tests {
    use super::*;

    #[test]
    fn test_arithmetic_ops() {
        // Basic arithmetic - bool_operands flag doesn't affect these
        assert_eq!(translate_binop(MirBinOp::Add, false), Some(BinOp::Add));
        assert_eq!(translate_binop(MirBinOp::Sub, false), Some(BinOp::Sub));
        assert_eq!(translate_binop(MirBinOp::Mul, false), Some(BinOp::Mul));
        assert_eq!(translate_binop(MirBinOp::Div, false), Some(BinOp::Div));
        assert_eq!(translate_binop(MirBinOp::Rem, false), Some(BinOp::Mod));
    }

    #[test]
    fn test_overflow_variants() {
        // Overflow-checking variants should map to base operations
        assert_eq!(
            translate_binop(MirBinOp::AddWithOverflow, false),
            Some(BinOp::Add)
        );
        assert_eq!(
            translate_binop(MirBinOp::SubWithOverflow, false),
            Some(BinOp::Sub)
        );
        assert_eq!(
            translate_binop(MirBinOp::MulWithOverflow, false),
            Some(BinOp::Mul)
        );
    }

    #[test]
    fn test_unchecked_variants() {
        // Unchecked variants should map to base operations
        assert_eq!(
            translate_binop(MirBinOp::AddUnchecked, false),
            Some(BinOp::Add)
        );
        assert_eq!(
            translate_binop(MirBinOp::SubUnchecked, false),
            Some(BinOp::Sub)
        );
        assert_eq!(
            translate_binop(MirBinOp::MulUnchecked, false),
            Some(BinOp::Mul)
        );
    }

    #[test]
    fn test_comparison_ops() {
        assert_eq!(translate_binop(MirBinOp::Eq, false), Some(BinOp::Eq));
        assert_eq!(translate_binop(MirBinOp::Ne, false), Some(BinOp::Ne));
        assert_eq!(translate_binop(MirBinOp::Lt, false), Some(BinOp::Lt));
        assert_eq!(translate_binop(MirBinOp::Le, false), Some(BinOp::Le));
        assert_eq!(translate_binop(MirBinOp::Gt, false), Some(BinOp::Gt));
        assert_eq!(translate_binop(MirBinOp::Ge, false), Some(BinOp::Ge));
    }

    #[test]
    fn test_bitand_bitor_bool_operands() {
        // BitAnd/BitOr map to logical And/Or only for boolean operands
        assert_eq!(translate_binop(MirBinOp::BitAnd, true), Some(BinOp::And));
        assert_eq!(translate_binop(MirBinOp::BitOr, true), Some(BinOp::Or));
    }

    #[test]
    fn test_bitwise_int_operands_produce_bitwise_ops() {
        // BitAnd/BitOr/BitXor/Shl/Shr on integer operands produce bitwise
        // BinOp variants for UF or BV encoding (#490, #2666)
        assert_eq!(
            translate_binop(MirBinOp::BitAnd, false),
            Some(BinOp::BitAnd)
        );
        assert_eq!(translate_binop(MirBinOp::BitOr, false), Some(BinOp::BitOr));
        assert_eq!(
            translate_binop(MirBinOp::BitXor, false),
            Some(BinOp::BitXor)
        );
        assert_eq!(translate_binop(MirBinOp::Shl, false), Some(BinOp::Shl));
        assert_eq!(translate_binop(MirBinOp::Shr, false), Some(BinOp::Shr));
    }

    #[test]
    fn test_unsupported_ops() {
        // Offset is not supported in the verification encoding
        assert_eq!(translate_binop(MirBinOp::Offset, false), None);
    }
}

// Tests for translate_unop - maps MIR unary operators to trust-wp operators
mod translate_unop_tests {
    use super::*;

    #[test]
    fn test_not_bool_operand() {
        // Not on boolean operands maps to logical negation
        assert_eq!(translate_unop(MirUnOp::Not, true), Some(UnOp::Not));
    }

    #[test]
    fn test_not_non_bool_is_bitnot() {
        // Not on integer operands is bitwise complement (#2697)
        assert_eq!(translate_unop(MirUnOp::Not, false), Some(UnOp::BitNot));
    }

    #[test]
    fn test_neg_op() {
        // Neg is always valid (arithmetic negation), regardless of bool flag
        assert_eq!(translate_unop(MirUnOp::Neg, false), Some(UnOp::Neg));
        assert_eq!(translate_unop(MirUnOp::Neg, true), Some(UnOp::Neg));
    }

    #[test]
    fn test_ptr_metadata_returns_none() {
        assert_eq!(translate_unop(MirUnOp::PtrMetadata, false), None);
    }
}
