// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Structural sort shape checks on parsed specification expressions.

use super::PureExpr;
use crate::formula::{BinOp, UnOp};

impl PureExpr {
    /// True when this expression is STRUCTURALLY guaranteed not to be `bool`.
    ///
    /// Used to reject assertion bodies whose type is not `bool`, e.g.
    /// `proof_assert! { 1 }` (Creusot: `error[E0308]: mismatched types,
    /// expected bool, found Int`). Conservative: only numeric literals,
    /// arithmetic/shift operators, unary minus, and `if`/`let`/`old`/`*`/`^`
    /// wrappers whose result is itself definitely non-boolean. Bitwise
    /// `&`/`|`/`^` and `!` are NOT included: on `bool` operands they are
    /// boolean. Anything ambiguous (variables, calls, fields) returns false.
    #[must_use]
    pub fn is_definitely_non_boolean(&self) -> bool {
        match self {
            Self::Int(_) | Self::Float(_) => true,
            Self::BinOp(
                _,
                BinOp::Add
                | BinOp::Sub
                | BinOp::Mul
                | BinOp::Div
                | BinOp::Mod
                | BinOp::DivTrunc
                | BinOp::RemTrunc
                | BinOp::Shl
                | BinOp::Shr,
                _,
            )
            | Self::UnOp(UnOp::Neg, _) => true,
            // Bitwise `&`/`|`/`^` are boolean on bool operands and integer on
            // integer operands, so they are definitely non-boolean only when
            // an operand is.
            Self::BinOp(lhs, BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor, rhs) => {
                lhs.is_definitely_non_boolean() || rhs.is_definitely_non_boolean()
            }
            Self::Old(inner) | Self::Deref(inner) | Self::Final(inner) => {
                inner.is_definitely_non_boolean()
            }
            Self::Ite(_, then_branch, else_branch) => {
                then_branch.is_definitely_non_boolean() && else_branch.is_definitely_non_boolean()
            }
            _ => false,
        }
    }

    /// True when this expression must be REFUSED as a boolean contract clause
    /// (`requires`/`ensures`/`invariant`).
    ///
    /// THE CODE THAT GRANTS AND THE CODE THAT OWES MUST BE THE SAME CODE. Two
    /// places decide this question about the same clause text: the driver, in
    /// `callbacks::parsing::clauses::parse_boolean_clause`, which refuses the
    /// clause and then declines to verify the function at all; and the macro
    /// vehicle, in `trust-wp-macros`' `spec_tc::driver_parses`, which SKIPS
    /// emitting a rustc type-check for exactly the clauses the driver is going
    /// to refuse (so the user sees the driver's parse diagnostic rather than an
    /// E0308 from inside the vehicle). Those two lived as hand-copied twins.
    /// They agreed, but if this predicate ever narrows on one side only, the
    /// macro skips the type-check for a clause the driver then ACCEPTS — the
    /// clause reaches the encoder having been checked by nobody.
    ///
    /// It is `is_definitely_non_boolean` with one exception: an `if`/`else` is
    /// never refused structurally, because its branches may be opaque.
    #[must_use]
    pub fn is_refused_as_boolean_clause(&self) -> bool {
        match self {
            Self::Ite(..) => false,
            _ => self.is_definitely_non_boolean(),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;

    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    #[test]
    fn numeric_literals_and_arithmetic_are_non_boolean() {
        assert!(PureExpr::Int(1).is_definitely_non_boolean());
        let sum = PureExpr::BinOp(Arc::new(var("x")), BinOp::Add, Arc::new(PureExpr::Int(1)));
        assert!(sum.is_definitely_non_boolean());
        assert!(PureExpr::UnOp(UnOp::Neg, Arc::new(var("x"))).is_definitely_non_boolean());
        let ite = PureExpr::Ite(
            Arc::new(var("c")),
            Arc::new(PureExpr::Int(1)),
            Arc::new(PureExpr::Int(2)),
        );
        assert!(ite.is_definitely_non_boolean());
        assert!(PureExpr::Old(Arc::new(PureExpr::Int(3))).is_definitely_non_boolean());
        let masked = PureExpr::BinOp(
            Arc::new(var("x")),
            BinOp::BitAnd,
            Arc::new(PureExpr::Int(1)),
        );
        assert!(masked.is_definitely_non_boolean());
    }

    #[test]
    fn boolean_or_ambiguous_shapes_are_not_rejected() {
        assert!(!PureExpr::Bool(true).is_definitely_non_boolean());
        assert!(!var("b").is_definitely_non_boolean());
        let cmp = PureExpr::BinOp(Arc::new(var("x")), BinOp::Eq, Arc::new(PureExpr::Int(1)));
        assert!(!cmp.is_definitely_non_boolean());
        // `a & b` / `a | b` / `a ^ b` / `!a` are boolean on bool operands.
        for op in [BinOp::BitAnd, BinOp::BitOr, BinOp::BitXor] {
            let e = PureExpr::BinOp(Arc::new(var("a")), op, Arc::new(var("b")));
            assert!(!e.is_definitely_non_boolean(), "{op:?}");
        }
        assert!(!PureExpr::UnOp(UnOp::Not, Arc::new(var("a"))).is_definitely_non_boolean());
        let mixed = PureExpr::Ite(
            Arc::new(var("c")),
            Arc::new(PureExpr::Int(1)),
            Arc::new(var("b")),
        );
        assert!(!mixed.is_definitely_non_boolean());
    }

    #[test]
    fn parsed_non_bool_assertion_bodies_are_rejected() {
        use crate::contract_parser::parse_contract_body;
        for text in ["1", "x + 1", "-x", "2.5", "x & 1", "(x + 1) | y"] {
            let expr = parse_contract_body(text).expect(text);
            assert!(expr.is_definitely_non_boolean(), "{text}");
        }
        for text in [
            "true",
            "x == 1",
            "a & b",
            "a | (b ^ c)",
            "forall<i: Int> i == i",
            "x@ == 1",
        ] {
            let expr = parse_contract_body(text).expect(text);
            assert!(!expr.is_definitely_non_boolean(), "{text}");
        }
    }
}
