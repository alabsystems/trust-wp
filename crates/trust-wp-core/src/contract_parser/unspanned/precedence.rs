// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Operator-precedence descent for expression parsing.
//!
//! From highest to lowest precedence: unary, multiplicative, additive, shift,
//! bitwise-and, bitwise-xor, bitwise-or, comparison, equality, logical-and,
//! logical-or, implication.

use std::sync::Arc;

use super::super::{helpers::borrows::dereference, ContractParser, ParseError, WrittenTypeSite};
use crate::formula::{BinOp, PureExpr, UnOp};

impl ContractParser<'_> {
    pub(in crate::contract_parser) fn parse_expr(&mut self) -> Result<PureExpr, ParseError> {
        self.parse_implies()
    }

    /// Parse ==> (implication, lowest precedence)
    pub(super) fn parse_implies(&mut self) -> Result<PureExpr, ParseError> {
        let mut left = self.parse_or()?;
        // Implication is right-associative: a ==> b ==> c means a ==> (b ==> c)
        if self.try_consume("==>") {
            let right = self.parse_implies()?;
            left = PureExpr::BinOp(Arc::new(left), BinOp::Implies, Arc::new(right));
        }
        Ok(left)
    }

    /// Parse ||
    pub(super) fn parse_or(&mut self) -> Result<PureExpr, ParseError> {
        let mut left = self.parse_and()?;
        while self.try_consume("||") {
            let right = self.parse_and()?;
            left = PureExpr::BinOp(Arc::new(left), BinOp::Or, Arc::new(right));
        }
        Ok(left)
    }

    /// Parse &&
    pub(super) fn parse_and(&mut self) -> Result<PureExpr, ParseError> {
        let mut left = self.parse_equality()?;
        while self.try_consume("&&") {
            let right = self.parse_equality()?;
            left = PureExpr::BinOp(Arc::new(left), BinOp::And, Arc::new(right));
        }
        Ok(left)
    }

    /// Parse == and !=
    pub(super) fn parse_equality(&mut self) -> Result<PureExpr, ParseError> {
        let mut left = self.parse_comparison()?;
        loop {
            // Check for == but not ==> (which has lower precedence)
            if self.try_consume_eq_not_implies() {
                let right = self.parse_comparison()?;
                left = PureExpr::BinOp(Arc::new(left), BinOp::Eq, Arc::new(right));
            } else if self.try_consume("!=") {
                let right = self.parse_comparison()?;
                left = PureExpr::BinOp(Arc::new(left), BinOp::Ne, Arc::new(right));
            } else {
                break;
            }
        }
        Ok(left)
    }

    /// Parse <, <=, >, >=
    pub(super) fn parse_comparison(&mut self) -> Result<PureExpr, ParseError> {
        let first = self.parse_bitwise_or()?;
        let Some(first_op) = self.try_parse_comparison_op() else {
            return Ok(first);
        };
        let first_right = self.parse_bitwise_or()?;

        // Creusot-style chained comparisons: `a < b < c` desugars to
        // `(a < b) && (b < c)` rather than nesting boolean/integer comparisons.
        // Build the first comparison directly, then fold chained operators with AND.
        let mut expr = PureExpr::BinOp(Arc::new(first), first_op, Arc::new(first_right.clone()));
        let mut prev_rhs = first_right;

        while let Some(op) = self.try_parse_comparison_op() {
            let right = self.parse_bitwise_or()?;
            let cmp = PureExpr::BinOp(Arc::new(prev_rhs.clone()), op, Arc::new(right.clone()));
            expr = PureExpr::BinOp(Arc::new(expr), BinOp::And, Arc::new(cmp));
            prev_rhs = right;
        }
        Ok(expr)
    }

    /// Parse bitwise OR (`|`)
    pub(super) fn parse_bitwise_or(&mut self) -> Result<PureExpr, ParseError> {
        let mut left = self.parse_bitwise_xor()?;
        while self.try_consume_single_pipe() {
            let right = self.parse_bitwise_xor()?;
            left = PureExpr::BinOp(Arc::new(left), BinOp::BitOr, Arc::new(right));
        }
        Ok(left)
    }

    /// Parse bitwise XOR (`^`)
    pub(super) fn parse_bitwise_xor(&mut self) -> Result<PureExpr, ParseError> {
        let mut left = self.parse_bitwise_and()?;
        while self.try_consume("^") {
            let right = self.parse_bitwise_and()?;
            left = PureExpr::BinOp(Arc::new(left), BinOp::BitXor, Arc::new(right));
        }
        Ok(left)
    }

    /// Parse bitwise AND (`&`)
    pub(super) fn parse_bitwise_and(&mut self) -> Result<PureExpr, ParseError> {
        let mut left = self.parse_shift()?;
        while self.try_consume_single_ampersand() {
            let right = self.parse_shift()?;
            left = PureExpr::BinOp(Arc::new(left), BinOp::BitAnd, Arc::new(right));
        }
        Ok(left)
    }

    /// Parse shift operators (`<<`, `>>`)
    pub(super) fn parse_shift(&mut self) -> Result<PureExpr, ParseError> {
        let mut left = self.parse_additive()?;
        loop {
            self.skip_whitespace();
            let at = self.position;
            if self.try_consume("<<") {
                let right = self.parse_additive()?;
                left = self.written_binop(left, BinOp::Shl, right, at)?;
            } else if self.try_consume(">>") {
                let right = self.parse_additive()?;
                left = self.written_binop(left, BinOp::Shr, right, at)?;
            } else {
                break;
            }
        }
        Ok(left)
    }

    /// Parse + and -
    pub(super) fn parse_additive(&mut self) -> Result<PureExpr, ParseError> {
        let mut left = self.parse_multiplicative()?;
        loop {
            self.skip_whitespace();
            let at = self.position;
            if self.try_consume("+") {
                let right = self.parse_multiplicative()?;
                left = self.written_binop(left, BinOp::Add, right, at)?;
            } else if self.try_consume("-") {
                let right = self.parse_multiplicative()?;
                left = self.written_binop(left, BinOp::Sub, right, at)?;
            } else {
                break;
            }
        }
        Ok(left)
    }

    /// Parse *, /, and %
    pub(super) fn parse_multiplicative(&mut self) -> Result<PureExpr, ParseError> {
        let mut left = self.parse_cast()?;
        loop {
            self.skip_whitespace();
            let at = self.position;
            if self.try_consume("*") {
                let right = self.parse_cast()?;
                left = self.written_binop(left, BinOp::Mul, right, at)?;
            } else if self.try_consume("/") {
                let right = self.parse_cast()?;
                // Creusot models the `/` operator on `Int` as
                // `int.ComputerDivision.div` (truncation toward zero), NOT
                // Euclidean — see creusot-std `impl DivLogic for Int`. Lower it
                // to `BinOp::DivTrunc` so contract division matches the signed
                // machine body (also `DivTrunc`). `div_euclid` stays Euclidean
                // (`BinOp::Div`). See trust-wp-divmod-semantics.
                left = self.written_binop(left, BinOp::DivTrunc, right, at)?;
            } else if self.try_consume("%") {
                let right = self.parse_cast()?;
                // Creusot's `%` on `Int` is `int.ComputerDivision.mod`
                // (truncating, sign of the dividend: `-3 % 2 == -1`). Lower it
                // to `BinOp::RemTrunc`; the Euclidean remainder is spelled
                // `a.rem_euclid(b)`. `x % 0` stays unspecified.
                left = self.written_binop(left, BinOp::RemTrunc, right, at)?;
            } else {
                break;
            }
        }
        Ok(left)
    }

    /// Parse cast expressions (`expr as Type`) and type ascriptions
    /// (`expr : Type`).
    ///
    /// A cast is Rust's `as` between integer types, lowered to exact integer
    /// arithmetic, or a parse error naming it (`lower_cast`); it is never its
    /// operand. A Pearlite ascription (`(term : Type)`) keeps the operand's
    /// value and states its sort (`ascribe`). The `: Type` is only consumed
    /// when a single `:` (not `::`) follows; quantifier/closure/let binders
    /// and struct fields consume their `:` before reaching expression
    /// parsing, so there is no collision.
    pub(super) fn parse_cast(&mut self) -> Result<PureExpr, ParseError> {
        let mut expr = self.parse_view()?;
        loop {
            self.skip_whitespace();
            let at = self.position;
            if self.try_consume_keyword("as") {
                self.skip_whitespace();
                let (_, text) = self.consume_written_type_text(WrittenTypeSite::Cast)?;
                expr = self.lower_cast(expr, &text, at)?;
            } else if self.try_consume_single_colon() {
                self.skip_whitespace();
                let (sort, text) = self.consume_written_type_text(WrittenTypeSite::Ascription)?;
                expr = self.ascribe(expr, sort.as_ref(), &text, "type ascription", at)?;
            } else {
                break;
            }
        }
        Ok(expr)
    }

    /// Parse the low-precedence view operator (`@`) after leading unary syntax.
    ///
    /// Creusot treats `*x@` / `^x@` as `(*x)@` / `(^x)@`, so `@` must bind to
    /// the completed unary expression rather than the unary operand.
    pub(super) fn parse_view(&mut self) -> Result<PureExpr, ParseError> {
        let expr = self.parse_unary()?;
        self.parse_view_suffix(expr)
    }

    /// Parse unary operators (!, ~, -, *, ^, &, &mut)
    ///
    /// RustHorn/Creusot-style operators:
    /// - `*v`: Dereference (current value of borrow)
    /// - `^v`: Final/prophecy value (value when borrow ends)
    /// - `&mut v` / `&v`: Reference operators (the AST keeps the operand)
    pub(super) fn parse_unary(&mut self) -> Result<PureExpr, ParseError> {
        self.skip_whitespace();
        let at = self.position;
        if self.try_consume("!") {
            let operand = self.parse_unary()?;
            return self.written_not(operand, at);
        }
        if self.try_consume("~") {
            let operand = self.parse_unary()?;
            return Ok(PureExpr::UnOp(UnOp::BitNot, Arc::new(operand)));
        }
        // Check for negation (must not be followed by digit for negative literal)
        if self.peek() == Some('-') && !self.is_negative_literal() {
            self.advance();
            let operand = self.parse_unary()?;
            return self.written_neg(operand, at);
        }
        // Dereference: *v (current value of a borrow). `*` of a borrow is the
        // borrowed value (`helpers/borrows.rs`).
        if self.try_consume("*") {
            let operand = self.parse_unary()?;
            return Ok(dereference(operand));
        }
        // Final/prophecy: ^v (value when borrow ends); never of a borrow.
        if self.try_consume("^") {
            let operand = self.parse_unary()?;
            return self.final_value(operand, "^");
        }
        // Reference operators: &mut expr / &expr. The finished AST has no
        // borrow node: `*` reads through the borrow, and otherwise the
        // operand stands for it (`result == &mut r.0` parses) and the borrow
        // is recorded (`helpers/borrows.rs`).
        let borrow_start = self.position;
        if self.try_consume_single_ampersand() {
            self.skip_whitespace();
            self.try_consume_keyword("mut");
            let operand = self.parse_unary()?;
            return Ok(self.borrow(borrow_start, operand));
        }
        self.parse_postfix()
    }

    /// Check if current position is a negative literal (minus followed by digit)
    pub(in crate::contract_parser) fn is_negative_literal(&self) -> bool {
        let remaining = &self.input[self.position..];
        let mut chars = remaining.chars();
        chars.next() == Some('-') && chars.next().is_some_and(|c| c.is_ascii_digit())
    }
}
