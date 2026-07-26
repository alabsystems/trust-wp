// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Operator-precedence descent for expression parsing.
//!
//! From highest to lowest precedence: unary, multiplicative, additive, shift,
//! bitwise-and, bitwise-xor, bitwise-or, comparison, equality, logical-and,
//! logical-or, implication.

use std::sync::Arc;

use super::super::{ContractParser, ParseError};
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
            if self.try_consume("<<") {
                let right = self.parse_additive()?;
                left = PureExpr::BinOp(Arc::new(left), BinOp::Shl, Arc::new(right));
            } else if self.try_consume(">>") {
                let right = self.parse_additive()?;
                left = PureExpr::BinOp(Arc::new(left), BinOp::Shr, Arc::new(right));
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
            if self.try_consume("+") {
                let right = self.parse_multiplicative()?;
                left = PureExpr::BinOp(Arc::new(left), BinOp::Add, Arc::new(right));
            } else if self.try_consume("-") {
                let right = self.parse_multiplicative()?;
                left = PureExpr::BinOp(Arc::new(left), BinOp::Sub, Arc::new(right));
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
            if self.try_consume("*") {
                let right = self.parse_cast()?;
                left = PureExpr::BinOp(Arc::new(left), BinOp::Mul, Arc::new(right));
            } else if self.try_consume("/") {
                let right = self.parse_cast()?;
                // Creusot models the `/` operator on `Int` as
                // `int.ComputerDivision.div` (truncation toward zero), NOT
                // Euclidean — see creusot-std `impl DivLogic for Int`. Lower it
                // to `BinOp::DivTrunc` so contract division matches the signed
                // machine body (also `DivTrunc`). `div_euclid` stays Euclidean
                // (`BinOp::Div`). See trust-wp-divmod-semantics.
                left = PureExpr::BinOp(Arc::new(left), BinOp::DivTrunc, Arc::new(right));
            } else if self.try_consume("%") {
                let right = self.parse_cast()?;
                // `%` stays Euclidean (`BinOp::Mod`): trust-wp-std's wrapping
                // arithmetic specs reduce a possibly-negative dividend modulo
                // `2^n` and rely on the non-negative Euclidean remainder. Only
                // `/` is reclassified to truncated. See trust-wp-divmod-semantics.
                left = PureExpr::BinOp(Arc::new(left), BinOp::Mod, Arc::new(right));
            } else {
                break;
            }
        }
        Ok(left)
    }

    /// Parse cast expressions (`expr as Type`) and type ascriptions
    /// (`expr : Type`).
    ///
    /// Casts are currently treated as logical no-ops so contracts using
    /// pointer/integer cast syntax can be parsed and encoded. Pearlite type
    /// ascriptions (`(term : Type)`) are likewise transparent: the ascribed
    /// type is parsed and discarded, and the inner expression is returned
    /// unchanged. The `: Type` is only consumed when a single `:` (not `::`)
    /// follows; quantifier/closure/let binders and struct fields consume their
    /// `:` before reaching expression parsing, so there is no collision.
    pub(super) fn parse_cast(&mut self) -> Result<PureExpr, ParseError> {
        let expr = self.parse_view()?;
        loop {
            if self.try_consume_keyword("as") {
                self.skip_whitespace();
                self.consume_type_annotation()?;
            } else if self.try_consume_single_colon() {
                self.skip_whitespace();
                self.consume_type_annotation()?;
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
    /// - `&mut v` / `&v`: Reference operators (transparent in contract logic)
    pub(super) fn parse_unary(&mut self) -> Result<PureExpr, ParseError> {
        self.skip_whitespace();
        if self.try_consume("!") {
            let operand = self.parse_unary()?;
            return Ok(PureExpr::UnOp(UnOp::Not, Arc::new(operand)));
        }
        if self.try_consume("~") {
            let operand = self.parse_unary()?;
            return Ok(PureExpr::UnOp(UnOp::BitNot, Arc::new(operand)));
        }
        // Check for negation (must not be followed by digit for negative literal)
        if self.peek() == Some('-') && !self.is_negative_literal() {
            self.advance();
            let operand = self.parse_unary()?;
            return Ok(PureExpr::UnOp(UnOp::Neg, Arc::new(operand)));
        }
        // Dereference: *v (current value of mutable borrow)
        if self.try_consume("*") {
            let operand = self.parse_unary()?;
            return Ok(PureExpr::Deref(Arc::new(operand)));
        }
        // Final/prophecy: ^v (value when borrow ends)
        if self.try_consume("^") {
            let operand = self.parse_unary()?;
            return Ok(PureExpr::Final(Arc::new(operand)));
        }
        // Reference operators: &mut expr / &expr
        // In contract logic, references are transparent — the reference operator
        // is parsed but does not change the logical value. This allows Creusot
        // contracts like `result == &mut r.0` to parse correctly.
        if self.try_consume_single_ampersand() {
            self.skip_whitespace();
            self.try_consume_keyword("mut");
            let operand = self.parse_unary()?;
            return Ok(operand);
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
