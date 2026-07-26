// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Postfix expression parsing: method calls, field access, indexing, range
//! slicing, plus the lower-precedence view (`@`) suffix.

use std::sync::Arc;

use super::super::{ContractParser, ParseError};
use crate::formula::{
    internal::tuple_lowering::{tuple_field_logic_fn_name, NAMED_FIELD_LOGIC_FN_PREFIX},
    BinOp, PureExpr,
};

impl ContractParser<'_> {
    /// Parse high-precedence postfix operators (method calls, field access,
    /// indexing, and range slicing) on top of a primary expression.
    pub(super) fn parse_postfix(&mut self) -> Result<PureExpr, ParseError> {
        let expr = self.parse_primary()?;
        self.parse_postfix_suffix(expr)
    }

    /// Parse repeated postfix suffixes after a primary expression.
    pub(in crate::contract_parser) fn parse_postfix_suffix(
        &mut self,
        mut expr: PureExpr,
    ) -> Result<PureExpr, ParseError> {
        loop {
            self.skip_whitespace();

            // Method call, field access, or tuple field access.
            // Use try_consume_single_dot to avoid consuming the first `.` of
            // a `..` or `..=` range operator inside index brackets. (#1513)
            if self.try_consume_single_dot() {
                // Tuple field access: expr.0, expr.1, etc.
                if let Some(index) = self.try_parse_tuple_field_index() {
                    expr = PureExpr::LogicFnCall {
                        name: tuple_field_logic_fn_name(index),
                        args: vec![expr],
                    };
                    continue;
                }
                let method_name = self
                    .try_parse_method_name()
                    .ok_or_else(|| self.error("expected method name or tuple index after '.'"))?;
                self.skip_whitespace();
                if self.try_consume("(") {
                    // Method call: expr.method(args...)
                    let args = self.parse_argument_list()?;
                    if !self.try_consume(")") {
                        return Err(self.error("expected ')' after method arguments"));
                    }
                    expr = PureExpr::MethodCall {
                        receiver: Arc::new(expr),
                        method: method_name,
                        args,
                    };
                } else {
                    // Named field access: expr.field
                    // Lowered to a synthetic logic function call like tuple fields
                    expr = PureExpr::LogicFnCall {
                        name: format!("{NAMED_FIELD_LOGIC_FN_PREFIX}{method_name}"),
                        args: vec![expr],
                    };
                }
                continue;
            }

            // Indexing or range slicing: expr[index] or expr[a..b] etc.
            // Plain index → expr.index_logic(index)
            // Range variants → expr.subsequence(from, to) (#1513)
            if self.try_consume("[") {
                expr = self.parse_index_or_range(expr)?;
                continue;
            }

            break;
        }

        Ok(expr)
    }

    /// Parse one-or-more low-precedence view suffixes, allowing the usual
    /// field/index/method chain after each `@`.
    pub(in crate::contract_parser) fn parse_view_suffix(
        &mut self,
        mut expr: PureExpr,
    ) -> Result<PureExpr, ParseError> {
        loop {
            self.skip_whitespace();
            if !self.try_consume("@") {
                break;
            }
            expr = PureExpr::View(Arc::new(expr));
            expr = self.parse_postfix_suffix(expr)?;
        }
        Ok(expr)
    }

    /// Parse the contents inside `[...]` after consuming the opening bracket.
    ///
    /// Detects range syntax and desugars to `subsequence` method calls on the
    /// receiver, following Creusot's `IndexLogic` impls for `Range`, `RangeFrom`,
    /// `RangeTo`, `RangeToInclusive`, `RangeInclusive`, and `RangeFull`. (#1513)
    ///
    /// | Syntax      | Desugaring                          |
    /// |-------------|-------------------------------------|
    /// | `s[a..b]`   | `s.subsequence(a, b)`               |
    /// | `s[a..=b]`  | `s.subsequence(a, b + 1)`           |
    /// | `s[a..]`    | `s.subsequence(a, s.len())`         |
    /// | `s[..b]`    | `s.subsequence(0, b)`               |
    /// | `s[..=b]`   | `s.subsequence(0, b + 1)`           |
    /// | `s[..]`     | `s.subsequence(0, s.len())`         |
    /// | `s[i]`      | `s.index_logic(i)`                  |
    pub(in crate::contract_parser) fn parse_index_or_range(
        &mut self,
        receiver: PureExpr,
    ) -> Result<PureExpr, ParseError> {
        self.skip_whitespace();

        // Helper: build `receiver.len()` for open-ended ranges
        let make_len = |recv: &PureExpr| -> PureExpr {
            PureExpr::MethodCall {
                receiver: Arc::new(recv.clone()),
                method: "len".to_string(),
                args: vec![],
            }
        };

        // Check for range starting with `..`
        if self.try_consume("..=") {
            // `..=b` → subsequence(0, b + 1)
            let end = self.parse_expr()?;
            if !self.try_consume("]") {
                return Err(self.error("expected ']' after range expression"));
            }
            let end_plus_one =
                PureExpr::BinOp(Arc::new(end), BinOp::Add, Arc::new(PureExpr::Int(1)));
            return Ok(PureExpr::MethodCall {
                receiver: Arc::new(receiver),
                method: "subsequence".to_string(),
                args: vec![PureExpr::Int(0), end_plus_one],
            });
        }
        if self.try_consume("..") {
            self.skip_whitespace();
            if self.try_consume("]") {
                // `..` (full range) → subsequence(0, s.len())
                let len = make_len(&receiver);
                return Ok(PureExpr::MethodCall {
                    receiver: Arc::new(receiver),
                    method: "subsequence".to_string(),
                    args: vec![PureExpr::Int(0), len],
                });
            }
            // `..b` → subsequence(0, b)
            let end = self.parse_expr()?;
            if !self.try_consume("]") {
                return Err(self.error("expected ']' after range expression"));
            }
            return Ok(PureExpr::MethodCall {
                receiver: Arc::new(receiver),
                method: "subsequence".to_string(),
                args: vec![PureExpr::Int(0), end],
            });
        }

        // Parse the first expression (could be plain index or range start)
        let first = self.parse_expr()?;
        self.skip_whitespace();

        // Check for range operators after the first expression
        if self.try_consume("..=") {
            // `a..=b` → subsequence(a, b + 1)
            let end = self.parse_expr()?;
            if !self.try_consume("]") {
                return Err(self.error("expected ']' after range expression"));
            }
            let end_plus_one =
                PureExpr::BinOp(Arc::new(end), BinOp::Add, Arc::new(PureExpr::Int(1)));
            return Ok(PureExpr::MethodCall {
                receiver: Arc::new(receiver),
                method: "subsequence".to_string(),
                args: vec![first, end_plus_one],
            });
        }
        if self.try_consume("..") {
            self.skip_whitespace();
            if self.try_consume("]") {
                // `a..` → subsequence(a, s.len())
                let len = make_len(&receiver);
                return Ok(PureExpr::MethodCall {
                    receiver: Arc::new(receiver),
                    method: "subsequence".to_string(),
                    args: vec![first, len],
                });
            }
            // `a..b` → subsequence(a, b)
            let end = self.parse_expr()?;
            if !self.try_consume("]") {
                return Err(self.error("expected ']' after range expression"));
            }
            return Ok(PureExpr::MethodCall {
                receiver: Arc::new(receiver),
                method: "subsequence".to_string(),
                args: vec![first, end],
            });
        }

        // Plain index: `s[i]` → s.index_logic(i)
        if !self.try_consume("]") {
            return Err(self.error("expected ']' after index expression"));
        }
        Ok(PureExpr::MethodCall {
            receiver: Arc::new(receiver),
            method: "index_logic".to_string(),
            args: vec![first],
        })
    }
}
