// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Block expression parsing: block bodies, let-bindings, pattern desugaring,
//! top-level body parsing, and line-comment skipping.

use std::sync::Arc;

use super::super::{ContractParser, ParseError};
use crate::formula::{
    internal::tuple_lowering::{tuple_field_logic_fn_name, tuple_logic_fn_name},
    MatchArm, Pattern, PureExpr,
};

impl ContractParser<'_> {
    /// Parse a block expression: `{ stmt; stmt; expr }`.
    ///
    /// Statements are either let-bindings (`let x = expr;`) or expression
    /// statements (`expr;`). The final expression (without semicolon) is the
    /// block's value. Let-bindings are lowered to nested `PureExpr::Let` nodes.
    /// Expression statements are discarded (their value is unused in spec
    /// context) and only the trailing expression is kept.
    pub(in crate::contract_parser) fn parse_block(&mut self) -> Result<PureExpr, ParseError> {
        if !self.try_consume("{") {
            return Err(self.error("expected '{'"));
        }
        let result = self.parse_block_body()?;
        self.skip_whitespace();
        if !self.try_consume("}") {
            return Err(self.error("expected '}'"));
        }
        Ok(result)
    }

    /// Parse a top-level block body (statements + trailing expression) terminated
    /// by end-of-input rather than `}`.
    ///
    /// Used by `parse_as_block` for multi-statement `proof_assert!` text where
    /// the input is not wrapped in braces.
    pub(in crate::contract_parser) fn parse_top_level_body(
        &mut self,
    ) -> Result<PureExpr, ParseError> {
        self.skip_whitespace();
        self.skip_line_comments();

        // End of input → unit
        if self.peek().is_none() {
            return Ok(PureExpr::LogicFnCall {
                name: tuple_logic_fn_name(0),
                args: vec![],
            });
        }

        // Skip `use` statements — compile-time imports, no effect in contracts.
        // (#1513, syntax/05_pearlite.rs)
        if self.try_consume_keyword("use") {
            while let Some(c) = self.peek() {
                self.advance();
                if c == ';' {
                    break;
                }
            }
            return self.parse_top_level_body();
        }

        // Let-binding: `let <ident> = <expr>; <body>`
        if self.try_consume_keyword("let") {
            // Let bindings call parse_block_body for their continuation;
            // but at top-level we need to handle end-of-input. For now,
            // fall back to the brace-based let binding (it will work as
            // long as there are further expressions after the semicolon).
            return self.parse_let_binding_top_level();
        }

        // Expression — could be a statement (followed by `;`) or trailing expr
        let expr = self.parse_expr()?;
        self.skip_whitespace();
        self.skip_line_comments();

        if self.try_consume(";") {
            self.skip_whitespace();
            self.skip_line_comments();
            // If end-of-input follows, this was a trailing statement.
            // The semicolon discards the value; evaluates to unit.
            if self.peek().is_none() {
                let unit = PureExpr::LogicFnCall {
                    name: tuple_logic_fn_name(0),
                    args: vec![],
                };
                return if self.preserve_stmt_exprs {
                    Ok(self.wrap_stmt_expr(expr, unit))
                } else {
                    Ok(unit)
                };
            }
            // More statements/expressions follow — parse rest.
            // The expression statement is discarded (spec context: no side effects).
            let body = self.parse_top_level_body()?;
            if self.preserve_stmt_exprs {
                Ok(self.wrap_stmt_expr(expr, body))
            } else {
                Ok(body)
            }
        } else {
            // No semicolon — this is the trailing expression (block value).
            Ok(expr)
        }
    }

    /// Parse a top-level block body and retain leading expression statements.
    pub(in crate::contract_parser) fn parse_top_level_body_with_leading_exprs(
        &mut self,
    ) -> Result<(Vec<PureExpr>, PureExpr), ParseError> {
        self.skip_whitespace();
        self.skip_line_comments();

        if self.peek().is_none() {
            return Ok((
                Vec::new(),
                PureExpr::LogicFnCall {
                    name: tuple_logic_fn_name(0),
                    args: vec![],
                },
            ));
        }

        if self.try_consume_keyword("use") {
            while let Some(c) = self.peek() {
                self.advance();
                if c == ';' {
                    break;
                }
            }
            return self.parse_top_level_body_with_leading_exprs();
        }

        if self.try_consume_keyword("let") {
            return Ok((Vec::new(), self.parse_let_binding_top_level()?));
        }

        let expr = self.parse_expr()?;
        self.skip_whitespace();
        self.skip_line_comments();

        if self.try_consume(";") {
            self.skip_whitespace();
            self.skip_line_comments();
            if self.peek().is_none() {
                return Ok((
                    vec![expr],
                    PureExpr::LogicFnCall {
                        name: tuple_logic_fn_name(0),
                        args: vec![],
                    },
                ));
            }
            let (mut rest, tail) = self.parse_top_level_body_with_leading_exprs()?;
            let mut leading = Vec::with_capacity(rest.len() + 1);
            leading.push(expr);
            leading.append(&mut rest);
            Ok((leading, tail))
        } else {
            Ok((Vec::new(), expr))
        }
    }

    /// Parse a let-binding at top level (end-of-input terminated).
    ///
    /// Supports `let else` (RFC 3137) — see `parse_let_binding` for desugaring.
    fn parse_let_binding_top_level(&mut self) -> Result<PureExpr, ParseError> {
        self.skip_whitespace();

        // `let mut x = ...` — consume `mut` transparently (#1513)
        self.try_consume_keyword("mut");
        self.skip_whitespace();

        let pattern = self.parse_pattern()?;

        self.skip_whitespace();
        if self.try_consume(":") {
            self.consume_type_annotation()?;
        }

        self.skip_whitespace();
        if !self.try_consume("=") {
            return Err(self.error("expected '=' in let binding"));
        }

        let value = self.parse_expr()?;
        self.skip_whitespace();

        // `let <pat> = <expr> else { <block> };` at top level
        if self.try_consume_keyword("else") {
            return self.finish_let_else_binding_top_level(pattern, value);
        }

        if !self.try_consume(";") {
            return Err(self.error("expected ';' after let binding value"));
        }

        let body = self.parse_top_level_body()?;

        Self::desugar_let_pattern(pattern, value, body)
    }

    /// Top-level variant of `finish_let_else_binding`.
    fn finish_let_else_binding_top_level(
        &mut self,
        pattern: Pattern,
        value: PureExpr,
    ) -> Result<PureExpr, ParseError> {
        self.skip_whitespace();
        if !self.try_consume("{") {
            return Err(self.error("expected '{' after 'else' in let-else binding"));
        }
        let else_body = self.parse_block_body()?;
        self.skip_whitespace();
        if !self.try_consume("}") {
            return Err(self.error("expected '}' to close let-else block"));
        }
        self.skip_whitespace();
        if !self.try_consume(";") {
            return Err(self.error("expected ';' after let-else binding"));
        }
        let rest = self.parse_top_level_body()?;
        Ok(PureExpr::Match {
            scrutinee: Arc::new(value),
            arms: vec![
                MatchArm {
                    pattern,
                    body: rest,
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    body: else_body,
                },
            ],
        })
    }

    /// Parse the body of a block (statements + trailing expression).
    pub(in crate::contract_parser) fn parse_block_body(&mut self) -> Result<PureExpr, ParseError> {
        self.skip_whitespace();
        self.skip_line_comments();

        // Empty block → unit
        if self.peek() == Some('}') {
            return Ok(PureExpr::LogicFnCall {
                name: tuple_logic_fn_name(0),
                args: vec![],
            });
        }

        // Skip `use` statements inside blocks — they're compile-time imports
        // with no runtime effect. Consume `use ... ;` and continue parsing
        // the rest of the block body. (#1513, syntax/05_pearlite.rs)
        if self.try_consume_keyword("use") {
            // Consume everything until the semicolon
            while let Some(c) = self.peek() {
                self.advance();
                if c == ';' {
                    break;
                }
            }
            return self.parse_block_body();
        }

        // Let-binding: `let <ident> = <expr>; <body>`
        if self.try_consume_keyword("let") {
            return self.parse_let_binding();
        }

        // Expression — could be a statement (followed by `;`) or trailing expr
        let expr = self.parse_expr()?;
        self.skip_whitespace();
        self.skip_line_comments();

        if self.try_consume(";") {
            self.skip_whitespace();
            self.skip_line_comments();
            // If closing brace follows, this was a trailing statement.
            // The semicolon discards the value; the block evaluates to unit.
            if self.peek() == Some('}') {
                let unit = PureExpr::LogicFnCall {
                    name: tuple_logic_fn_name(0),
                    args: vec![],
                };
                return if self.preserve_stmt_exprs {
                    Ok(self.wrap_stmt_expr(expr, unit))
                } else {
                    Ok(unit)
                };
            }
            // More statements/expressions follow — parse rest of block body.
            // The expression statement is discarded (spec context: no side effects).
            let body = self.parse_block_body()?;
            if self.preserve_stmt_exprs {
                Ok(self.wrap_stmt_expr(expr, body))
            } else {
                Ok(body)
            }
        } else {
            // No semicolon — this is the trailing expression (block value).
            Ok(expr)
        }
    }

    /// Parse the body of a block and retain leading expression statements.
    pub(in crate::contract_parser) fn parse_block_body_with_leading_exprs(
        &mut self,
    ) -> Result<(Vec<PureExpr>, PureExpr), ParseError> {
        self.skip_whitespace();
        self.skip_line_comments();

        if self.peek() == Some('}') {
            return Ok((
                Vec::new(),
                PureExpr::LogicFnCall {
                    name: tuple_logic_fn_name(0),
                    args: vec![],
                },
            ));
        }

        if self.try_consume_keyword("use") {
            while let Some(c) = self.peek() {
                self.advance();
                if c == ';' {
                    break;
                }
            }
            return self.parse_block_body_with_leading_exprs();
        }

        if self.try_consume_keyword("let") {
            return Ok((Vec::new(), self.parse_let_binding()?));
        }

        let expr = self.parse_expr()?;
        self.skip_whitespace();
        self.skip_line_comments();

        if self.try_consume(";") {
            self.skip_whitespace();
            self.skip_line_comments();
            if self.peek() == Some('}') {
                return Ok((
                    vec![expr],
                    PureExpr::LogicFnCall {
                        name: tuple_logic_fn_name(0),
                        args: vec![],
                    },
                ));
            }
            let (mut rest, tail) = self.parse_block_body_with_leading_exprs()?;
            let mut leading = Vec::with_capacity(rest.len() + 1);
            leading.push(expr);
            leading.append(&mut rest);
            Ok((leading, tail))
        } else {
            Ok((Vec::new(), expr))
        }
    }

    /// Parse a let-binding: `let <pattern> = <expr>; <body>`.
    ///
    /// Supports simple identifier bindings, `let _` (discard), `let mut x`
    /// (transparent in contract logic), and destructuring patterns like
    /// `let Name(a, b) = expr` or `let (a, b) = expr`. (#1513)
    ///
    /// Destructuring patterns are desugared into nested `Let` nodes using
    /// tuple field accessor logic functions.
    ///
    /// Also supports `let <pattern> = <expr> else { <diverging-block> };`
    /// (Rust's `let else`, RFC 3137). The else block is divergent in real
    /// Rust; in contract logic we desugar to a `Match` with the bound
    /// pattern leading to the rest of the block body and a wildcard arm
    /// carrying the diverging block. Soundness: trust-wp treats the else
    /// arm body as the value when the pattern does not match, mirroring
    /// the `if let ... else { ... }` desugaring (#1360).
    fn parse_let_binding(&mut self) -> Result<PureExpr, ParseError> {
        self.skip_whitespace();

        // `let mut x = ...` — consume `mut` transparently (no semantic
        // difference in contract logic)
        self.try_consume_keyword("mut");
        self.skip_whitespace();

        // Parse binding pattern: `_`, `x`, `Name(a, b)`, `(a, b)`, etc.
        let pattern = self.parse_pattern()?;

        // Optional type annotation: `let x: Type = ...`
        self.skip_whitespace();
        if self.try_consume(":") {
            self.consume_type_annotation()?;
        }

        self.skip_whitespace();
        if !self.try_consume("=") {
            return Err(self.error("expected '=' in let binding"));
        }

        let value = self.parse_expr()?;
        self.skip_whitespace();

        // `let <pat> = <expr> else { <block> };` — RFC 3137
        if self.try_consume_keyword("else") {
            return self.finish_let_else_binding(pattern, value);
        }

        if !self.try_consume(";") {
            return Err(self.error("expected ';' after let binding value"));
        }

        let body = self.parse_block_body()?;

        Self::desugar_let_pattern(pattern, value, body)
    }

    /// Finish parsing a `let <pat> = <expr> else { <block> };` form after the
    /// `else` keyword has been consumed.
    ///
    /// Desugars to `match value { pat => rest_of_block, _ => else_block }`,
    /// matching the established `if let ... else { ... }` desugaring (#1360).
    fn finish_let_else_binding(
        &mut self,
        pattern: Pattern,
        value: PureExpr,
    ) -> Result<PureExpr, ParseError> {
        self.skip_whitespace();
        if !self.try_consume("{") {
            return Err(self.error("expected '{' after 'else' in let-else binding"));
        }
        let else_body = self.parse_block_body()?;
        self.skip_whitespace();
        if !self.try_consume("}") {
            return Err(self.error("expected '}' to close let-else block"));
        }
        self.skip_whitespace();
        if !self.try_consume(";") {
            return Err(self.error("expected ';' after let-else binding"));
        }
        let rest = self.parse_block_body()?;
        Ok(PureExpr::Match {
            scrutinee: Arc::new(value),
            arms: vec![
                MatchArm {
                    pattern,
                    body: rest,
                },
                MatchArm {
                    pattern: Pattern::Wildcard,
                    body: else_body,
                },
            ],
        })
    }

    /// Desugar a let-binding pattern into `PureExpr` nodes.
    ///
    /// - `Binding(name)` → `Let { var: name, value, body }`
    /// - `Wildcard` → `body` (value discarded)
    /// - `Constructor { name, inner }` → nested `Let` with field accessors
    /// - `Tuple(elements)` → nested `Let` with tuple field accessors
    fn desugar_let_pattern(
        pattern: Pattern,
        value: PureExpr,
        body: PureExpr,
    ) -> Result<PureExpr, ParseError> {
        match pattern {
            Pattern::Wildcard => Ok(body),
            Pattern::Binding(name) => Ok(PureExpr::Let {
                var: name,
                value: Arc::new(value),
                body: Arc::new(body),
            }),
            Pattern::Alias { alias, pattern } => {
                let body = Self::desugar_let_pattern(*pattern, value.clone(), body)?;
                Ok(PureExpr::Let {
                    var: alias,
                    value: Arc::new(value),
                    body: Arc::new(body),
                })
            }
            Pattern::Constructor { inner: None, .. } => {
                // `let Name() = expr;` — unit constructor, no bindings
                Ok(body)
            }
            Pattern::Constructor {
                inner: Some(inner), ..
            } => {
                // `let Name(p1, p2, ...) = expr;`
                // inner is either a single pattern or Tuple of patterns
                let sub_patterns = match *inner {
                    Pattern::Tuple(pats) => pats,
                    single => vec![single],
                };
                Self::desugar_field_bindings(sub_patterns, &value, body)
            }
            Pattern::Tuple(elements) => {
                // `let (a, b) = expr;`
                Self::desugar_field_bindings(elements, &value, body)
            }
            Pattern::Literal(_) => {
                // Literal patterns in let-bindings don't make sense in
                // contract logic but we don't error — just discard.
                Ok(body)
            }
        }
    }

    /// Desugar a list of sub-patterns at field positions into nested `Let`
    /// nodes. Each `Binding(name)` at position `i` produces:
    /// `let name = __trust_wp_tuple_fieldI(value); ...`
    fn desugar_field_bindings(
        patterns: Vec<Pattern>,
        value: &PureExpr,
        body: PureExpr,
    ) -> Result<PureExpr, ParseError> {
        // Build from innermost outward: wrap body in Let nodes from last to first
        let mut result = body;
        for (i, pat) in patterns.into_iter().enumerate().rev() {
            match pat {
                Pattern::Wildcard | Pattern::Literal(_) => {
                    // Skip this field — no binding needed
                }
                Pattern::Binding(name) => {
                    let field_accessor = PureExpr::LogicFnCall {
                        name: tuple_field_logic_fn_name(i),
                        args: vec![value.clone()],
                    };
                    result = PureExpr::Let {
                        var: name,
                        value: Arc::new(field_accessor),
                        body: Arc::new(result),
                    };
                }
                Pattern::Constructor { .. } | Pattern::Tuple(_) | Pattern::Alias { .. } => {
                    // Nested destructuring: recursively desugar
                    let field_accessor = PureExpr::LogicFnCall {
                        name: tuple_field_logic_fn_name(i),
                        args: vec![value.clone()],
                    };
                    result = Self::desugar_let_pattern(pat, field_accessor, result)?;
                }
            }
        }
        Ok(result)
    }

    /// Skip `//` line comments (common in Creusot logic function bodies).
    fn skip_line_comments(&mut self) {
        loop {
            self.skip_whitespace();
            let checkpoint_pos = self.position;
            let checkpoint_chars = self.chars.clone();
            if self.try_consume("//") {
                // Consume until end of line
                while let Some(c) = self.peek() {
                    if c == '\n' {
                        self.advance();
                        break;
                    }
                    self.advance();
                }
            } else {
                self.position = checkpoint_pos;
                self.chars = checkpoint_chars;
                break;
            }
        }
    }
}
