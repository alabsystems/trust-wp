// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Block expression parsing: block bodies, let-bindings, pattern desugaring,
//! top-level body parsing, and line-comment skipping.

use std::sync::Arc;

use super::super::{
    helpers::borrows::{match_through_reference, peel_reference_patterns},
    ContractParser, ParseError, WrittenTypeSite,
};
use crate::formula::{
    internal::tuple_lowering::{tuple_field_logic_fn_name, tuple_logic_fn_name},
    parse_named_struct_ctor, MatchArm, Pattern, PureExpr,
};

impl ContractParser<'_> {
    /// True when the expression just parsed (starting at `expr_start`) is a
    /// block-like expression statement — `match .. { .. }`, `if .. { .. }` or
    /// `{ .. }` — and more of the block follows. Rust lets such statements
    /// omit the `;` (`match n { A(m) => f(m), } g(n)`); like any expression
    /// statement in spec context its (unit) value is discarded.
    fn ends_block_like_statement(&mut self, expr_start: usize) -> bool {
        if matches!(self.peek(), None | Some('}')) {
            return false;
        }
        let text = self.input[expr_start..self.position].trim();
        if !text.ends_with('}') {
            return false;
        }
        let starts_with_keyword = |kw: &str| {
            text.strip_prefix(kw).is_some_and(|rest| {
                rest.chars()
                    .next()
                    .is_some_and(|c| !(c.is_ascii_alphanumeric() || c == '_'))
            })
        };
        text.starts_with('{') || starts_with_keyword("match") || starts_with_keyword("if")
    }

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
        let statement_start = self.position;
        if self.try_consume_keyword("use") {
            while let Some(c) = self.peek() {
                self.advance();
                if c == ';' {
                    break;
                }
            }
            self.note_discarded_statement(statement_start);
            return self.parse_top_level_body();
        }

        // Let-binding: `let <ident> = <expr>; <body>`
        if self.try_consume_keyword("let") {
            // Let bindings call parse_block_body for their continuation;
            // but at top-level we need to handle end-of-input. For now,
            // fall back to the brace-based let binding (it will work as
            // long as there are further expressions after the semicolon).
            return self.parse_let_binding_top_level(statement_start);
        }

        // Expression — could be a statement (followed by `;`) or trailing expr
        let expr_start = self.position;
        let expr = self.parse_expr()?;
        self.skip_whitespace();
        self.skip_line_comments();

        if self.try_consume(";") || self.ends_block_like_statement(expr_start) {
            self.skip_whitespace();
            self.skip_line_comments();
            if !self.preserve_stmt_exprs {
                self.note_discarded_statement(expr_start);
            }
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

        let statement_start = self.position;
        if self.try_consume_keyword("use") {
            while let Some(c) = self.peek() {
                self.advance();
                if c == ';' {
                    break;
                }
            }
            self.note_discarded_statement(statement_start);
            return self.parse_top_level_body_with_leading_exprs();
        }

        if self.try_consume_keyword("let") {
            return Ok((
                Vec::new(),
                self.parse_let_binding_top_level(statement_start)?,
            ));
        }

        let expr_start = self.position;
        let expr = self.parse_expr()?;
        self.skip_whitespace();
        self.skip_line_comments();

        if self.try_consume(";") || self.ends_block_like_statement(expr_start) {
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
    fn parse_let_binding_top_level(&mut self, let_start: usize) -> Result<PureExpr, ParseError> {
        let (pattern, value) = self.parse_let_head()?;

        // `let <pat> = <expr> else { <block> };` at top level
        if self.try_consume_keyword("else") {
            return self.finish_let_else_binding_top_level(pattern, value);
        }

        if !self.try_consume(";") {
            return Err(self.error("expected ';' after let binding value"));
        }
        self.check_irrefutable_let(&pattern, let_start)?;

        let body = self.parse_top_level_body()?;

        self.desugar_let_statement(pattern, value, body)
    }

    /// Parse `[mut] <pattern> [: <type>] = <value>` after `let`, the value
    /// read at the annotation's sort ([`Self::ascribe`]).
    fn parse_let_head(&mut self) -> Result<(Pattern, PureExpr), ParseError> {
        self.skip_whitespace();

        // `let mut x = ...` — consume `mut` transparently (no semantic
        // difference in contract logic) (#1513)
        if self.try_consume_keyword("mut") {
            self.pattern_forms
                .push(super::super::PatternForm::MutBinding);
        }
        self.skip_whitespace();

        // Parse binding pattern: `_`, `x`, `Name(a, b)`, `(a, b)`, etc.
        let pattern = self.parse_pattern()?;

        // Optional type annotation: `let x: Type = ...`
        self.skip_whitespace();
        let annotation = if self.try_consume(":") {
            self.skip_whitespace();
            let at = self.position;
            Some((
                self.consume_written_type_text(WrittenTypeSite::LetBinding)?,
                at,
            ))
        } else {
            None
        };

        self.skip_whitespace();
        if !self.try_consume("=") {
            return Err(self.error("expected '=' in let binding"));
        }

        let value = self.parse_expr()?;
        let value = match annotation {
            Some(((sort, text), at)) => {
                self.ascribe(value, sort.as_ref(), &text, "`let` annotation", at)?
            }
            None => value,
        };
        self.skip_whitespace();
        Ok((pattern, value))
    }

    /// A plain `let` (no `else`) whose pattern can fail to match is refused:
    /// rustc rejects it, and the desugaring would drop the test. One whose
    /// pattern binds nothing (`let _ = e;`, `let Unit = e;`) drops the whole
    /// statement, which is recorded.
    pub(in crate::contract_parser) fn check_irrefutable_let(
        &mut self,
        pattern: &Pattern,
        let_start: usize,
    ) -> Result<(), ParseError> {
        fn has_literal(pattern: &Pattern) -> bool {
            match pattern {
                Pattern::Literal(_) => true,
                Pattern::Wildcard | Pattern::Binding(_) => false,
                Pattern::Constructor { inner, .. } => inner.as_deref().is_some_and(has_literal),
                Pattern::Alias { pattern, .. } => has_literal(pattern),
                Pattern::Tuple(elements) => elements.iter().any(has_literal),
            }
        }
        if has_literal(pattern) {
            return Err(ParseError {
                message: "a literal pattern in a `let` without `else` is refutable; rustc rejects \
                          it, and the binding would drop the test"
                    .to_string(),
                position: let_start,
            });
        }
        if !self.preserve_stmt_exprs
            && matches!(
                peel_reference_patterns(pattern),
                Pattern::Wildcard | Pattern::Constructor { inner: None, .. }
            )
        {
            self.note_discarded_statement(let_start);
        }
        Ok(())
    }

    /// Desugar a plain `let` statement. One whose pattern binds nothing has
    /// no binding to carry its value, so the desugaring drops the value; where
    /// statements are preserved (a logic function body, whose calls owe their
    /// preconditions: Creusot's vcgen reads `let _ = e; rest` through `e`,
    /// logic_fn_callee_precondition_wildcard_let.rs) the value is kept as a
    /// statement instead.
    fn desugar_let_statement(
        &mut self,
        pattern: Pattern,
        value: PureExpr,
        body: PureExpr,
    ) -> Result<PureExpr, ParseError> {
        fn binds(pattern: &Pattern) -> bool {
            match pattern {
                Pattern::Binding(_) | Pattern::Alias { .. } => true,
                Pattern::Wildcard | Pattern::Literal(_) => false,
                Pattern::Constructor { inner, .. } => inner.as_deref().is_some_and(binds),
                Pattern::Tuple(elements) => elements.iter().any(binds),
            }
        }
        if self.preserve_stmt_exprs && !binds(&pattern) {
            return Ok(self.wrap_stmt_expr(value, body));
        }
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
        let statement_start = self.position;
        if self.try_consume_keyword("use") {
            // Consume everything until the semicolon
            while let Some(c) = self.peek() {
                self.advance();
                if c == ';' {
                    break;
                }
            }
            self.note_discarded_statement(statement_start);
            return self.parse_block_body();
        }

        // Let-binding: `let <ident> = <expr>; <body>`
        if self.try_consume_keyword("let") {
            return self.parse_let_binding(statement_start);
        }

        // Expression — could be a statement (followed by `;`) or trailing expr
        let expr_start = self.position;
        let expr = self.parse_expr()?;
        self.skip_whitespace();
        self.skip_line_comments();

        if self.try_consume(";") || self.ends_block_like_statement(expr_start) {
            self.skip_whitespace();
            self.skip_line_comments();
            if !self.preserve_stmt_exprs {
                self.note_discarded_statement(expr_start);
            }
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

        let statement_start = self.position;
        if self.try_consume_keyword("use") {
            while let Some(c) = self.peek() {
                self.advance();
                if c == ';' {
                    break;
                }
            }
            self.note_discarded_statement(statement_start);
            return self.parse_block_body_with_leading_exprs();
        }

        if self.try_consume_keyword("let") {
            return Ok((Vec::new(), self.parse_let_binding(statement_start)?));
        }

        let expr_start = self.position;
        let expr = self.parse_expr()?;
        self.skip_whitespace();
        self.skip_line_comments();

        if self.try_consume(";") || self.ends_block_like_statement(expr_start) {
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
    fn parse_let_binding(&mut self, let_start: usize) -> Result<PureExpr, ParseError> {
        let (pattern, value) = self.parse_let_head()?;

        // `let <pat> = <expr> else { <block> };` — RFC 3137
        if self.try_consume_keyword("else") {
            return self.finish_let_else_binding(pattern, value);
        }

        if !self.try_consume(";") {
            return Err(self.error("expected ';' after let binding value"));
        }
        self.check_irrefutable_let(&pattern, let_start)?;

        let body = self.parse_block_body()?;

        self.desugar_let_statement(pattern, value, body)
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
    /// - `Alias { alias, pattern }` → `let alias = value`, then `pattern`
    ///   against `alias`
    /// - a reference pattern → its inner pattern against `*value` (`&p`,
    ///   `&mut p`) or against a borrow of `value` (`ref x`, `ref mut x`,
    ///   `ref x @ p`)
    /// - a NAMED-FIELD `Constructor` (`S { a: aa, .. }`) → the single-arm
    ///   `Match` a `match value { pattern => body }` would produce
    /// - any other `Constructor { name, inner }` → nested `Let` with field accessors
    /// - `Tuple(elements)` → nested `Let` with tuple field accessors
    pub(in crate::contract_parser) fn desugar_let_pattern(
        pattern: Pattern,
        value: PureExpr,
        body: PureExpr,
    ) -> Result<PureExpr, ParseError> {
        if let Some((inner, value)) = match_through_reference(&pattern, value.clone()) {
            return Self::desugar_let_pattern(inner, value, body);
        }
        if let Pattern::Constructor { name, .. } = &pattern {
            if parse_named_struct_ctor(name).is_some() {
                // A named-field pattern's field names are an INSTRUCTION to the
                // driver — place each sub-pattern at the index its declaration
                // gives it — and only a declaration can carry it out. Lowering
                // the binding to positional field reads here would discard that
                // instruction before any declaration is consulted, so `aa` in
                // `let S { a: aa, b: _ } = s` would denote whichever field is
                // declared FIRST rather than the field named `a`. Keeping the
                // pattern whole, exactly as `let ... else` does, hands it to
                // the same placement pass and the same encoder gate a `match`
                // arm reaches.
                return Ok(PureExpr::Match {
                    scrutinee: Arc::new(value),
                    arms: vec![MatchArm { pattern, body }],
                });
            }
        }
        match pattern {
            Pattern::Wildcard => Ok(body),
            Pattern::Binding(name) => Ok(PureExpr::Let {
                var: name,
                value: Arc::new(value),
                body: Arc::new(body),
            }),
            // The subpattern matches the value the alias names: the value
            // is read once, before any name the subpattern binds. Matched
            // against `value` itself, `let x @ y = x + 1` read `y` as the
            // new `x` plus one.
            Pattern::Alias { alias, pattern } => {
                let alias_value = PureExpr::Var(alias.clone(), None);
                let body = Self::desugar_let_pattern(*pattern, alias_value, body)?;
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
                // `let Name(p1, p2, ...) = expr;` — a tuple-style constructor,
                // whose fields have no names: written position IS declared
                // position, so a positional read is the declaration's answer.
                // (A named-field constructor never reaches this arm.)
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
            // Refused before desugaring (`check_irrefutable_let`); a
            // `let ... else` keeps its pattern in a `Match`.
            Pattern::Literal(_) => Err(ParseError {
                message: "a literal pattern in a `let` without `else` is refutable".to_string(),
                position: 0,
            }),
        }
    }

    /// Desugar a list of sub-patterns at field positions into nested `Let`
    /// nodes. Each `Binding(name)` at position `i` produces:
    /// `let name = __trust_wp_tuple_fieldI(value); ...`
    ///
    /// Each field's `let` reads `value` inside the fields bound before it, so
    /// a `value` that reads a name the patterns bind is first bound to a
    /// name of its own: `let (a, b) = (b, a)` read `b` as the new `a`.
    fn desugar_field_bindings(
        patterns: Vec<Pattern>,
        value: &PureExpr,
        body: PureExpr,
    ) -> Result<PureExpr, ParseError> {
        let captured =
            value.any_free_var(|name, _| patterns.iter().any(|pattern| pattern.binds_name(name)));
        if captured {
            let taken = |name: &str| {
                value.any_free_var(|free, _| free == name)
                    || body.any_free_var(|free, _| free == name)
                    || patterns.iter().any(|pattern| pattern.binds_name(name))
            };
            let mut index = 0usize;
            let scrutinee = loop {
                let name = format!("$let{index}");
                if !taken(&name) {
                    break name;
                }
                index += 1;
            };
            let scrutinee_value = PureExpr::Var(scrutinee.clone(), None);
            let body = Self::desugar_field_bindings(patterns, &scrutinee_value, body)?;
            return Ok(PureExpr::Let {
                var: scrutinee,
                value: Arc::new(value.clone()),
                body: Arc::new(body),
            });
        }
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

#[cfg(test)]
mod block_like_statement_tests {
    use crate::contract_parser::parse_contract_body;

    #[test]
    fn match_statement_without_semicolon_then_tail() {
        let parsed = parse_contract_body("{ match n { Never(m) => sneak(*m), } sneak(n) }");
        assert!(parsed.is_ok(), "{parsed:?}");
        let parsed = parse_contract_body("{ if b { f(x) } else { g(x) } h(x) }");
        assert!(parsed.is_ok(), "{parsed:?}");
    }

    #[test]
    fn non_block_like_expressions_still_need_a_semicolon() {
        assert!(parse_contract_body("{ f(x) g(x) }").is_err());
        assert!(parse_contract_body("{ x + y z }").is_err());
    }
}
