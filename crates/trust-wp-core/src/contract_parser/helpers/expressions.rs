// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compound expression parsing: match, if-else, closures, struct literals,
//! and argument lists.

use std::sync::Arc;

use super::super::{ContractParser, ParseError};
use crate::formula::{
    internal::tuple_lowering::tuple_logic_fn_name, ExprSort, MatchArm, Pattern, PureExpr,
};

impl ContractParser<'_> {
    /// Parse a match expression: `match expr { pattern => body, ... }`
    pub(in crate::contract_parser) fn parse_match(&mut self) -> Result<PureExpr, ParseError> {
        self.skip_whitespace();

        // Parse the scrutinee expression (allow full expression, not just unary)
        let scrutinee = self.parse_expr()?;

        self.skip_whitespace();

        // Expect '{'
        if !self.try_consume("{") {
            return Err(self.error("expected '{' after match expression"));
        }

        let mut arms = Vec::new();

        loop {
            self.skip_whitespace();

            // Check for closing brace
            if self.peek() == Some('}') {
                break;
            }

            // Parse pattern(s) — or-patterns `pat1 | pat2 | pat3` desugar
            // into separate arms sharing the same body (#658).
            let mut patterns = vec![self.parse_pattern()?];
            loop {
                self.skip_whitespace();
                if self.try_consume("|") {
                    self.skip_whitespace();
                    patterns.push(self.parse_pattern()?);
                } else {
                    break;
                }
            }

            // Reject integer-literal patterns inside match arms. Pearlite
            // does not support matching integer literals (Creusot rejects
            // `match v { (0, _, _) | ... => 1, _ => 0 }` with: "Pattern
            // matching literals on Int are unsupported by Pearlite. Consider
            // using if-then-else instead.")
            // Bool literal patterns remain supported.
            for pattern in &patterns {
                if pattern_contains_int_literal(pattern) {
                    return Err(self.error(
                        "Pattern matching literals on Int are unsupported by Pearlite.                          Consider using if-then-else instead.",
                    ));
                }
            }

            self.skip_whitespace();

            // Expect '=>'
            if !self.try_consume("=>") {
                return Err(self.error("expected '=>' after pattern"));
            }

            self.skip_whitespace();

            // Detect brace-delimited arm bodies where trailing comma is optional:
            //   `pattern => { ... }`         — block body
            //   `pattern => if c { } else {}` — if-else body
            //   `pattern => match x { .. }`  — nested match body
            // Matches Rust syntax: Creusot's `requires_terminator()` pattern.
            let remaining = &self.input[self.position..];
            let body_is_braced = self.peek() == Some('{')
                || remaining.starts_with("if")
                    && !remaining[2..]
                        .chars()
                        .next()
                        .is_some_and(Self::is_ident_continue)
                || remaining.starts_with("match")
                    && !remaining[5..]
                        .chars()
                        .next()
                        .is_some_and(Self::is_ident_continue);
            let body = self.parse_expr()?;

            for pattern in patterns {
                arms.push(MatchArm {
                    pattern,
                    body: body.clone(),
                });
            }

            self.skip_whitespace();

            // Comma required after non-brace bodies; optional after brace-delimited bodies
            if body_is_braced {
                self.try_consume(",");
            } else if !self.try_consume(",") {
                break;
            }
        }

        self.skip_whitespace();

        // Expect '}'
        if !self.try_consume("}") {
            return Err(self.error("expected '}' to close match expression"));
        }

        if arms.is_empty() {
            return Err(self.error("match expression must have at least one arm"));
        }

        Ok(PureExpr::Match {
            scrutinee: Arc::new(scrutinee),
            arms,
        })
    }

    /// Parse an if-then-else expression: `if cond { then } else { else }`
    ///
    /// Called after consuming `if` keyword.
    ///
    /// # Syntax
    ///
    /// ```text
    /// if condition { then_expr } else { else_expr }
    /// ```
    ///
    /// Both branches must use braces. The `else` clause is optional — when
    /// omitted, the expression evaluates to unit (`()`), matching Rust semantics
    /// for `if cond { body }` without `else`.
    pub(in crate::contract_parser) fn parse_if_else(&mut self) -> Result<PureExpr, ParseError> {
        self.skip_whitespace();

        // Parse the condition expression (stop at '{')
        let cond = self.parse_if_condition()?;

        self.skip_whitespace();

        // Expect '{' for then branch
        if !self.try_consume("{") {
            return Err(self.error("expected '{' after if condition"));
        }

        // Parse then branch as a block body (handles statements like `f();`)
        let then_expr = self.parse_block_body()?;

        self.skip_whitespace();

        // Expect '}' to close then branch
        if !self.try_consume("}") {
            return Err(self.error("expected '}' to close if then branch"));
        }

        self.skip_whitespace();

        // Check for `if let` sentinel — desugar to Match (#1360)
        if let PureExpr::MethodCall {
            receiver,
            method,
            args,
        } = &cond
        {
            if method == "__trust_wp_if_let" {
                if let Some(PureExpr::Match { arms, .. }) = args.first() {
                    if let Some(arm) = arms.first() {
                        let scrutinee = receiver.clone();
                        let pattern = arm.pattern.clone();

                        // Optional 'else' clause
                        let else_expr = if self.try_consume_keyword("else") {
                            self.skip_whitespace();
                            self.parse_else_branch()?
                        } else {
                            // No else: `if let Pat = expr { body }` → unit for non-matching
                            PureExpr::LogicFnCall {
                                name: tuple_logic_fn_name(0),
                                args: vec![],
                            }
                        };

                        return Ok(PureExpr::Match {
                            scrutinee,
                            arms: vec![
                                MatchArm {
                                    pattern,
                                    body: then_expr,
                                },
                                MatchArm {
                                    pattern: Pattern::Wildcard,
                                    body: else_expr,
                                },
                            ],
                        });
                    }
                }
            }
        }

        // Regular if-else (non-let)

        // Optional 'else' clause
        if !self.try_consume_keyword("else") {
            // No else: `if cond { body }` evaluates to unit
            let unit = PureExpr::LogicFnCall {
                name: tuple_logic_fn_name(0),
                args: vec![],
            };
            return Ok(PureExpr::Ite(
                Arc::new(cond),
                Arc::new(then_expr),
                Arc::new(unit),
            ));
        }

        self.skip_whitespace();

        let else_expr = self.parse_else_branch()?;

        Ok(PureExpr::Ite(
            Arc::new(cond),
            Arc::new(then_expr),
            Arc::new(else_expr),
        ))
    }

    /// Parse the else branch of an if expression (after `else` keyword consumed).
    fn parse_else_branch(&mut self) -> Result<PureExpr, ParseError> {
        self.skip_whitespace();

        // else-if chain: `else if cond2 { ... }`
        if self.try_consume_keyword("if") {
            return self.parse_if_else();
        }

        // Expect '{' for else branch
        if !self.try_consume("{") {
            return Err(self.error("expected '{' after else"));
        }

        // Parse else branch as a block body
        let expr = self.parse_block_body()?;

        self.skip_whitespace();

        // Expect '}' to close else branch
        if !self.try_consume("}") {
            return Err(self.error("expected '}' to close else branch"));
        }
        Ok(expr)
    }

    /// Parse the condition part of an if expression (up to the '{').
    ///
    /// Handles both regular conditions and `if let` patterns (#1360):
    /// - `if cond { ... }` — normal boolean condition
    /// - `if let Pattern = expr { ... }` — desugared to internal IfLet representation
    ///
    /// Mirrors Rust's `RESTRICTION_NO_STRUCT_LITERAL`: struct literal syntax
    /// (`Ident { field: val }`) is suppressed so that `if x == NULL { body }`
    /// does not misparse `NULL {` as a struct literal constructor. (#2331)
    fn parse_if_condition(&mut self) -> Result<PureExpr, ParseError> {
        self.skip_whitespace();

        // Check for `if let` pattern
        if self.try_consume_keyword("let") {
            return self.parse_if_let_condition();
        }

        let prev = self.no_struct_literals;
        self.no_struct_literals = true;
        let result = self.parse_expr();
        self.no_struct_literals = prev;
        result
    }

    /// Parse `let Pattern = expr` after the `let` keyword has been consumed.
    ///
    /// Returns a synthetic boolean condition that will be used by `parse_if_else`
    /// to build the if-then-else. The actual desugaring into a match expression
    /// happens in `parse_if_else` when it detects the IfLetCondition marker.
    ///
    /// Desugars `if let Pat = scrutinee { then } else { else }` into:
    /// ```text
    /// match scrutinee { Pat => then, _ => else }
    /// ```
    fn parse_if_let_condition(&mut self) -> Result<PureExpr, ParseError> {
        self.skip_whitespace();
        let pattern = self.parse_pattern()?;
        self.skip_whitespace();
        if !self.try_consume("=") {
            return Err(self.error("expected '=' after if-let pattern"));
        }
        self.skip_whitespace();
        let prev = self.no_struct_literals;
        self.no_struct_literals = true;
        let scrutinee = self.parse_expr()?;
        self.no_struct_literals = prev;

        // Return a sentinel that parse_if_else will detect and convert to Match.
        // We use a MethodCall with a reserved name that cannot collide with user code.
        Ok(PureExpr::MethodCall {
            receiver: Arc::new(scrutinee),
            method: "__trust_wp_if_let".to_string(),
            args: vec![PureExpr::Match {
                scrutinee: Arc::new(PureExpr::Bool(true)), // placeholder
                arms: vec![MatchArm {
                    pattern,
                    body: PureExpr::Bool(true),
                }],
            }],
        })
    }

    /// Parse a closure expression: `|param1: Type1, param2: Type2| body`
    ///
    /// Called when `|` is encountered in primary expression position (not `||`).
    /// Closure parameters may have optional type annotations, which are consumed
    /// and mapped to `ExprSort` where possible (same as quantifier bindings).
    ///
    /// Also handles destructuring parameters like `|(x, y)| body` (#1513):
    /// tuple patterns are flattened into individual named parameters.
    ///
    /// Returns `PureExpr::Closure { params, body }`.
    pub(in crate::contract_parser) fn parse_closure(&mut self) -> Result<PureExpr, ParseError> {
        // Consume the opening `|`
        if !self.try_consume("|") {
            return Err(self.error("expected '|' to start closure"));
        }

        let mut params = Vec::new();

        self.skip_whitespace();

        // Handle `|| body` (zero-parameter closure)
        if self.peek() == Some('|') {
            self.advance(); // consume closing `|`
        } else {
            // Parse comma-separated parameter bindings: `name: Type, ...`
            // Also accepts destructuring patterns: `|(x, y)| body` (#1513)
            loop {
                self.skip_whitespace();

                // Check for tuple destructuring pattern: `(a, b)`
                if self.peek() == Some('(') {
                    let pat = self.parse_pattern()?;
                    // Flatten tuple/binding patterns into named params
                    Self::flatten_pattern_to_params(&pat, &mut params);
                } else {
                    let name = self
                        .try_parse_simple_identifier()
                        .ok_or_else(|| self.error("expected parameter name in closure"))?;

                    self.skip_whitespace();

                    // Optional type annotation: `: Type`
                    let sort = if self.try_consume(":") {
                        self.skip_whitespace();
                        self.consume_type_annotation()?
                    } else {
                        None
                    };

                    params.push((name, sort));
                }

                self.skip_whitespace();

                if self.try_consume(",") {
                    continue;
                }
                break;
            }

            self.skip_whitespace();

            // Expect closing `|`
            if !self.try_consume("|") {
                return Err(self.error("expected '|' to close closure parameters"));
            }
        }

        self.skip_whitespace();

        // Parse the closure body (a single expression)
        let body = self.parse_expr()?;

        Ok(PureExpr::Closure {
            params,
            body: Arc::new(body),
        })
    }

    /// Flatten a pattern into closure parameter names.
    ///
    /// Used to desugar destructuring closure parameters like `|(x, y)|` into
    /// flat parameter lists `[("x", None), ("y", None)]`. Wildcards are
    /// converted to synthetic `_` names. (#1513)
    fn flatten_pattern_to_params(pat: &Pattern, out: &mut Vec<(String, Option<ExprSort>)>) {
        match pat {
            Pattern::Binding(name) => out.push((name.clone(), None)),
            Pattern::Alias { alias, pattern } => {
                out.push((alias.clone(), None));
                Self::flatten_pattern_to_params(pattern, out);
            }
            Pattern::Tuple(elements) => {
                for elem in elements {
                    Self::flatten_pattern_to_params(elem, out);
                }
            }
            Pattern::Wildcard => out.push(("_".to_string(), None)),
            Pattern::Constructor { inner, .. } => {
                if let Some(inner_pat) = inner {
                    Self::flatten_pattern_to_params(inner_pat, out);
                }
            }
            Pattern::Literal(_) => {
                // Literal in closure param position — unusual but not a parse error
                out.push(("_".to_string(), None));
            }
        }
    }

    /// Parse a struct literal expression: `TypeName { field: expr, ... }`
    ///
    /// Called after the type name has been parsed and `{` has been peeked.
    /// Desugars to `LogicFnCall { name: "TypeName{field1,field2}", args: [expr1, expr2] }`
    /// with field names encoded in the constructor name so the driver's rewrite
    /// pass can reorder args to match the struct definition's canonical field
    /// order. Shorthand `{ field }` is equivalent to `{ field: field }`. (#1819)
    ///
    /// Also handles struct update syntax `{ field, ..base }` (#1513):
    /// the `..base` expression is parsed and appended as the last argument.
    /// Downstream encoders treat the extra arg as a base-object reference.
    /// When struct update syntax is present, field names are NOT encoded (the
    /// base-object makes positional reordering ambiguous).
    pub(in crate::contract_parser) fn parse_struct_literal(
        &mut self,
        name: String,
    ) -> Result<PureExpr, ParseError> {
        if !self.try_consume("{") {
            return Err(self.error("expected '{' in struct literal"));
        }
        self.skip_whitespace();

        let mut field_names = Vec::new();
        let mut args = Vec::new();
        let mut has_base_update = false;

        while self.peek() != Some('}') {
            // Handle `..base` struct update syntax — consume the base
            // expression and stop parsing fields. (#1513)
            if self.try_consume("..") {
                self.skip_whitespace();
                let base = self.parse_expr()?;
                args.push(base);
                has_base_update = true;
                self.skip_whitespace();
                // Allow trailing comma after `..base`
                self.try_consume(",");
                self.skip_whitespace();
                break;
            }

            // Parse field: `name: expr` or shorthand `name`
            let field_name = self
                .try_parse_simple_identifier()
                .ok_or_else(|| self.error("expected field name in struct literal"))?;
            self.skip_whitespace();

            let value = if self.try_consume(":") {
                self.skip_whitespace();
                self.parse_expr()?
            } else {
                // Shorthand: `{ b }` means `{ b: b }`
                PureExpr::Var(field_name.clone(), None)
            };
            field_names.push(field_name);
            args.push(value);

            self.skip_whitespace();
            if !self.try_consume(",") {
                break;
            }
            self.skip_whitespace();
        }

        if !self.try_consume("}") {
            return Err(self.error("expected '}' to close struct literal"));
        }

        // Encode field names into the constructor name so the driver can
        // reorder to canonical field order. Skip encoding when struct update
        // syntax is present (base-object makes reordering ambiguous).
        let ctor_name = if has_base_update || field_names.is_empty() {
            name
        } else {
            crate::formula::named_struct_ctor_name(&name, &field_names)
        };

        Ok(PureExpr::LogicFnCall {
            name: ctor_name,
            args,
        })
    }

    /// Parse comma-separated argument list (without parens)
    pub(in crate::contract_parser) fn parse_argument_list(
        &mut self,
    ) -> Result<Vec<PureExpr>, ParseError> {
        self.parse_argument_list_with_closing(')')
    }

    /// Parse comma-separated arguments until the given closing delimiter.
    pub(in crate::contract_parser) fn parse_argument_list_with_closing(
        &mut self,
        closing: char,
    ) -> Result<Vec<PureExpr>, ParseError> {
        let mut args = Vec::new();
        self.skip_whitespace();
        if self.peek() == Some(closing) {
            return Ok(args);
        }
        loop {
            args.push(self.parse_expr()?);
            self.skip_whitespace();
            if self.peek() == Some(closing) {
                break;
            }
            if !self.try_consume(",") {
                return Err(self.error(&format!("expected ',' or '{closing}' in argument list")));
            }
            self.skip_whitespace();
            if self.peek() == Some(closing) {
                break;
            }
        }
        Ok(args)
    }
}

/// Returns true if a pattern (recursively) contains an integer literal —
/// Pearlite does not support integer-literal pattern matching, so trust-wp
/// rejects such matches the same way Creusot does (see
/// `reference/creusot/tests/should_fail/unsupported/1827/test3.rs` and
/// `test4.rs`).
fn pattern_contains_int_literal(pattern: &Pattern) -> bool {
    match pattern {
        Pattern::Literal(PureExpr::Int(_)) => true,
        Pattern::Literal(_) | Pattern::Wildcard | Pattern::Binding(_) => false,
        Pattern::Constructor {
            inner: Some(inner), ..
        } => pattern_contains_int_literal(inner),
        Pattern::Constructor { inner: None, .. } => false,
        Pattern::Alias { pattern, .. } => pattern_contains_int_literal(pattern),
        Pattern::Tuple(elements) => elements.iter().any(pattern_contains_int_literal),
    }
}
