// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::sync::Arc;

use super::{ContractParser, ParseError};
use crate::formula::{
    internal::tuple_lowering::{
        tuple_field_logic_fn_name, tuple_logic_fn_name, NAMED_FIELD_LOGIC_FN_PREFIX,
    },
    BinOp, PureExpr, SourceSpan, SpannedExpr, UnOp,
};

impl ContractParser<'_> {
    pub(super) fn span(&self, start: usize) -> SourceSpan {
        SourceSpan::from_contract(start, self.position)
    }

    /// Parse an expression with span tracking (handles all operators by precedence)
    pub(super) fn parse_expr_spanned(&mut self) -> Result<SpannedExpr, ParseError> {
        self.parse_implies_spanned()
    }

    /// Parse ==> (implication, lowest precedence) with span tracking
    pub(super) fn parse_implies_spanned(&mut self) -> Result<SpannedExpr, ParseError> {
        let start = self.position;
        let mut left = self.parse_or_spanned()?;
        // Implication is right-associative: a ==> b ==> c means a ==> (b ==> c)
        if self.try_consume("==>") {
            let right = self.parse_implies_spanned()?;
            let expr = PureExpr::BinOp(Arc::new(left.expr), BinOp::Implies, Arc::new(right.expr));
            left = SpannedExpr::new(expr, self.span(start));
        }
        Ok(left)
    }

    /// Parse || with span tracking
    pub(super) fn parse_or_spanned(&mut self) -> Result<SpannedExpr, ParseError> {
        let start = self.position;
        let mut left = self.parse_and_spanned()?;
        while self.try_consume("||") {
            let right = self.parse_and_spanned()?;
            let expr = PureExpr::BinOp(Arc::new(left.expr), BinOp::Or, Arc::new(right.expr));
            left = SpannedExpr::new(expr, self.span(start));
        }
        Ok(left)
    }

    /// Parse && with span tracking
    pub(super) fn parse_and_spanned(&mut self) -> Result<SpannedExpr, ParseError> {
        let start = self.position;
        let mut left = self.parse_equality_spanned()?;
        while self.try_consume("&&") {
            let right = self.parse_equality_spanned()?;
            let expr = PureExpr::BinOp(Arc::new(left.expr), BinOp::And, Arc::new(right.expr));
            left = SpannedExpr::new(expr, self.span(start));
        }
        Ok(left)
    }

    /// Parse == and != with span tracking
    pub(super) fn parse_equality_spanned(&mut self) -> Result<SpannedExpr, ParseError> {
        let start = self.position;
        let mut left = self.parse_comparison_spanned()?;
        loop {
            // Check for == but not ==> (which has lower precedence)
            if self.try_consume_eq_not_implies() {
                let right = self.parse_comparison_spanned()?;
                let expr = PureExpr::BinOp(Arc::new(left.expr), BinOp::Eq, Arc::new(right.expr));
                left = SpannedExpr::new(expr, self.span(start));
            } else if self.try_consume("!=") {
                let right = self.parse_comparison_spanned()?;
                let expr = PureExpr::BinOp(Arc::new(left.expr), BinOp::Ne, Arc::new(right.expr));
                left = SpannedExpr::new(expr, self.span(start));
            } else {
                break;
            }
        }
        Ok(left)
    }

    /// Parse <, <=, >, >= with span tracking
    pub(super) fn parse_comparison_spanned(&mut self) -> Result<SpannedExpr, ParseError> {
        let start = self.position;
        let first = self.parse_bitwise_or_spanned()?;
        let Some(first_op) = self.try_parse_comparison_op() else {
            return Ok(first);
        };
        let first_right = self.parse_bitwise_or_spanned()?;

        // Build the first comparison directly, then fold chained operators with AND.
        let mut expr = PureExpr::BinOp(
            Arc::new(first.expr),
            first_op,
            Arc::new(first_right.expr.clone()),
        );
        let mut prev_rhs = first_right.expr;

        while let Some(op) = self.try_parse_comparison_op() {
            let right = self.parse_bitwise_or_spanned()?;
            let cmp = PureExpr::BinOp(Arc::new(prev_rhs.clone()), op, Arc::new(right.expr.clone()));
            expr = PureExpr::BinOp(Arc::new(expr), BinOp::And, Arc::new(cmp));
            prev_rhs = right.expr;
        }
        Ok(SpannedExpr::new(expr, self.span(start)))
    }

    /// Parse bitwise OR (`|`) with span tracking
    pub(super) fn parse_bitwise_or_spanned(&mut self) -> Result<SpannedExpr, ParseError> {
        let start = self.position;
        let mut left = self.parse_bitwise_xor_spanned()?;
        while self.try_consume_single_pipe() {
            let right = self.parse_bitwise_xor_spanned()?;
            let expr = PureExpr::BinOp(Arc::new(left.expr), BinOp::BitOr, Arc::new(right.expr));
            left = SpannedExpr::new(expr, self.span(start));
        }
        Ok(left)
    }

    /// Parse bitwise XOR (`^`) with span tracking
    pub(super) fn parse_bitwise_xor_spanned(&mut self) -> Result<SpannedExpr, ParseError> {
        let start = self.position;
        let mut left = self.parse_bitwise_and_spanned()?;
        while self.try_consume("^") {
            let right = self.parse_bitwise_and_spanned()?;
            let expr = PureExpr::BinOp(Arc::new(left.expr), BinOp::BitXor, Arc::new(right.expr));
            left = SpannedExpr::new(expr, self.span(start));
        }
        Ok(left)
    }

    /// Parse bitwise AND (`&`) with span tracking
    pub(super) fn parse_bitwise_and_spanned(&mut self) -> Result<SpannedExpr, ParseError> {
        let start = self.position;
        let mut left = self.parse_shift_spanned()?;
        while self.try_consume_single_ampersand() {
            let right = self.parse_shift_spanned()?;
            let expr = PureExpr::BinOp(Arc::new(left.expr), BinOp::BitAnd, Arc::new(right.expr));
            left = SpannedExpr::new(expr, self.span(start));
        }
        Ok(left)
    }

    /// Parse shift operators (`<<`, `>>`) with span tracking
    pub(super) fn parse_shift_spanned(&mut self) -> Result<SpannedExpr, ParseError> {
        let start = self.position;
        let mut left = self.parse_additive_spanned()?;
        loop {
            if self.try_consume("<<") {
                let right = self.parse_additive_spanned()?;
                let expr = PureExpr::BinOp(Arc::new(left.expr), BinOp::Shl, Arc::new(right.expr));
                left = SpannedExpr::new(expr, self.span(start));
            } else if self.try_consume(">>") {
                let right = self.parse_additive_spanned()?;
                let expr = PureExpr::BinOp(Arc::new(left.expr), BinOp::Shr, Arc::new(right.expr));
                left = SpannedExpr::new(expr, self.span(start));
            } else {
                break;
            }
        }
        Ok(left)
    }

    /// Parse + and - with span tracking
    pub(super) fn parse_additive_spanned(&mut self) -> Result<SpannedExpr, ParseError> {
        let start = self.position;
        let mut left = self.parse_multiplicative_spanned()?;
        loop {
            if self.try_consume("+") {
                let right = self.parse_multiplicative_spanned()?;
                let expr = PureExpr::BinOp(Arc::new(left.expr), BinOp::Add, Arc::new(right.expr));
                left = SpannedExpr::new(expr, self.span(start));
            } else if self.try_consume("-") {
                let right = self.parse_multiplicative_spanned()?;
                let expr = PureExpr::BinOp(Arc::new(left.expr), BinOp::Sub, Arc::new(right.expr));
                left = SpannedExpr::new(expr, self.span(start));
            } else {
                break;
            }
        }
        Ok(left)
    }

    /// Parse * and / with span tracking
    pub(super) fn parse_multiplicative_spanned(&mut self) -> Result<SpannedExpr, ParseError> {
        let start = self.position;
        let mut left = self.parse_cast_spanned()?;
        loop {
            if self.try_consume("*") {
                let right = self.parse_cast_spanned()?;
                let expr = PureExpr::BinOp(Arc::new(left.expr), BinOp::Mul, Arc::new(right.expr));
                left = SpannedExpr::new(expr, self.span(start));
            } else if self.try_consume("/") {
                let right = self.parse_cast_spanned()?;
                // Creusot's `/` on `Int` is `int.ComputerDivision.div`
                // (truncation toward zero), not Euclidean. Lower to
                // `BinOp::DivTrunc` so contract division agrees with the signed
                // machine body. See trust-wp-divmod-semantics.
                let expr =
                    PureExpr::BinOp(Arc::new(left.expr), BinOp::DivTrunc, Arc::new(right.expr));
                left = SpannedExpr::new(expr, self.span(start));
            } else if self.try_consume("%") {
                let right = self.parse_cast_spanned()?;
                // `%` stays Euclidean (`BinOp::Mod`): trust-wp-std's wrapping
                // arithmetic specs reduce a possibly-negative dividend modulo
                // `2^n` and rely on the non-negative Euclidean remainder. Only
                // `/` is reclassified to truncated. See trust-wp-divmod-semantics.
                let expr = PureExpr::BinOp(Arc::new(left.expr), BinOp::Mod, Arc::new(right.expr));
                left = SpannedExpr::new(expr, self.span(start));
            } else {
                break;
            }
        }
        Ok(left)
    }

    /// Parse cast expressions (`expr as Type`) and type ascriptions
    /// (`expr : Type`).
    ///
    /// Both are treated as transparent in logical expressions: the type is
    /// parsed and discarded and the inner expression is returned (with its span
    /// widened to include the ascription). The `: Type` form is only consumed
    /// on a single `:` (not `::`); see `parse_cast` for why this does not
    /// collide with binder/struct-field colons.
    pub(super) fn parse_cast_spanned(&mut self) -> Result<SpannedExpr, ParseError> {
        let start = self.position;
        let mut expr = self.parse_view_spanned()?;
        loop {
            if self.try_consume_keyword("as") {
                self.skip_whitespace();
                self.consume_type_annotation()?;
                expr = SpannedExpr::new(expr.expr, self.span(start));
            } else if self.try_consume_single_colon() {
                self.skip_whitespace();
                self.consume_type_annotation()?;
                expr = SpannedExpr::new(expr.expr, self.span(start));
            } else {
                break;
            }
        }
        Ok(expr)
    }

    /// Parse the low-precedence view operator (`@`) with span tracking.
    pub(super) fn parse_view_spanned(&mut self) -> Result<SpannedExpr, ParseError> {
        let start = self.position;
        let expr = self.parse_unary_spanned()?;
        self.parse_view_suffix_spanned(expr, start)
    }

    /// Parse unary operators with span tracking
    pub(super) fn parse_unary_spanned(&mut self) -> Result<SpannedExpr, ParseError> {
        self.skip_whitespace();
        let start = self.position;
        if self.try_consume("!") {
            let operand = self.parse_unary_spanned()?;
            let expr = PureExpr::UnOp(UnOp::Not, Arc::new(operand.expr));
            return Ok(SpannedExpr::new(expr, self.span(start)));
        }
        if self.try_consume("~") {
            let operand = self.parse_unary_spanned()?;
            let expr = PureExpr::UnOp(UnOp::BitNot, Arc::new(operand.expr));
            return Ok(SpannedExpr::new(expr, self.span(start)));
        }
        // Check for negation (must not be followed by digit for negative literal)
        if self.peek() == Some('-') && !self.is_negative_literal() {
            self.advance();
            let operand = self.parse_unary_spanned()?;
            let expr = PureExpr::UnOp(UnOp::Neg, Arc::new(operand.expr));
            return Ok(SpannedExpr::new(expr, self.span(start)));
        }
        // Dereference: *v (current value of mutable borrow)
        if self.try_consume("*") {
            let operand = self.parse_unary_spanned()?;
            let expr = PureExpr::Deref(Arc::new(operand.expr));
            return Ok(SpannedExpr::new(expr, self.span(start)));
        }
        // Final/prophecy: ^v (value when borrow ends)
        if self.try_consume("^") {
            let operand = self.parse_unary_spanned()?;
            let expr = PureExpr::Final(Arc::new(operand.expr));
            return Ok(SpannedExpr::new(expr, self.span(start)));
        }
        // Reference operators: &mut expr / &expr (transparent in contract logic)
        if self.try_consume_single_ampersand() {
            self.skip_whitespace();
            self.try_consume_keyword("mut");
            let operand = self.parse_unary_spanned()?;
            return Ok(SpannedExpr::new(operand.expr, self.span(start)));
        }
        self.parse_postfix_spanned()
    }

    /// Parse high-precedence postfix operators with span tracking (method calls,
    /// field access, indexing, and range slicing).
    pub(super) fn parse_postfix_spanned(&mut self) -> Result<SpannedExpr, ParseError> {
        let start = self.position;
        let expr = self.parse_primary_base_spanned()?;
        self.parse_postfix_suffix_spanned(expr, start)
    }

    /// Parse repeated postfix suffixes after a primary expression.
    fn parse_postfix_suffix_spanned(
        &mut self,
        mut expr: SpannedExpr,
        start: usize,
    ) -> Result<SpannedExpr, ParseError> {
        loop {
            self.skip_whitespace();

            // Method call, field access, or tuple field access.
            // Use try_consume_single_dot to avoid consuming `.` when `..` or
            // `..=` range operator follows inside index brackets. (#1513)
            if self.try_consume_single_dot() {
                // Tuple field access: expr.0, expr.1, etc.
                if let Some(index) = self.try_parse_tuple_field_index() {
                    let field_expr = PureExpr::LogicFnCall {
                        name: tuple_field_logic_fn_name(index),
                        args: vec![expr.expr],
                    };
                    expr = SpannedExpr::new(field_expr, self.span(start));
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
                    let method_expr = PureExpr::MethodCall {
                        receiver: Arc::new(expr.expr),
                        method: method_name,
                        args,
                    };
                    expr = SpannedExpr::new(method_expr, self.span(start));
                } else {
                    // Named field access: expr.field
                    // Lowered to a synthetic logic function call like tuple fields
                    let field_expr = PureExpr::LogicFnCall {
                        name: format!("{NAMED_FIELD_LOGIC_FN_PREFIX}{method_name}"),
                        args: vec![expr.expr],
                    };
                    expr = SpannedExpr::new(field_expr, self.span(start));
                }
                continue;
            }

            // Indexing or range slicing: expr[index] or expr[a..b] etc.
            // Plain index → expr.index_logic(index)
            // Range variants → expr.subsequence(from, to) (#1513)
            if self.try_consume("[") {
                let result = self.parse_index_or_range(expr.expr)?;
                expr = SpannedExpr::new(result, self.span(start));
                continue;
            }

            break;
        }

        Ok(expr)
    }

    /// Parse one-or-more low-precedence view suffixes, preserving the full
    /// span from the unary expression through any chained postfixes.
    fn parse_view_suffix_spanned(
        &mut self,
        mut expr: SpannedExpr,
        start: usize,
    ) -> Result<SpannedExpr, ParseError> {
        loop {
            self.skip_whitespace();
            if !self.try_consume("@") {
                break;
            }
            let view_expr = PureExpr::View(Arc::new(expr.expr));
            expr = SpannedExpr::new(view_expr, self.span(start));
            expr = self.parse_postfix_suffix_spanned(expr, start)?;
        }
        Ok(expr)
    }

    /// Parse base primary expressions with span tracking
    #[allow(clippy::too_many_lines)]
    pub(super) fn parse_primary_base_spanned(&mut self) -> Result<SpannedExpr, ParseError> {
        self.skip_whitespace();
        let start = self.position;

        // Parenthesized expression or unit value ()
        if self.try_consume("(") {
            self.skip_whitespace();
            // Unit value: () — empty tuple / unit type
            if self.try_consume(")") {
                let unit_expr = PureExpr::LogicFnCall {
                    name: tuple_logic_fn_name(0),
                    args: vec![],
                };
                return Ok(SpannedExpr::new(unit_expr, self.span(start)));
            }
            let first = self.parse_expr_spanned()?;
            self.skip_whitespace();
            if self.try_consume(",") {
                self.skip_whitespace();
                if self.try_consume(")") {
                    // Singleton tuple sugar: `(x,)` lowers to `x`.
                    return Ok(SpannedExpr::new(first.expr, self.span(start)));
                }
                // Multi-element tuples are lowered to synthetic logic-function calls:
                // `(x, y)` -> `__trust_wp_tuple2(x, y)`.
                let mut items = vec![first.expr];
                loop {
                    let item = self.parse_expr_spanned()?;
                    items.push(item.expr);
                    self.skip_whitespace();
                    if self.try_consume(",") {
                        self.skip_whitespace();
                        if self.try_consume(")") {
                            break;
                        }
                        continue;
                    }
                    if self.try_consume(")") {
                        break;
                    }
                    return Err(self.error("expected ',' or ')' in tuple expression"));
                }
                let tuple_expr = PureExpr::LogicFnCall {
                    name: tuple_logic_fn_name(items.len()),
                    args: items,
                };
                return Ok(SpannedExpr::new(tuple_expr, self.span(start)));
            }
            if !self.try_consume(")") {
                return Err(self.error("expected ')'"));
            }
            // Return inner expression with full span including parens
            return Ok(SpannedExpr::new(first.expr, self.span(start)));
        }

        // Boolean literals
        if self.try_consume_keyword("true") {
            return Ok(SpannedExpr::new(PureExpr::Bool(true), self.span(start)));
        }
        if self.try_consume_keyword("false") {
            return Ok(SpannedExpr::new(PureExpr::Bool(false), self.span(start)));
        }

        // old(expr) - captures value at function entry.
        // `old` followed by `(` is the Old keyword; bare `old` (e.g., as a
        // match binding name) falls through to the identifier path. (#967)
        {
            let saved_pos = self.position;
            if self.try_consume_keyword("old") {
                self.skip_whitespace();
                if self.try_consume("(") {
                    let inner = self.parse_expr_spanned()?;
                    if !self.try_consume(")") {
                        return Err(self.error("expected ')' after old expression"));
                    }
                    let expr = PureExpr::Old(Arc::new(inner.expr));
                    return Ok(SpannedExpr::new(expr, self.span(start)));
                }
                // No '(' after 'old' — backtrack and treat as identifier
                self.position = saved_pos;
                self.chars = self.input[self.position..].chars().peekable();
            }
        }

        // Universal quantifier: forall<x: Type> body
        if self.try_consume_keyword("forall") {
            let expr = self.parse_quantifier(true)?;
            return Ok(SpannedExpr::new(expr, self.span(start)));
        }

        // Existential quantifier: exists<x: Type> body
        if self.try_consume_keyword("exists") {
            let expr = self.parse_quantifier(false)?;
            return Ok(SpannedExpr::new(expr, self.span(start)));
        }

        // Match expression: match expr { pattern => body, ... }
        if self.try_consume_keyword("match") {
            let expr = self.parse_match()?;
            return Ok(SpannedExpr::new(expr, self.span(start)));
        }

        // If-then-else expression: if cond { then } else { else }.
        //
        // Parity with the unspanned primary (`unspanned/primary.rs`): delegate to
        // the SAME `parse_if_else`/`parse_block`/`parse_closure`/qualified-path
        // methods the normal-fn parser uses, wrapping the result in a single span.
        // This is byte-identical-AST by construction — a `#[requires]` clause must
        // lower to the same `PureExpr` whether the function is trait-refined (this
        // spanned path) or not (the unspanned path), or it would be ASSUMED at
        // entry with one meaning and PROVEN at the call site with another.
        if self.try_consume_keyword("if") {
            let expr = self.parse_if_else()?;
            return Ok(SpannedExpr::new(expr, self.span(start)));
        }

        // Block expression: { stmt; ...; expr }
        if self.peek() == Some('{') {
            let expr = self.parse_block()?;
            return Ok(SpannedExpr::new(expr, self.span(start)));
        }

        // Character literal: 'c' — parsed as integer (Unicode codepoint). (#1513)
        if self.peek() == Some('\'') {
            let char_expr = self.parse_char_literal()?;
            return Ok(SpannedExpr::new(char_expr, self.span(start)));
        }

        // Numeric literal (integer or float, including negative, hex)
        if let Some(num) = self.try_parse_number()? {
            return Ok(SpannedExpr::new(num, self.span(start)));
        }

        // Fully-qualified associated type/const path: `<Type as Trait>::CONST`
        // (e.g. `<I3<T> as Nat>::VALUE`). Mirrors `unspanned/primary.rs` node-for-
        // node so the AST matches: a trailing `(args)` is a `LogicFnCall`,
        // otherwise a `Var` with the full path string.
        if let Some(qualified) = self.try_parse_qualified_path() {
            self.skip_whitespace();
            if self.try_consume("(") {
                let args = self.parse_argument_list()?;
                if !self.try_consume(")") {
                    return Err(self.error("expected ')' after qualified path call arguments"));
                }
                let expr = PureExpr::LogicFnCall {
                    name: qualified,
                    args,
                };
                return Ok(SpannedExpr::new(expr, self.span(start)));
            }
            let expr = PureExpr::Var(qualified, None);
            return Ok(SpannedExpr::new(expr, self.span(start)));
        }

        // Identifier (variable, path like i32::MIN, or logic function call)
        if let Some(ident) = self.try_parse_identifier() {
            let turbofish_args = self.try_parse_turbofish_args()?;
            self.skip_whitespace();
            // Check for logic function call: identifier(args...)
            if self.try_consume("(") {
                let mut args = turbofish_args.unwrap_or_default();
                args.extend(self.parse_argument_list()?);
                if !self.try_consume(")") {
                    return Err(self.error("expected ')' after function arguments"));
                }
                let expr = PureExpr::LogicFnCall { name: ident, args };
                return Ok(SpannedExpr::new(expr, self.span(start)));
            }
            // Macro-style call: identifier!(...), identifier![...], identifier!{...}
            if let Some(open) = self.peek_macro_invocation_delimiter() {
                let close = match open {
                    '(' => ')',
                    '[' => ']',
                    '{' => '}',
                    // Defensive: peek_macro_invocation_delimiter only returns '(', '[', or '{'.
                    _ => return Err(self.error("unexpected macro delimiter")),
                };
                self.advance(); // '!'
                self.skip_whitespace();
                self.advance(); // opening delimiter
                let args = self.parse_argument_list_with_closing(close)?;
                if self.peek() != Some(close) {
                    return Err(self.error(&format!("expected '{close}' after macro arguments")));
                }
                self.advance(); // closing delimiter

                // pearlite! is a transparent wrapper — unwrap to avoid creating
                // an unregistered LogicFnCall that confuses sort inference (#610)
                if ident == "pearlite" && args.len() == 1 {
                    let mut args = args;
                    let expr = args.remove(0);
                    return Ok(SpannedExpr::new(expr, self.span(start)));
                }
                let expr = PureExpr::LogicFnCall { name: ident, args };
                return Ok(SpannedExpr::new(expr, self.span(start)));
            }
            // Struct literal expression: `TypeName { field: expr, ... }`
            if self.peek() == Some('{') {
                let is_type_name =
                    ident.contains("::") || ident.chars().next().is_some_and(char::is_uppercase);
                if is_type_name {
                    let expr = self.parse_struct_literal(ident)?;
                    return Ok(SpannedExpr::new(expr, self.span(start)));
                }
            }
            return Ok(SpannedExpr::new(
                PureExpr::Var(ident, None),
                self.span(start),
            ));
        }

        // Closure expression: |p: T, ...| body (incl. `||` for zero params). In
        // primary position `|` starts a closure; bitwise/logical OR live at higher
        // precedence. Delegates to the shared `parse_closure` for AST parity.
        if self.peek() == Some('|') {
            let expr = self.parse_closure()?;
            return Ok(SpannedExpr::new(expr, self.span(start)));
        }

        Err(self.error("expected expression"))
    }
}
