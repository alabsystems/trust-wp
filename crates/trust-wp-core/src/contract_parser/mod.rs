// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Contract expression parser
//!
//! Parses contract strings (e.g., "x > 0", "result == x + 1") into
//! `PureExpr` AST nodes for verification condition generation.

use std::{error::Error, fmt, iter::Peekable, str::Chars, sync::Arc};

use crate::formula::{PureExpr, SpannedExpr};

mod helpers;
mod spanned;
mod unspanned;

#[cfg(test)]
mod tests;

/// Internal wrapper used to preserve turbofish generic arguments until the
/// driver can classify type-only generics vs. const generics. (#1635)
pub const TURBOFISH_ARG_WRAPPER_NAME: &str = "__trust_wp_turbofish_arg";

/// Error during contract parsing
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub message: String,
    pub position: usize,
}

impl fmt::Display for ParseError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "parse error at position {}: {}",
            self.position, self.message
        )
    }
}

impl Error for ParseError {}

/// Contract expression parser
pub(crate) struct ContractParser<'a> {
    input: &'a str,
    chars: Peekable<Chars<'a>>,
    position: usize,
    preserve_stmt_exprs: bool,
    stmt_expr_counter: usize,
    /// When true, suppress struct literal parsing for uppercase identifiers
    /// followed by `{`. Mirrors Rust's `RESTRICTION_NO_STRUCT_LITERAL` for
    /// if/while/for conditions where `Ident {` would be ambiguous with the
    /// branch block. (#2331)
    no_struct_literals: bool,
}

impl<'a> ContractParser<'a> {
    /// Create a new parser for the given input
    pub(crate) fn new(input: &'a str) -> Self {
        Self {
            input,
            chars: input.chars().peekable(),
            position: 0,
            preserve_stmt_exprs: false,
            stmt_expr_counter: 0,
            no_struct_literals: false,
        }
    }

    /// Parse the entire input as an expression.
    ///
    /// # Errors
    ///
    /// Returns a [`ParseError`] if the input contains:
    /// - Syntax errors (unmatched parentheses, invalid operators)
    /// - Unexpected characters after a valid expression
    /// - Invalid tokens
    pub(crate) fn parse(mut self) -> Result<PureExpr, ParseError> {
        self.skip_whitespace();
        let expr = self.parse_expr()?;
        self.skip_whitespace();
        if self.chars.peek().is_some() {
            return Err(self.error("unexpected characters after expression"));
        }
        Ok(normalize_parsed_expr(expr))
    }

    /// Parse the entire input as a block body (statements + trailing expression).
    ///
    /// Handles Creusot-style multi-statement `proof_assert!` blocks:
    /// ```text
    /// lemma_call();
    /// lemma_call2();
    /// assertion_expr
    /// ```
    ///
    /// Statement expressions (followed by `;`) are parsed and discarded (they
    /// serve as lemma invocation hints in Creusot but have no logical value in
    /// trust-wp's current architecture). The trailing expression without `;` is
    /// returned as the block's value.
    ///
    /// Falls back to single-expression parsing when no semicolons are present.
    pub(crate) fn parse_as_block(mut self) -> Result<PureExpr, ParseError> {
        self.skip_whitespace();
        let expr = self.parse_top_level_body()?;
        self.skip_whitespace();
        if self.chars.peek().is_some() {
            return Err(self.error("unexpected characters after expression"));
        }
        Ok(normalize_parsed_expr(expr))
    }

    /// Parse the entire input as a block body and retain leading statements.
    pub(crate) fn parse_as_block_with_leading_exprs(
        mut self,
    ) -> Result<(Vec<PureExpr>, PureExpr), ParseError> {
        self.preserve_stmt_exprs = true;
        self.skip_whitespace();
        let expr = if self.peek() == Some('{') {
            self.try_consume("{");
            let parsed = self.parse_block_body_with_leading_exprs()?;
            self.skip_whitespace();
            if !self.try_consume("}") {
                return Err(self.error("expected '}'"));
            }
            parsed
        } else {
            self.parse_top_level_body_with_leading_exprs()?
        };
        self.skip_whitespace();
        if self.chars.peek().is_some() {
            return Err(self.error("unexpected characters after expression"));
        }
        Ok((
            expr.0.into_iter().map(normalize_parsed_expr).collect(),
            normalize_parsed_expr(expr.1),
        ))
    }

    /// Parse the entire input as an expression with source location tracking.
    ///
    /// Returns a [`SpannedExpr`] that records the span of the full expression
    /// within the input string.
    ///
    /// # Errors
    ///
    /// Returns a [`ParseError`] if the input contains syntax errors, invalid tokens,
    /// or unexpected characters.
    pub(crate) fn parse_spanned(mut self) -> Result<SpannedExpr, ParseError> {
        self.skip_whitespace();
        let expr = self.parse_expr_spanned()?;
        self.skip_whitespace();
        if self.chars.peek().is_some() {
            return Err(self.error("unexpected characters after expression"));
        }
        let expr = SpannedExpr {
            expr: normalize_parsed_expr(expr.expr),
            span: expr.span,
        };
        Ok(expr)
    }

    pub(crate) fn wrap_stmt_expr(&mut self, value: PureExpr, body: PureExpr) -> PureExpr {
        let idx = self.stmt_expr_counter;
        self.stmt_expr_counter += 1;
        PureExpr::Let {
            var: format!("__stmt{idx}"),
            value: Arc::new(value),
            body: Arc::new(body),
        }
    }
}

fn normalize_parsed_expr(expr: PureExpr) -> PureExpr {
    expr.rewrite_bottom_up(|node| match node {
        PureExpr::Var(name, sort) => {
            let name = normalize_qualified_path_spacing(name);
            PureExpr::Var(name, sort)
        }
        PureExpr::LogicFnCall { name, args } => {
            let name = normalize_qualified_path_spacing(name);
            PureExpr::LogicFnCall { name, args }
        }
        node => node,
    })
}

fn normalize_qualified_path_spacing(name: String) -> String {
    if name.starts_with('<') && name.contains(">as ") {
        name.replace(">as ", "> as ")
    } else {
        name
    }
}

/// Parse a contract expression string into a [`PureExpr`] AST.
///
/// # Errors
///
/// Returns a [`ParseError`] if the input contains syntax errors, invalid tokens,
/// or unexpected characters.
pub fn parse_contract(input: &str) -> Result<PureExpr, ParseError> {
    ContractParser::new(input).parse()
}

/// Parse a block-style contract body into a [`PureExpr`] AST.
///
/// Handles multi-statement input such as Creusot `proof_assert!` blocks:
/// ```text
/// lemma_call();
/// lemma_call2();
/// assertion_expr
/// ```
///
/// Leading statement expressions (terminated by `;`) are parsed and discarded.
/// The trailing expression is returned as the block value. If the input contains
/// no semicolons, this behaves identically to [`parse_contract`].
///
/// # Errors
///
/// Returns a [`ParseError`] if the input contains syntax errors, invalid tokens,
/// or unexpected characters.
pub fn parse_contract_body(input: &str) -> Result<PureExpr, ParseError> {
    ContractParser::new(input).parse_as_block()
}

/// Parse a block-style contract body and retain leading expression statements.
///
/// # Errors
///
/// Returns a [`ParseError`] if the input contains syntax errors, invalid tokens,
/// or unexpected characters.
pub fn parse_contract_body_with_leading_exprs(
    input: &str,
) -> Result<(Vec<PureExpr>, PureExpr), ParseError> {
    ContractParser::new(input).parse_as_block_with_leading_exprs()
}

/// Parse a contract expression string into a [`SpannedExpr`] AST with source locations.
///
/// This is the preferred entry point when source location information is needed
/// for error reporting. The returned [`SpannedExpr`] records the span of the
/// full expression within the input string.
///
/// # Errors
///
/// Returns a [`ParseError`] if the input contains syntax errors, invalid tokens,
/// or unexpected characters.
pub fn parse_contract_spanned(input: &str) -> Result<SpannedExpr, ParseError> {
    ContractParser::new(input).parse_spanned()
}
