// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Contract expression validation and analysis
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This module validates contract expressions and identifies special forms
//! like `result` and `old(...)`.

use proc_macro2::Span;
use syn::{spanned::Spanned, visit::Visit, Expr, ExprCall, ExprPath, Ident};
use thiserror::Error;

/// Typed validation errors for contract expressions.
///
/// Each variant corresponds to a specific validation failure. The `Display` impl
/// (via thiserror) produces user-facing error messages shown at compile time.
#[derive(Debug, Error)]
pub(crate) enum ContractValidationError {
    /// `result` used inside `old()` -- `result` is post-state, `old()` captures pre-state.
    #[error("`result` cannot be used inside `old()` - `result` is post-state, `old()` captures pre-state")]
    ResultInsideOld,

    /// `result` used in a contract kind that does not support it.
    #[error(
        "`result` can only be used in #[ensures] postconditions or #[invariant] loop invariants"
    )]
    ResultInWrongContext,

    /// `old()` used in a contract kind that does not support it.
    #[error("`old()` can only be used in #[ensures] postconditions")]
    OldInWrongContext,

    /// `old()` called with wrong number of arguments.
    #[error("old() expects exactly 1 argument, found {arg_count}")]
    OldWrongArgCount {
        /// The number of arguments found.
        arg_count: usize,
    },

    /// `result` used on a function that returns unit.
    #[error("`result` requires the annotated item to return a value")]
    ResultOnUnitReturn,

    /// Contract contains disallowed control flow, assignments, or side effects.
    #[error("contract expressions cannot contain control flow, assignments, or side effects")]
    DisallowedControlFlow,

    /// Failed to parse the contract expression via trust-wp-core.
    #[error("failed to parse contract: {reason}")]
    CoreParseFailed {
        /// The underlying parse error description.
        reason: String,
    },

    /// Failed to parse the expression via syn.
    #[error("failed to parse pearlite expression: {reason}")]
    SynParseFailed {
        /// The underlying syn error description.
        reason: String,
    },
}

/// Span-enriched contract parse error for proc-macro error reporting.
///
/// Wraps a [`ContractValidationError`] with a [`Span`] so that compile-time
/// diagnostics point to the correct source location.
#[derive(Debug)]
pub(crate) struct ContractParseError {
    pub(crate) span: Span,
    pub(crate) kind: ContractValidationError,
}

impl ContractParseError {
    /// Creates a new `ContractParseError` from a span and validation error kind.
    pub(crate) fn new(span: Span, kind: ContractValidationError) -> Self {
        Self { span, kind }
    }

    /// Returns the user-facing error message.
    pub(crate) fn message(&self) -> String {
        self.kind.to_string()
    }
}

/// The kind of contract being validated.
///
/// This context determines which special forms are valid:
/// - `result` is only valid in `Ensures` and `Invariant`
/// - `old(...)` is only valid in `Ensures`
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum ContractKind {
    /// Precondition - cannot use `result` or `old()`
    Requires,
    /// Postcondition - can use `result` and `old()`
    Ensures,
    /// Loop invariant - can use `result` but not `old()`
    Invariant,
    /// Termination variant - no special forms
    Variant,
}

/// Represents a validated contract expression.
///
/// Contract expressions support:
/// - Standard Rust expressions (arithmetic, comparisons, logical operators)
/// - `result` - refers to the function's return value (in ensures and invariants)
/// - `old(expr)` - captures the value of expr at function entry (in ensures)
pub(crate) struct ContractExpr;

impl ContractExpr {
    /// Validates a contract expression with context awareness.
    ///
    /// The `kind` determines which special forms are allowed:
    /// - `Requires`: No `result`, no `old()`
    /// - `Ensures`: Both `result` and `old()` allowed
    /// - `Invariant`: `result` allowed, no `old()`
    /// - `Variant`: Neither `result` nor `old()` allowed
    pub(crate) fn validate_with_kind(
        expr: &Expr,
        kind: ContractKind,
    ) -> Result<(), ContractParseError> {
        let mut validator = ExprValidator::new(kind);
        validator.visit_expr(expr);

        if let Some(error) = validator.error {
            return Err(error);
        }

        Ok(())
    }
}

/// AST visitor for validating contract expressions.
struct ExprValidator {
    kind: ContractKind,
    /// Tracks whether we're inside an `old()` call.
    /// `result` cannot be used inside `old()` because result is post-state
    /// and `old()` captures pre-state.
    inside_old: bool,
    error: Option<ContractParseError>,
}

impl ExprValidator {
    fn new(kind: ContractKind) -> Self {
        Self {
            kind,
            inside_old: false,
            error: None,
        }
    }

    /// Check if `result` is allowed in this contract kind.
    fn result_allowed(&self) -> bool {
        matches!(self.kind, ContractKind::Ensures | ContractKind::Invariant)
    }

    /// Check if `old()` is allowed in this contract kind.
    fn old_allowed(&self) -> bool {
        matches!(self.kind, ContractKind::Ensures)
    }

    fn report_error(&mut self, span: Span, kind: ContractValidationError) {
        if self.error.is_none() {
            self.error = Some(ContractParseError::new(span, kind));
        }
    }

    /// Check if an identifier is the special `result` variable.
    fn is_result_var(ident: &Ident) -> bool {
        ident == "result"
    }

    /// Check if a call expression is the `old(...)` form.
    fn is_old_call(call: &ExprCall) -> bool {
        if let Expr::Path(ExprPath { path, .. }) = call.func.as_ref() {
            if path.is_ident("old") {
                return true;
            }
        }
        false
    }

    /// Validate that `old()` is called with exactly one argument.
    fn validate_old_call(&mut self, call: &ExprCall) {
        if call.args.len() != 1 {
            self.report_error(
                call.func.span(),
                ContractValidationError::OldWrongArgCount {
                    arg_count: call.args.len(),
                },
            );
        }
    }
}

impl<'ast> Visit<'ast> for ExprValidator {
    fn visit_expr(&mut self, expr: &'ast Expr) {
        // Stop on first error
        if self.error.is_some() {
            return;
        }

        match expr {
            // Check for special forms in path expressions
            Expr::Path(expr_path) => {
                // `result` is only allowed in ensures/invariant
                if let Some(ident) = expr_path.path.get_ident() {
                    if Self::is_result_var(ident) {
                        // result cannot be inside old() - old() captures pre-state, result is post-state
                        if self.inside_old {
                            self.report_error(
                                ident.span(),
                                ContractValidationError::ResultInsideOld,
                            );
                            return;
                        }
                        if !self.result_allowed() {
                            self.report_error(
                                ident.span(),
                                ContractValidationError::ResultInWrongContext,
                            );
                        }
                        return;
                    }
                }
                // Other paths are variable references - allowed
            }

            // Check for old() calls
            Expr::Call(call) if Self::is_old_call(call) => {
                if !self.old_allowed() {
                    self.report_error(call.func.span(), ContractValidationError::OldInWrongContext);
                    return;
                }
                self.validate_old_call(call);
                // Validate the argument with inside_old context
                let prev_inside_old = self.inside_old;
                self.inside_old = true;
                for arg in &call.args {
                    self.visit_expr(arg);
                }
                self.inside_old = prev_inside_old;
                return;
            }
            // Other function calls - validate arguments

            // Allow if-then-else in contracts (encoded as ITE in SMT)
            Expr::If(expr_if) => {
                self.visit_expr(&expr_if.cond);
                for stmt in &expr_if.then_branch.stmts {
                    if let syn::Stmt::Expr(e, _) = stmt {
                        self.visit_expr(e);
                    }
                }
                if let Some((_, else_branch)) = &expr_if.else_branch {
                    self.visit_expr(else_branch);
                }
                return;
            }

            // Allow match expressions in contracts (encoded as nested ITE in SMT)
            Expr::Match(expr_match) => {
                self.visit_expr(&expr_match.expr);
                for arm in &expr_match.arms {
                    if let Some((_, guard)) = &arm.guard {
                        self.visit_expr(guard);
                    }
                    self.visit_expr(&arm.body);
                }
                return;
            }

            // Allow block expressions (containers used by if/match else branches)
            Expr::Block(expr_block) => {
                for stmt in &expr_block.block.stmts {
                    if let syn::Stmt::Expr(e, _) = stmt {
                        self.visit_expr(e);
                    }
                }
                return;
            }

            // Disallow: loops, control flow, assignments (closures allowed).
            Expr::Loop(_)
            | Expr::While(_)
            | Expr::ForLoop(_)
            | Expr::Return(_)
            | Expr::Break(_)
            | Expr::Continue(_)
            | Expr::Assign(_)
            | Expr::Async(_)
            | Expr::Await(_)
            | Expr::Yield(_) => {
                self.report_error(expr.span(), ContractValidationError::DisallowedControlFlow);
                return;
            }

            // Valid expressions: arithmetic, comparison, logical operations,
            // unary operations, parenthesized, literals, field access,
            // method calls, indexing, references, casts, and others
            _ => {}
        }

        // Continue visiting children
        syn::visit::visit_expr(self, expr);
    }
}

#[cfg(test)]
mod tests;
