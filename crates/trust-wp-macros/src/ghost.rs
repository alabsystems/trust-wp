// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ghost block validation
//!
//! Author: Andrew Yates <andrewyates.name@gmail.com>
//!
//! This module validates ghost blocks for the `ghost!` macro.
//! Ghost blocks cannot escape control flow to the enclosing scope.

use proc_macro::TokenStream;
use proc_macro2::Span;
use syn::{visit::Visit, Block, Expr, Stmt};

/// Error type for ghost block validation failures.
#[derive(Debug)]
pub(crate) struct GhostValidationError {
    pub(crate) span: Span,
    pub(crate) message: String,
}

/// Validates a ghost block, ensuring it doesn't escape control flow.
///
/// # Restrictions (macro-time validation)
///
/// This validates control-flow restrictions that can be checked at parse time:
/// - `return` at ghost-block level is rejected (would escape to enclosing function)
/// - `return` inside closures within the ghost block is allowed (exits the closure)
/// - `yield` and `become` are never allowed
/// - `break`/`continue` outside loops are rejected
/// - Labeled `break`/`continue` are conservatively rejected (label scope unknown)
///
/// Semantic restrictions (e.g., no writes to program variables) are
/// validated by the driver at verification time.
///
/// Local unlabeled loops within the ghost block are allowed.
pub(crate) fn validate_ghost_block(input: &TokenStream) -> Result<(), GhostValidationError> {
    validate_ghost_block2(input.clone().into())
}

/// Internal validation using `proc_macro2::TokenStream` (testable outside proc-macro context).
fn validate_ghost_block2(input: proc_macro2::TokenStream) -> Result<(), GhostValidationError> {
    // Parse as a block (braces required around ghost content)
    let block: Block = syn::parse2(input).map_err(|e| GhostValidationError {
        span: e.span(),
        message: "failed to parse ghost block: expected curly braces".to_string(),
    })?;

    let mut validator = GhostValidator::new();
    validator.visit_block(&block);

    if let Some(error) = validator.error {
        return Err(error);
    }

    Ok(())
}

/// AST visitor for validating ghost blocks.
struct GhostValidator {
    /// Current loop nesting depth (for break/continue validation)
    loop_depth: usize,
    /// Current closure nesting depth.
    /// `return` inside a closure exits the closure, not the ghost block,
    /// so it is safe.
    closure_depth: usize,
    /// First error encountered
    error: Option<GhostValidationError>,
}

impl GhostValidator {
    fn new() -> Self {
        Self {
            loop_depth: 0,
            closure_depth: 0,
            error: None,
        }
    }

    fn report_error(&mut self, span: Span, message: impl Into<String>) {
        if self.error.is_none() {
            self.error = Some(GhostValidationError {
                span,
                message: message.into(),
            });
        }
    }
}

impl<'ast> Visit<'ast> for GhostValidator {
    fn visit_expr(&mut self, expr: &'ast Expr) {
        // Stop on first error
        if self.error.is_some() {
            return;
        }

        match expr {
            // Return is not allowed at ghost-block level, but IS allowed
            // inside closures within the ghost block (it exits the closure,
            // not the enclosing function).
            // Reference: Creusot message_passing examples use `return` inside
            // `ghost! { inv.open(..., |inv| { ... return ... }) }`.
            Expr::Return(ret) if self.closure_depth == 0 => {
                self.report_error(
                    ret.return_token.span,
                    "ghost blocks cannot contain 'return' - control flow cannot escape",
                );
                return;
            }

            // Yield and become are not allowed
            Expr::Yield(y) => {
                self.report_error(
                    y.yield_token.span,
                    "ghost blocks cannot contain 'yield' - control flow cannot escape",
                );
                return;
            }

            // Break is only allowed inside loops within the ghost block
            Expr::Break(expr_break) => {
                // Break with a label could escape if the label is outside
                // For Phase 1, we allow break only inside loops (no label escaping)
                if self.loop_depth == 0 {
                    self.report_error(
                        expr_break.break_token.span,
                        "ghost blocks cannot contain 'break' outside of loops - control flow cannot escape",
                    );
                    return;
                }
                // Break with a label - conservatively disallow labeled breaks
                // as they could reference outer loops
                if let Some(label) = &expr_break.label {
                    self.report_error(
                        label.ident.span(),
                        "ghost blocks cannot contain labeled 'break' - label might escape ghost block",
                    );
                    return;
                }
            }

            // Continue is only allowed inside loops within the ghost block
            Expr::Continue(expr_continue) => {
                if self.loop_depth == 0 {
                    self.report_error(
                        expr_continue.continue_token.span,
                        "ghost blocks cannot contain 'continue' outside of loops - control flow cannot escape",
                    );
                    return;
                }
                // Continue with a label - conservatively disallow
                if let Some(label) = &expr_continue.label {
                    self.report_error(
                        label.ident.span(),
                        "ghost blocks cannot contain labeled 'continue' - label might escape ghost block",
                    );
                    return;
                }
            }

            // Track loop entry for break/continue validation
            Expr::Loop(expr_loop) => {
                self.loop_depth += 1;
                syn::visit::visit_expr_loop(self, expr_loop);
                self.loop_depth -= 1;
                return;
            }

            Expr::While(expr_while) => {
                self.loop_depth += 1;
                syn::visit::visit_expr_while(self, expr_while);
                self.loop_depth -= 1;
                return;
            }

            Expr::ForLoop(expr_for) => {
                self.loop_depth += 1;
                syn::visit::visit_expr_for_loop(self, expr_for);
                self.loop_depth -= 1;
                return;
            }

            // Track closure boundaries. `return`/`break`/`continue` inside
            // a closure affect the closure, not the ghost block.
            Expr::Closure(expr_closure) => {
                self.closure_depth += 1;
                // Reset loop_depth inside the closure — loops in the
                // enclosing scope don't apply inside the closure.
                let saved_loop_depth = self.loop_depth;
                self.loop_depth = 0;
                syn::visit::visit_expr_closure(self, expr_closure);
                self.loop_depth = saved_loop_depth;
                self.closure_depth -= 1;
                return;
            }

            // Other expressions are allowed
            _ => {}
        }

        // Continue visiting children
        syn::visit::visit_expr(self, expr);
    }

    fn visit_stmt(&mut self, stmt: &'ast Stmt) {
        // Stop on first error
        if self.error.is_some() {
            return;
        }

        // Continue visiting
        syn::visit::visit_stmt(self, stmt);
    }
}

#[cfg(test)]
mod tests {
    use quote::quote;

    use super::*;

    fn validate(tokens: proc_macro2::TokenStream) -> Result<(), GhostValidationError> {
        validate_ghost_block2(tokens)
    }

    #[test]
    fn test_empty_block() {
        validate(quote! { {} }).unwrap();
    }

    #[test]
    fn test_simple_let() {
        validate(quote! {
            {
                let x = 42;
            }
        })
        .unwrap();
    }

    #[test]
    fn test_ghost_variable() {
        validate(quote! {
            {
                let _g = 42;
                let _h = _g + 1;
            }
        })
        .unwrap();
    }

    #[test]
    fn test_loop_inside_ghost() {
        validate(quote! {
            {
                let mut i = 0;
                while i < 10 {
                    i += 1;
                }
            }
        })
        .unwrap();
    }

    #[test]
    fn test_break_inside_loop() {
        validate(quote! {
            {
                loop {
                    break;
                }
            }
        })
        .unwrap();
    }

    #[test]
    fn test_continue_inside_loop() {
        validate(quote! {
            {
                let mut i = 0;
                while i < 10 {
                    i += 1;
                    if i == 5 {
                        continue;
                    }
                }
            }
        })
        .unwrap();
    }

    #[test]
    fn test_reject_return() {
        let err = validate(quote! {
            {
                return;
            }
        })
        .unwrap_err();
        assert!(
            err.message.contains("cannot contain 'return'"),
            "expected return-rejection error, got: {}",
            err.message
        );
    }

    #[test]
    fn test_reject_return_with_value() {
        let err = validate(quote! {
            {
                return 42;
            }
        })
        .unwrap_err();
        assert!(
            err.message.contains("cannot contain 'return'"),
            "expected return-rejection error, got: {}",
            err.message
        );
    }

    #[test]
    fn test_reject_break_outside_loop() {
        let err = validate(quote! {
            {
                break;
            }
        })
        .unwrap_err();
        assert!(
            err.message.contains("outside of loops"),
            "expected break-outside-loop error, got: {}",
            err.message
        );
    }

    #[test]
    fn test_reject_continue_outside_loop() {
        let err = validate(quote! {
            {
                continue;
            }
        })
        .unwrap_err();
        assert!(
            err.message.contains("outside of loops"),
            "expected continue-outside-loop error, got: {}",
            err.message
        );
    }

    #[test]
    fn test_reject_labeled_break() {
        let err = validate(quote! {
            {
                'outer: loop {
                    loop {
                        break 'outer;
                    }
                }
            }
        })
        .unwrap_err();
        assert!(
            err.message.contains("labeled"),
            "expected labeled-break error, got: {}",
            err.message
        );
    }

    #[test]
    fn test_reject_yield() {
        let err = validate(quote! {
            {
                yield 42;
            }
        })
        .unwrap_err();
        assert!(
            err.message.contains("yield"),
            "expected yield-rejection error, got: {}",
            err.message
        );
    }

    #[test]
    fn test_allow_return_inside_closure() {
        // Creusot message_passing tests use `return` inside closures within
        // ghost blocks. The `return` exits the closure, not the function.
        validate(quote! {
            {
                inv.open(tokens, |inv: &mut Foo| {
                    if !cond {
                        return
                    }
                    do_something();
                })
            }
        })
        .unwrap();
    }

    #[test]
    fn test_reject_return_outside_closure() {
        // `return` at the ghost block level should still be rejected.
        let err = validate(quote! {
            {
                let _f = |x| { return x; };
                return;
            }
        })
        .unwrap_err();
        assert!(
            err.message.contains("cannot contain 'return'"),
            "expected return-rejection error, got: {}",
            err.message
        );
    }

    #[test]
    fn test_allow_break_inside_closure_loop() {
        // Break inside a loop inside a closure within ghost block.
        validate(quote! {
            {
                let _f = |items: Vec<i32>| {
                    for x in items {
                        if x > 0 {
                            break;
                        }
                    }
                };
            }
        })
        .unwrap();
    }
}
