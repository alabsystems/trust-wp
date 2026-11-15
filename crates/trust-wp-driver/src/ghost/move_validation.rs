// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Move validation for ghost blocks.
//!
//! Detects when non-Copy, non-Ghost values from outside a ghost block are
//! consumed in positions that would constitute a move (let bindings, function
//! arguments, struct fields, etc.).

use std::collections::HashSet;

use rustc_hir::{
    intravisit::{walk_expr, walk_stmt, Visitor},
    Expr, ExprKind, HirId, LoopSource, Stmt, StmtKind,
};
use rustc_middle::ty::{TyCtxt, TypeckResults, TypingEnv};

use super::{
    type_helpers::{
        is_binding_from_ghost_like_init, is_ghost_like_type, is_trust_wp_logic_type,
        BoundVariableCollector,
    },
    GhostBlock, GhostValidationError,
};

/// Validate a single ghost block for moves of non-ghost values.
///
/// This is a conservative HIR-level check that detects when non-Copy types
/// from outside the ghost block are used in consuming positions:
/// - Let bindings: `let x = outer_var;` where outer_var is non-Copy
/// - Function calls: `foo(outer_var)` where outer_var is non-Copy
/// - Return values: using outer_var directly without borrowing
///
/// `Ghost<T>` types are exempt from this check as they are specification-only.
pub(super) fn validate_ghost_block_moves<'tcx>(
    tcx: TyCtxt<'tcx>,
    ghost_block: &GhostBlock,
    expr: &'tcx Expr<'tcx>,
) -> Vec<GhostValidationError> {
    // Collect variables bound inside the ghost block (these can be moved freely)
    let mut bound_collector = BoundVariableCollector::new();
    bound_collector.visit_expr(expr);

    // Get type checking results for the containing function
    let typeck_results = tcx.typeck(ghost_block.containing_fn);

    // Build a typing environment for the containing function so we can query
    // rustc whether arbitrary types implement Copy.
    let typing_env = TypingEnv::non_body_analysis(tcx, ghost_block.containing_fn);

    // Find all value usages that might be moves
    let mut validator = MoveValidator {
        tcx,
        typeck_results,
        typing_env,
        bound_variables: bound_collector.bound_variables,
        errors: Vec::new(),
    };
    validator.visit_expr(expr);

    validator.errors
}

/// Validate a single ghost block for non-terminating `loop {}` expressions.
///
/// `while`/`for` loops are handled via their own contract checking paths. This
/// validator only flags raw `loop {}` constructs that have no `break`, which
/// are trivially non-terminating in ghost context.
pub(super) fn validate_ghost_block_loops<'tcx>(
    _ghost_block: &GhostBlock,
    expr: &'tcx Expr<'tcx>,
) -> Vec<GhostValidationError> {
    let mut validator = LoopValidator { errors: Vec::new() };
    validator.visit_expr(expr);
    validator.errors
}

/// HIR visitor that rejects obviously non-terminating `loop {}` in ghost code.
struct LoopValidator {
    errors: Vec<GhostValidationError>,
}

impl<'tcx> Visitor<'tcx> for LoopValidator {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if let ExprKind::Loop(body, _label, source, _span) = expr.kind {
            if matches!(source, LoopSource::Loop) && !block_contains_break(body) {
                self.errors.push(GhostValidationError {
                    span: expr.span,
                    message: "non-terminating `loop {}` in ghost block requires #[variant(...)]"
                        .to_string(),
                });
            }
        }

        walk_expr(self, expr);
    }
}

fn block_contains_break<'tcx>(block: &'tcx rustc_hir::Block<'tcx>) -> bool {
    struct BreakFinder {
        found: bool,
    }

    impl<'tcx> Visitor<'tcx> for BreakFinder {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if self.found {
                return;
            }
            if matches!(expr.kind, ExprKind::Break(..)) {
                self.found = true;
                return;
            }
            walk_expr(self, expr);
        }
    }

    let mut finder = BreakFinder { found: false };
    finder.visit_block(block);
    finder.found
}

/// HIR visitor that validates ghost blocks don't move non-ghost values.
///
/// A move occurs when a non-Copy value is used without borrowing. This validator
/// checks for uses of non-ghost variables in consuming positions.
struct MoveValidator<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    /// Type checking results for the containing function
    typeck_results: &'a TypeckResults<'tcx>,
    /// Typing environment for the containing function, used to query rustc
    /// whether a type implements Copy.
    typing_env: TypingEnv<'tcx>,
    /// Variables declared inside the ghost block (these can be moved freely)
    bound_variables: HashSet<HirId>,
    /// Accumulated validation errors
    errors: Vec<GhostValidationError>,
}

impl<'tcx> Visitor<'tcx> for MoveValidator<'_, 'tcx> {
    fn visit_stmt(&mut self, stmt: &'tcx Stmt<'tcx>) {
        // Regular let statements are StmtKind::Let, not ExprKind::Let.
        // Validate the initializer because `let x = outer_var;` consumes `outer_var`.
        if let StmtKind::Let(let_stmt) = stmt.kind {
            if let Some(init) = let_stmt.init {
                self.check_potential_move(init);
            }
        }
        walk_stmt(self, stmt);
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        match &expr.kind {
            // Function call: `foo(arg)` - check if any arg is a move of non-ghost
            ExprKind::Call(_func, args) => {
                for arg in *args {
                    self.check_potential_move(arg);
                }
            }
            // Method call: `obj.method(args)` - check args (not receiver, it's borrowed)
            ExprKind::MethodCall(_path, _receiver, args, _span) => {
                for arg in *args {
                    self.check_potential_move(arg);
                }
            }
            // Struct expression: `Struct { field: value }` - check field values
            ExprKind::Struct(_path, fields, _base) => {
                for field in *fields {
                    self.check_potential_move(field.expr);
                }
            }
            // Tuple: `(a, b, c)` or Array literal: `[a, b, c]` - check each element
            ExprKind::Tup(elements) | ExprKind::Array(elements) => {
                for elem in *elements {
                    self.check_potential_move(elem);
                }
            }
            // Return: `return value` - check if returning a moved non-ghost
            ExprKind::Ret(Some(value)) => {
                self.check_potential_move(value);
            }
            // Block: `{ expr }` - check final expression (the block's value)
            ExprKind::Block(block, _) => {
                if let Some(final_expr) = block.expr {
                    self.check_potential_move(final_expr);
                }
            }
            // Match: `match scrutinee { ... }` - scrutinee is consumed
            ExprKind::Match(scrutinee, _arms, _source) => {
                self.check_potential_move(scrutinee);
            }
            _ => {}
        }
        // Continue walking the expression tree
        walk_expr(self, expr);
    }
}

impl<'tcx> MoveValidator<'_, 'tcx> {
    /// Check if an expression potentially moves a non-ghost value.
    fn check_potential_move(&mut self, expr: &'tcx Expr<'tcx>) {
        // Only check paths (variable references) that might be moves
        let ExprKind::Path(qpath) = &expr.kind else {
            return;
        };
        let rustc_hir::QPath::Resolved(_, path) = qpath else {
            return;
        };
        let rustc_hir::def::Res::Local(hir_id) = path.res else {
            return;
        };

        // Variables bound inside the ghost block can be moved freely
        if self.bound_variables.contains(&hir_id) {
            return;
        }

        // Get the type of this expression
        let ty = self.typeck_results.expr_ty(expr);

        // Ghost<T>/Snapshot<T> and logical types (Seq, FMap, FSet, Int) can be moved
        if is_ghost_like_type(self.tcx, ty)
            || is_trust_wp_logic_type(self.tcx, ty)
            || is_binding_from_ghost_like_init(self.tcx, self.typeck_results, hir_id)
        {
            return;
        }

        // Ask rustc whether the type implements Copy (covers user-defined Copy types)
        // Query keys must be region-free (`'?N` cannot be hashed); `Copy` is
        // decided modulo regions anyway, so erasing them changes no answer.
        let ty = self.tcx.erase_and_anonymize_regions(ty);
        if self.tcx.type_is_copy_modulo_regions(self.typing_env, ty) {
            return;
        }

        // This is a potential move of a non-Copy, non-Ghost value from outside the ghost block
        self.errors.push(GhostValidationError {
            span: expr.span,
            message: "cannot move non-ghost value in ghost block; consider borrowing with &"
                .to_string(),
        });
    }
}
