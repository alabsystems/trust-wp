// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Write validation for ghost blocks.
//!
//! Detects assignment expressions where the target is not a variable declared
//! inside the ghost block, and method/function calls that pass `&mut` references
//! to non-ghost variables.

use std::collections::HashSet;

use rustc_hir::{
    def_id::DefId,
    intravisit::{walk_expr, Visitor},
    Expr, ExprKind, HirId,
};
use rustc_middle::ty::{TyCtxt, TyKind, TypeckResults};

use super::{
    type_helpers::{
        binding_mut_borrow_target, is_binding_from_ghost_like_init, is_ghost_like_type,
        is_known_interior_mutability_mutator, is_mutable_reference_type,
        is_trust_wp_ghost_helper_method, is_trust_wp_logic_type, BoundVariableCollector,
    },
    GhostBlock, GhostValidationError,
};

/// Validate a single ghost block for writes to non-ghost variables.
///
/// This is a conservative HIR-level check that detects assignment expressions
/// where the target is not a variable declared inside the ghost block.
pub(super) fn validate_ghost_block_writes<'tcx>(
    tcx: TyCtxt<'tcx>,
    ghost_block: &GhostBlock,
    expr: &'tcx Expr<'tcx>,
) -> Vec<GhostValidationError> {
    let typeck_results = tcx.typeck(ghost_block.containing_fn);

    // First, collect all variables bound inside the ghost block
    let mut bound_collector = BoundVariableCollector::new();
    bound_collector.visit_expr(expr);

    // Then, find all assignments and check their targets
    let mut validator = WriteValidator {
        tcx,
        typeck_results,
        bound_variables: bound_collector.bound_variables,
        errors: Vec::new(),
    };
    validator.visit_expr(expr);

    validator.errors
}

/// HIR visitor that validates ghost blocks don't write to non-ghost variables.
struct WriteValidator<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    /// Type checking results for the containing function
    typeck_results: &'a TypeckResults<'tcx>,
    /// Variables declared inside the ghost block (these can be mutated)
    bound_variables: HashSet<HirId>,
    /// Accumulated validation errors
    errors: Vec<GhostValidationError>,
}

impl<'tcx> Visitor<'tcx> for WriteValidator<'_, 'tcx> {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        match &expr.kind {
            // Assignment: lhs = rhs
            ExprKind::Assign(lhs, _rhs, _span) => {
                self.check_write_target(lhs);
            }
            // AssignOp: lhs += rhs, etc
            ExprKind::AssignOp(_op, lhs, _rhs) => {
                self.check_write_target(lhs);
            }
            // Method call: `receiver.method(args...)`
            ExprKind::MethodCall(_path, receiver, args, _span) => {
                self.check_method_call_writes(expr, receiver, args);
            }
            // Function call: `func(args...)`
            ExprKind::Call(callee, args) => {
                self.check_function_call_writes(callee, args);
            }
            _ => {}
        }
        // Continue walking the expression tree
        walk_expr(self, expr);
    }
}

impl<'tcx> WriteValidator<'_, 'tcx> {
    /// Check method-call writes based on `&mut` parameters and known interior
    /// mutability mutators that expose mutation through `&self`.
    fn check_method_call_writes(
        &mut self,
        expr: &'tcx Expr<'tcx>,
        receiver: &'tcx Expr<'tcx>,
        args: &'tcx [Expr<'tcx>],
    ) {
        let Some(def_id) = self.typeck_results.type_dependent_def_id(expr.hir_id) else {
            return;
        };

        // Ghost helper methods (e.g., `push_back_ghost`, `pop_front_ghost`) are
        // specification-only operations defined on logic types (Seq, FMap, FSet).
        // These are erased at runtime and their `&mut self` receivers should not
        // trigger write validation errors. Part of #1581.
        if is_trust_wp_ghost_helper_method(self.tcx, def_id) {
            return;
        }

        self.check_call_arguments_for_mut_refs(def_id, Some(receiver), args);

        // `Cell`/`RefCell` mutators frequently expose writes through `&self`.
        // Treat these as writes on the receiver to fail closed.
        if is_known_interior_mutability_mutator(self.tcx, def_id) {
            self.check_write_operand(receiver);
        }
    }

    /// Check function-call writes based on `&mut` parameter positions.
    fn check_function_call_writes(&mut self, callee: &'tcx Expr<'tcx>, args: &'tcx [Expr<'tcx>]) {
        let Some(def_id) = self.call_def_id(callee) else {
            return;
        };

        self.check_call_arguments_for_mut_refs(def_id, None, args);
    }

    /// Resolve the DefId of a direct function call target if available.
    fn call_def_id(&self, callee: &'tcx Expr<'tcx>) -> Option<DefId> {
        if let TyKind::FnDef(def_id, _) = self.typeck_results.expr_ty(callee).kind() {
            return Some(*def_id);
        }

        if let ExprKind::Path(qpath) = &callee.kind {
            if let rustc_hir::def::Res::Def(_, def_id) =
                self.typeck_results.qpath_res(qpath, callee.hir_id)
            {
                return Some(def_id);
            }
        }

        None
    }

    /// For each `&mut` input in a callee signature, check the corresponding
    /// call operand as a potential write target.
    fn check_call_arguments_for_mut_refs(
        &mut self,
        def_id: DefId,
        receiver: Option<&'tcx Expr<'tcx>>,
        args: &'tcx [Expr<'tcx>],
    ) {
        let sig = self.tcx.fn_sig(def_id).instantiate_identity();
        let sig = sig.skip_binder();

        for (index, input_ty) in sig.inputs().iter().enumerate() {
            if !is_mutable_reference_type(*input_ty) {
                continue;
            }

            if let Some(receiver_expr) = receiver {
                if index == 0 {
                    self.check_write_operand(receiver_expr);
                    continue;
                }
                if let Some(arg) = args.get(index - 1) {
                    self.check_write_operand(arg);
                }
            } else if let Some(arg) = args.get(index) {
                self.check_write_operand(arg);
            }
        }
    }

    /// Normalize call operands (notably `&mut x`) to a write target expression.
    fn check_write_operand(&mut self, operand: &'tcx Expr<'tcx>) {
        if let ExprKind::AddrOf(_, _, inner) = &operand.kind {
            self.check_write_target(inner);
            return;
        }
        self.check_write_target(operand);
    }

    /// Check if the target of a write is a non-ghost variable.
    fn check_write_target(&mut self, target: &'tcx Expr<'tcx>) {
        // Handle paths (direct variable references)
        if let ExprKind::Path(qpath) = &target.kind {
            if let rustc_hir::QPath::Resolved(_, path) = qpath {
                // Get the definition this path refers to
                if let rustc_hir::def::Res::Local(hir_id) = path.res {
                    if self.bound_variables.contains(&hir_id) {
                        // A ghost-local binding may still alias an outer variable
                        // through `let alias = &mut outer;`. Follow that alias
                        // and validate writes against the original target.
                        if let Some(alias_target) = binding_mut_borrow_target(self.tcx, hir_id) {
                            self.check_write_target(alias_target);
                        }
                        return;
                    }

                    // Writes through Ghost<T>/Snapshot<T> or logical types
                    // (Seq, FMap, FSet, Int) are allowed — these are specification-only.
                    let target_ty = self.typeck_results.expr_ty(target);
                    let binding_ty = self.typeck_results.node_type(hir_id);
                    if is_ghost_like_type(self.tcx, target_ty)
                        || is_ghost_like_type(self.tcx, binding_ty)
                        || is_trust_wp_logic_type(self.tcx, target_ty)
                        || is_trust_wp_logic_type(self.tcx, binding_ty)
                        || is_binding_from_ghost_like_init(self.tcx, self.typeck_results, hir_id)
                    {
                        return;
                    }
                    // This is a write to a variable defined outside the ghost block
                    self.errors.push(GhostValidationError {
                        span: target.span,
                        message: "cannot write to non-ghost variable in ghost block".to_string(),
                    });
                }
            }
        }
        // Handle derefs: *ptr = value
        else if let ExprKind::Unary(rustc_hir::UnOp::Deref, inner) = &target.kind {
            // Recursively check the inner expression
            self.check_write_target(inner);
        }
        // Handle field access: obj.field = value
        else if let ExprKind::Field(base, _field) = &target.kind {
            // Check if the base is a non-ghost variable
            self.check_write_base(base);
        }
        // Handle indexing: arr[i] = value
        else if let ExprKind::Index(base, _index, _span) = &target.kind {
            // Check if the base is a non-ghost variable
            self.check_write_base(base);
        }
    }

    /// Check if the base of a compound write target is a non-ghost variable.
    fn check_write_base(&mut self, base: &'tcx Expr<'tcx>) {
        // For simplicity, we check if the base ultimately resolves to a non-ghost variable
        if let ExprKind::Path(qpath) = &base.kind {
            if let rustc_hir::QPath::Resolved(_, path) = qpath {
                if let rustc_hir::def::Res::Local(hir_id) = path.res {
                    if !self.bound_variables.contains(&hir_id) {
                        // Writes through Ghost<T>/Snapshot<T> or logical types are allowed.
                        let base_ty = self.typeck_results.expr_ty(base);
                        let binding_ty = self.typeck_results.node_type(hir_id);
                        if is_ghost_like_type(self.tcx, base_ty)
                            || is_ghost_like_type(self.tcx, binding_ty)
                            || is_trust_wp_logic_type(self.tcx, base_ty)
                            || is_trust_wp_logic_type(self.tcx, binding_ty)
                            || is_binding_from_ghost_like_init(
                                self.tcx,
                                self.typeck_results,
                                hir_id,
                            )
                        {
                            return;
                        }
                        // Writing to a field/index of a non-ghost variable
                        self.errors.push(GhostValidationError {
                            span: base.span,
                            message:
                                "cannot write to field/index of non-ghost variable in ghost block"
                                    .to_string(),
                        });
                    }
                }
            }
        }
        // Handle nested derefs, fields, etc.
        else if let ExprKind::Unary(rustc_hir::UnOp::Deref, inner) = &base.kind {
            self.check_write_base(inner);
        } else if let ExprKind::AddrOf(_, _, inner) = &base.kind {
            self.check_write_base(inner);
        } else if let ExprKind::Field(inner_base, _) = &base.kind {
            self.check_write_base(inner_base);
        }
    }
}
