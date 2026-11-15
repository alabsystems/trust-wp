// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! HIR-side collection of source ghost assignments.
//!
//! This is intentionally a small data-collection hook. It records source-level
//! ghost writes that MIR can erase, but it does not decide control-flow path or
//! inject verifier facts.

#![allow(dead_code)]

use std::collections::HashSet;

use rustc_ast::LitKind;
use rustc_hir::{
    def::{DefKind, Res},
    intravisit::{walk_expr, Visitor},
    Expr, ExprKind, HirId, QPath, UnOp,
};
use rustc_middle::ty::{TyCtxt, TypeckResults};
use rustc_span::Span;
use trust_wp_core::formula::{
    internal::tuple_lowering::tuple_logic_fn_name, BinOp, PureExpr, UnOp as PureUnOp,
};

use super::{
    type_helpers::{is_binding_from_ghost_like_init, is_ghost_like_type},
    GhostBlock,
};

/// A direct source assignment to a ghost-like local inside a `ghost!` block.
#[derive(Debug, Clone)]
pub(crate) struct GhostSourceAssignment {
    /// Function or closure containing the ghost block.
    pub(crate) containing_fn: rustc_hir::def_id::LocalDefId,
    /// HIR id of the containing ghost block expression.
    pub(crate) ghost_block_hir_id: HirId,
    /// Span of the containing ghost block expression.
    pub(crate) ghost_block_span: Span,
    /// Span of the full assignment expression.
    pub(crate) assignment_span: Span,
    /// Span of the assignment target.
    pub(crate) lhs_span: Span,
    /// Span of the assigned expression.
    pub(crate) rhs_span: Span,
    /// Source name of the direct local assignment target.
    pub(crate) lhs_name: String,
    /// Tuple field projection from the local assignment target, e.g. `p.0.1`
    /// becomes `[0, 1]`.
    pub(crate) lhs_tuple_fields: Vec<usize>,
    /// HIR id of the target local binding.
    pub(crate) lhs_hir_id: HirId,
    /// The containing body binds `lhs_name` more than once and the binding
    /// this write targets could not be found among them: the write may have
    /// changed any binding of that source name (D-237).
    pub(crate) lhs_binding_unresolved: bool,
    /// Structurally translated RHS expression when it is verifier-pure.
    pub(crate) rhs_expr: Option<PureExpr>,
    /// Best-effort RHS source text, for downstream matching/prototyping only.
    pub(crate) rhs_source: Option<String>,
    /// Whether the assignment target is a dereference (`*g = ..`) rather than a
    /// plain rebind (`g = ..`). Deref-mutations of a ghost value are erased into
    /// a `DerefMut::deref_mut` write chain in MIR, so the local-rebind tracking
    /// never sees them; this flag lets the consumer recover the post-block value.
    pub(crate) is_deref: bool,
}

/// Collect direct source assignments to ghost-like locals from all ghost blocks.
pub(crate) fn collect_ghost_source_assignments<'tcx>(
    tcx: TyCtxt<'tcx>,
    ghost_blocks: &[GhostBlock],
) -> Vec<GhostSourceAssignment> {
    let mut assignments = Vec::new();
    let mut seen_blocks = HashSet::new();

    for ghost_block in ghost_blocks {
        if !seen_blocks.insert(ghost_block.hir_id) {
            continue;
        }
        let expr = tcx.hir_node(ghost_block.hir_id).expect_expr();
        let typeck_results = tcx.typeck(ghost_block.containing_fn);
        let mut collector = SourceAssignmentCollector {
            tcx,
            typeck_results,
            ghost_block,
            assignments: Vec::new(),
            control_flow_depth: 0,
        };
        collector.visit_expr(expr);
        assignments.extend(collector.assignments);
    }

    assignments
}

struct SourceAssignmentCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck_results: &'a TypeckResults<'tcx>,
    ghost_block: &'a GhostBlock,
    assignments: Vec<GhostSourceAssignment>,
    control_flow_depth: usize,
}

impl<'tcx> Visitor<'tcx> for SourceAssignmentCollector<'_, 'tcx> {
    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if let ExprKind::Assign(lhs, rhs, _span) = expr.kind {
            self.record_direct_ghost_assignment(expr.span, lhs, rhs);
        }
        if is_branching_or_loop_expr(expr) {
            self.control_flow_depth += 1;
            walk_expr(self, expr);
            self.control_flow_depth -= 1;
            return;
        }
        walk_expr(self, expr);
    }
}

impl<'tcx> SourceAssignmentCollector<'_, 'tcx> {
    fn record_direct_ghost_assignment(
        &mut self,
        assignment_span: Span,
        lhs: &'tcx Expr<'tcx>,
        rhs: &'tcx Expr<'tcx>,
    ) {
        if self.control_flow_depth != 0 {
            return;
        }

        let Some((lhs_hir_id, lhs_name, lhs_tuple_fields)) = local_assignment_path(lhs) else {
            return;
        };

        let target_ty = self.typeck_results.expr_ty(lhs);
        let binding_ty = self.typeck_results.node_type(lhs_hir_id);
        if !is_ghost_like_type(self.tcx, target_ty)
            && !is_ghost_like_type(self.tcx, binding_ty)
            && !is_binding_from_ghost_like_init(self.tcx, self.typeck_results, lhs_hir_id)
        {
            return;
        }

        // The HIR names the target by source name; a body that binds that
        // name more than once names each binding apart (D-237), so the write
        // targets the binding the HIR resolved it to, or, when the body has no
        // binding of that name, every binding of the name.
        let identity = crate::mir_analysis::binding_identity::hir_binding_debug_name(
            self.tcx, &lhs_name, lhs_hir_id,
        );
        let lhs_binding_unresolved = identity != lhs_name
            && !crate::callbacks::try_get_body_with_context(
                self.tcx,
                self.ghost_block.containing_fn,
            )
            .is_some_and(|body| {
                body.body
                    .var_debug_info
                    .iter()
                    .any(|debug| debug.name.as_str() == identity)
            });
        let lhs_name = if lhs_binding_unresolved {
            lhs_name
        } else {
            identity
        };

        let rhs_source = self.tcx.sess.source_map().span_to_snippet(rhs.span).ok();
        let rhs_expr = hir_expr_to_pure(rhs);
        let is_deref = matches!(lhs.kind, ExprKind::Unary(UnOp::Deref, _));
        self.assignments.push(GhostSourceAssignment {
            containing_fn: self.ghost_block.containing_fn,
            ghost_block_hir_id: self.ghost_block.hir_id,
            ghost_block_span: self.ghost_block.span,
            assignment_span,
            lhs_span: lhs.span,
            rhs_span: rhs.span,
            lhs_name,
            lhs_tuple_fields,
            lhs_hir_id,
            lhs_binding_unresolved,
            rhs_expr,
            rhs_source,
            is_deref,
        });
    }
}

fn is_branching_or_loop_expr(expr: &Expr<'_>) -> bool {
    matches!(
        expr.kind,
        ExprKind::Closure(..) | ExprKind::If(..) | ExprKind::Match(..) | ExprKind::Loop(..)
    )
}

fn local_assignment_path(expr: &Expr<'_>) -> Option<(HirId, String, Vec<usize>)> {
    if let ExprKind::Unary(UnOp::Deref, inner) = &expr.kind {
        return local_assignment_path(inner);
    }

    if let ExprKind::Field(base, field_ident) = &expr.kind {
        let (hir_id, name, mut fields) = local_assignment_path(base)?;
        let field_idx = field_ident.name.as_str().parse::<usize>().ok()?;
        fields.push(field_idx);
        return Some((hir_id, name, fields));
    }

    let ExprKind::Path(QPath::Resolved(_, path)) = &expr.kind else {
        return None;
    };
    let rustc_hir::def::Res::Local(hir_id) = path.res else {
        return None;
    };
    let name = path.segments.last()?.ident.name.to_string();
    Some((hir_id, name, Vec::new()))
}

fn hir_expr_to_pure(expr: &Expr<'_>) -> Option<PureExpr> {
    match expr.kind {
        ExprKind::Lit(lit) => match lit.node {
            LitKind::Bool(value) => Some(PureExpr::Bool(value)),
            LitKind::Int(value, _) => i64::try_from(value.get()).ok().map(PureExpr::Int),
            _ => None,
        },
        ExprKind::Unary(UnOp::Neg, inner) => match hir_expr_to_pure(inner)? {
            PureExpr::Int(value) => Some(PureExpr::Int(-value)),
            other => Some(PureExpr::UnOp(PureUnOp::Neg, std::sync::Arc::new(other))),
        },
        ExprKind::Binary(op, lhs, rhs) => {
            let op = match op.node {
                rustc_hir::BinOpKind::Add => BinOp::Add,
                rustc_hir::BinOpKind::Sub => BinOp::Sub,
                rustc_hir::BinOpKind::Mul => BinOp::Mul,
                // Rust / Creusot `Int` `/` and `%` truncate toward zero.
                rustc_hir::BinOpKind::Div => BinOp::DivTrunc,
                rustc_hir::BinOpKind::Rem => BinOp::RemTrunc,
                rustc_hir::BinOpKind::Eq => BinOp::Eq,
                rustc_hir::BinOpKind::Lt => BinOp::Lt,
                rustc_hir::BinOpKind::Le => BinOp::Le,
                rustc_hir::BinOpKind::Ne => BinOp::Ne,
                rustc_hir::BinOpKind::Ge => BinOp::Ge,
                rustc_hir::BinOpKind::Gt => BinOp::Gt,
                rustc_hir::BinOpKind::And => BinOp::And,
                rustc_hir::BinOpKind::Or => BinOp::Or,
                _ => return None,
            };
            Some(PureExpr::BinOp(
                std::sync::Arc::new(hir_expr_to_pure(lhs)?),
                op,
                std::sync::Arc::new(hir_expr_to_pure(rhs)?),
            ))
        }
        ExprKind::Tup(items) => {
            let args = items
                .iter()
                .map(|item| hir_expr_to_pure(item))
                .collect::<Option<Vec<_>>>()?;
            Some(PureExpr::LogicFnCall {
                name: tuple_logic_fn_name(args.len()),
                args,
            })
        }
        // Single-field tuple-struct / tuple-variant constructor, e.g.
        // `NonCopy(4)`. Mirror the codebase's single-field collapse (a
        // one-field aggregate is represented by its inner value — see
        // `translate_rvalue`'s ADT/tuple handling), so a ghost write
        // `*g = NonCopy(4)` threads the inner scalar just as the initial
        // `ghost!(NonCopy(3))` seeds `g -> 3`. Only single-argument
        // constructors collapse this way; wider constructors are left
        // untranslated. (ghost/typing)
        ExprKind::Call(callee, [arg]) if is_tuple_ctor_callee(callee) => hir_expr_to_pure(arg),
        _ => None,
    }
}

/// Whether a call's callee resolves to a tuple-struct or tuple-variant
/// constructor (`DefKind::Ctor`), i.e. the call is `Ctor(arg, ...)` value
/// construction rather than an ordinary function call.
fn is_tuple_ctor_callee(callee: &Expr<'_>) -> bool {
    let ExprKind::Path(QPath::Resolved(_, path)) = &callee.kind else {
        return false;
    };
    matches!(path.res, Res::Def(DefKind::Ctor(..), _))
}

#[cfg(test)]
mod tests {
    use std::{
        fs,
        sync::atomic::{AtomicU64, Ordering},
    };

    use rustc_driver::{run_compiler, Callbacks, Compilation};
    use rustc_interface::interface::Compiler;
    use rustc_middle::ty::TyCtxt;
    use trust_wp_core::formula::PureExpr;

    use super::{collect_ghost_source_assignments, GhostSourceAssignment};
    use crate::ghost::find_ghost_blocks;

    static TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

    #[derive(Default)]
    struct AssignmentProbe {
        assignments: Vec<GhostSourceAssignment>,
        ran: bool,
    }

    impl Callbacks for AssignmentProbe {
        fn after_expansion<'tcx>(
            &mut self,
            _compiler: &Compiler,
            tcx: TyCtxt<'tcx>,
        ) -> Compilation {
            crate::callbacks::thread_locals::with_mir_session(tcx, || {
                let _ = tcx.analysis(());
                let ghost_blocks = find_ghost_blocks(tcx);
                self.assignments = collect_ghost_source_assignments(tcx, &ghost_blocks);
                self.ran = true;
                Compilation::Stop
            })
        }
    }

    fn collect_from_source(source: &str) -> AssignmentProbe {
        let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
        let temp_dir = std::env::temp_dir().join(format!(
            "trust_wp_ghost_source_assignment_test_{}_{}",
            std::process::id(),
            unique
        ));
        fs::create_dir_all(&temp_dir).expect("create test temp dir");

        let source_path = temp_dir.join("test.rs");
        fs::write(&source_path, source).expect("write test source");

        let units = trust_wp_test_utils::unit_dirs::UnitDirs::of_current_exe();
        // rustc emits artifacts using crate-name form (underscores), and
        // `--cfg` / `--extern` both consume crate-name form. The hyphenated
        // package name `trust-wp` maps to crate name `trust_wp`.
        let trust_wp_artifact = units.artifact("trust_wp", &["rmeta", "rlib"]);
        let trust_wp_std_artifact = units.artifact("trust_wp_std", &["rmeta", "rlib"]);

        let mut args = vec![
            "rustc".to_string(),
            source_path.to_string_lossy().into_owned(),
            "--crate-name".to_string(),
            "trust_wp_ghost_source_assignment_test".to_string(),
            "--crate-type".to_string(),
            "lib".to_string(),
            "--edition=2021".to_string(),
            "--cfg".to_string(),
            "trust_wp".to_string(),
            "--extern".to_string(),
            format!("trust_wp={}", trust_wp_artifact.display()),
            "--extern".to_string(),
            format!("trust_wp_std={}", trust_wp_std_artifact.display()),
            "--out-dir".to_string(),
            temp_dir.to_string_lossy().into_owned(),
        ];
        args.extend(units.search_args());

        let mut callbacks = AssignmentProbe::default();
        run_compiler(&args, &mut callbacks);

        let _ = fs::remove_file(&source_path);
        let _ = fs::remove_dir_all(&temp_dir);

        assert!(callbacks.ran, "assignment probe callback should run");
        callbacks
    }

    #[test]
    fn collects_nested_callback_direct_ghost_assignment() {
        let source = r#"
            use trust_wp::{ghost, Ghost};

            pub fn callback_shape() {
                let mut data_own: Ghost<Option<i32>> = Ghost::new(None);
                let mut runtime = 0;
                let mut callback = || {
                    let mut inner = || {
                        let _ = ghost! {
                            data_own = Ghost::new(Some(1));
                            runtime = 7;
                        };
                    };
                    inner();
                };
                callback();
                let _ = runtime;
            }
        "#;

        let probe = collect_from_source(source);
        assert_eq!(
            probe.assignments.len(),
            1,
            "collector should keep the Ghost<T> write and ignore program writes: {:?}",
            probe.assignments
        );

        let assignment = &probe.assignments[0];
        assert_eq!(assignment.lhs_name, "data_own");
        assert!(
            assignment
                .rhs_source
                .as_deref()
                .is_some_and(|source| source.contains("Ghost::new(Some(1))")),
            "expected RHS source to mention Ghost::new(Some(1)): {:?}",
            assignment.rhs_source
        );
        assert!(
            assignment.assignment_span.lo() >= assignment.lhs_span.lo()
                && assignment.assignment_span.hi() >= assignment.rhs_span.hi(),
            "assignment span should cover the lhs/rhs spans"
        );
        assert!(
            assignment.assignment_span.lo() >= assignment.ghost_block_span.lo()
                && assignment.assignment_span.hi() <= assignment.ghost_block_span.hi(),
            "assignment span should be inside the ghost block"
        );
    }

    #[test]
    fn collects_unconditional_tuple_field_ghost_assignment() {
        let source = r#"
            use trust_wp::{ghost, Ghost};

            pub fn tuple_field_write() {
                let mut p: Ghost<(i32, i32)> = Ghost::new((2, 3));
                let _ = ghost! {
                    p.0 = 4;
                    if true {
                        p.1 = 9;
                    }
                };
            }
        "#;

        let probe = collect_from_source(source);
        assert_eq!(
            probe.assignments.len(),
            1,
            "collector should keep only unconditional ghost tuple writes: {:?}",
            probe.assignments
        );

        let assignment = &probe.assignments[0];
        assert_eq!(assignment.lhs_name, "p");
        assert_eq!(assignment.lhs_tuple_fields, vec![0]);
        assert_eq!(assignment.rhs_expr, Some(PureExpr::Int(4)));
    }
}
