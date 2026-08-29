// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! MIR-level ghost erasure soundness check.
//!
//! Defense-in-depth validation that ghost code cannot influence runtime behavior.
//! Complements the HIR-level checks in [`super::write_validation`] and
//! [`super::move_validation`] by operating on post-borrowck MIR where all
//! desugaring and borrow analysis is complete.
//!
//! # Checks performed
//!
//! 1. **Ghost control-flow dependency:** A `SwitchInt` terminator outside a
//!    ghost region branches on a ghost-derived local. This means runtime
//!    control flow depends on a ghost value — a soundness violation.
//!
//! # Why not check all reads?
//!
//! The `ghost!` macro expands to `if false { Ghost::new({...}) } else { Ghost::conjure() }`.
//! At the MIR level, Ghost<T> locals are legitimately read outside ghost spans as
//! part of the macro infrastructure (e.g., assigning the conjure() result). These
//! reads are harmless because cfg-gating erases ghost code at runtime. The
//! remaining soundness concern is runtime control-flow dependency.
//!
//! # Design Reference
//!
//! See `designs/2026-02-18-ghost-pipeline-creusot-gap-analysis.md`, Gap 3.
//! Part of #1768.

use std::{
    collections::{HashMap, HashSet, VecDeque},
    fmt,
};

use log::debug;
use rustc_hir::{
    def::{DefKind, Res},
    def_id::{DefId, LocalDefId},
    Expr, ExprKind, HirId, PatKind, QPath, Stmt, StmtKind, UnOp,
};
use rustc_middle::{
    mir::{Body, Local, Operand, Rvalue, StatementKind, TerminatorKind, RETURN_PLACE},
    ty::{TyCtxt, TyKind},
};
use rustc_span::Span;

use super::{type_helpers::is_ghost_like_type, GhostBlock, GhostValidationError};
use crate::callbacks::thread_locals::try_get_body_with_context;

/// Validate source-level `#[erasure(target)]` attributes.
///
/// Creusot requires the erased body to match the target body. This pass covers
/// the expression shapes that currently appear in the compat suite: direct
/// returns, calls with const-generic arguments, simple binary expressions, and
/// the subset of block / method / tuple / ghost-projection forms that the
/// compat suite under `tests/should_succeed/specification/erasure.rs` exercises.
pub(crate) fn validate_erasure_attributes(tcx: TyCtxt<'_>) -> Vec<GhostValidationError> {
    let local_crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE).to_string();
    if matches!(
        local_crate_name.as_str(),
        "trust_wp_std" | "trust-wp" | "creusot_std" | "creusot_contracts" | "trust_wp_lib"
    ) {
        return Vec::new();
    }

    let local_fns_by_name = collect_local_functions_by_name(tcx);
    let mut errors = Vec::new();

    for local_def_id in tcx.hir_body_owners() {
        let hir_id = tcx.local_def_id_to_hir_id(local_def_id);
        let attrs = tcx.hir_attrs(hir_id);
        let erasure_targets = crate::attr_utils::get_erasure_targets(attrs);
        if erasure_targets.is_empty() {
            continue;
        }

        // Creusot parity: `#[trusted]` subjects are axiomatically accepted —
        // the developer asserts the erasure equivalence without proof. See
        // `reference/creusot/creusot/src/validate/erasure.rs` (`check_erasure`,
        // `is_trusted_item(ctx.tcx, left)` short-circuit).
        if has_trusted_doc_marker(attrs) {
            continue;
        }

        for target in erasure_targets {
            if target.trim() == "_" {
                continue;
            }
            let Some(target_def_id) = resolve_erasure_target(tcx, &local_fns_by_name, &target)
            else {
                errors.push(GhostValidationError {
                    span: tcx.def_span(local_def_id),
                    message: format!("#[erasure] target `{target}` must resolve to a function"),
                });
                continue;
            };

            let Some(target_expr) = canonical_erasure_body(tcx, target_def_id) else {
                errors.push(GhostValidationError {
                    span: tcx.def_span(local_def_id),
                    message: "#[erasure] target must have a body".to_string(),
                });
                continue;
            };
            let Some(erasure_expr) = canonical_erasure_body(tcx, local_def_id) else {
                continue;
            };

            if erasure_expr.expr != target_expr.expr {
                errors.push(GhostValidationError {
                    span: erasure_expr.span,
                    message: format!(
                        "failed #[erasure] check for {}: target expression `{}` does not match erasure expression `{}`",
                        tcx.def_path_str(local_def_id),
                        target_expr.expr,
                        erasure_expr.expr
                    ),
                });
            }
        }
    }

    errors
}

/// Local mirror of `callbacks::discovery::trusted::has_trusted_doc_marker`.
///
/// The proc macro emits `#[doc = "trust-wp:trusted:"]` for items marked with
/// `#[trusted]`. We replicate the detection here rather than reach into the
/// private `callbacks::discovery` module from the ghost layer.
fn has_trusted_doc_marker(attrs: &[rustc_hir::Attribute]) -> bool {
    attrs
        .iter()
        .filter_map(crate::attr_utils::doc_marker_str)
        .any(|value| value.as_str().starts_with("trust-wp:trusted:"))
}

fn collect_local_functions_by_name(tcx: TyCtxt<'_>) -> HashMap<String, Vec<LocalDefId>> {
    let mut local_fns_by_name: HashMap<String, Vec<LocalDefId>> = HashMap::new();
    for local_def_id in tcx.iter_local_def_id() {
        let def_id = local_def_id.to_def_id();
        if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
            continue;
        }
        local_fns_by_name
            .entry(tcx.item_name(def_id).as_str().to_string())
            .or_default()
            .push(local_def_id);
    }
    local_fns_by_name
}

fn resolve_erasure_target(
    tcx: TyCtxt<'_>,
    local_fns_by_name: &HashMap<String, Vec<LocalDefId>>,
    target: &str,
) -> Option<LocalDefId> {
    let target_name = erasure_target_base_name(target)?;
    let candidates = local_fns_by_name.get(&target_name)?;
    candidates
        .iter()
        .copied()
        .find(|candidate| tcx.hir_node_by_def_id(*candidate).body_id().is_some())
        .or_else(|| candidates.first().copied())
}

fn erasure_target_base_name(target: &str) -> Option<String> {
    let compact: String = target.chars().filter(|ch| !ch.is_whitespace()).collect();

    // For UFCS targets like `<Type as Trait>::method`, the method name follows
    // the closing `>::`. Strip the entire qualifier before the trailing path.
    let after_qualifier: &str = if compact.starts_with('<') {
        compact
            .find(">::")
            .map_or(compact.as_str(), |idx| &compact[idx + 3..])
    } else {
        compact.as_str()
    };

    // For paths with const-generic suffix like `baz::<42>`, drop everything
    // from the first `<` onward (not the leading `<` of a UFCS qualifier).
    let without_generics = after_qualifier
        .find("::<")
        .or_else(|| after_qualifier.find('<'))
        .map_or(after_qualifier, |index| &after_qualifier[..index]);

    without_generics
        .rsplit("::")
        .next()
        .filter(|name| !name.is_empty())
        .map(str::to_string)
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct CanonicalErasureBody {
    expr: ErasedExpr,
    span: Span,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ErasedExpr {
    Unit,
    Param(usize),
    /// A locally-bound variable, alpha-renamed by traversal order so the
    /// Nth fresh binding seen in each body matches the Nth fresh binding in
    /// the other body. Equates `let a = ...; a` across two bodies that
    /// happen to use different HIR ids.
    Local(String),
    Path(String),
    Lit(String),
    Call {
        callee: String,
        args: Vec<ErasedExpr>,
    },
    Binary {
        op: String,
        lhs: Box<ErasedExpr>,
        rhs: Box<ErasedExpr>,
    },
    /// Reborrow / autoref normalization: `&inner` — collapsed with `Deref`
    /// where applicable.
    AddrOf(Box<ErasedExpr>),
    /// `*inner` — symmetric to AddrOf.
    Deref(Box<ErasedExpr>),
    /// Field projection (`expr.field_name`).
    Field {
        base: Box<ErasedExpr>,
        field: String,
    },
    /// Block expression: a sequence of statements followed by a tail expression.
    Block {
        stmts: Vec<ErasedStmt>,
        tail: Box<ErasedExpr>,
    },
    /// `if cond { then } else { else_ }`.
    If {
        cond: Box<ErasedExpr>,
        then: Box<ErasedExpr>,
        else_: Box<ErasedExpr>,
    },
    Unsupported(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ErasedStmt {
    Let {
        pattern: String,
        init: ErasedExpr,
    },
    Expr(ErasedExpr),
    Assign {
        place: ErasedExpr,
        value: ErasedExpr,
    },
    AssignOp {
        op: String,
        place: ErasedExpr,
        value: ErasedExpr,
    },
    /// `while cond { body }`. The `#[invariant(...)]` attribute on the loop
    /// is stripped during canonicalization so a `while false {}` in the
    /// target matches `#[invariant(false)] while false {}` in the subject.
    While {
        cond: ErasedExpr,
        body: ErasedExpr,
    },
}

impl fmt::Display for ErasedExpr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErasedExpr::Unit => write!(f, "()"),
            ErasedExpr::Param(index) => write!(f, "${index}"),
            ErasedExpr::Local(name) => write!(f, "{name}"),
            ErasedExpr::Path(path) | ErasedExpr::Lit(path) | ErasedExpr::Unsupported(path) => {
                write!(f, "{path}")
            }
            ErasedExpr::Call { callee, args } => {
                write!(f, "{callee}(")?;
                for (index, arg) in args.iter().enumerate() {
                    if index > 0 {
                        write!(f, ",")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ")")
            }
            ErasedExpr::Binary { op, lhs, rhs } => write!(f, "({lhs} {op} {rhs})"),
            ErasedExpr::AddrOf(inner) => write!(f, "&{inner}"),
            ErasedExpr::Deref(inner) => write!(f, "*{inner}"),
            ErasedExpr::Field { base, field } => write!(f, "{base}.{field}"),
            ErasedExpr::Block { stmts, tail } => {
                write!(f, "{{")?;
                for stmt in stmts {
                    write!(f, "{stmt};")?;
                }
                write!(f, "{tail}}}")
            }
            ErasedExpr::If { cond, then, else_ } => {
                write!(f, "if({cond}){{{then}}}else{{{else_}}}")
            }
        }
    }
}

impl fmt::Display for ErasedStmt {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ErasedStmt::Let { pattern, init } => write!(f, "let {pattern}={init}"),
            ErasedStmt::Expr(expr) => write!(f, "{expr}"),
            ErasedStmt::Assign { place, value } => write!(f, "{place}={value}"),
            ErasedStmt::AssignOp { op, place, value } => write!(f, "{place}{op}={value}"),
            ErasedStmt::While { cond, body } => write!(f, "while({cond}){{{body}}}"),
        }
    }
}

fn canonical_erasure_body(
    tcx: TyCtxt<'_>,
    local_def_id: LocalDefId,
) -> Option<CanonicalErasureBody> {
    let body_id = tcx.hir_node_by_def_id(local_def_id).body_id()?;
    let body = tcx.hir_body(body_id);
    let typeck_results = tcx.typeck_body(body.id());
    let param_positions = body
        .params
        .iter()
        .enumerate()
        .filter_map(|(index, param)| match param.pat.kind {
            PatKind::Binding(_, hir_id, _, _) => Some((hir_id, index)),
            _ => None,
        })
        .collect::<HashMap<HirId, usize>>();
    let mut ctx = ErasureCtx {
        tcx,
        typeck_results,
        param_positions: &param_positions,
        local_names: HashMap::new(),
        next_local: 0,
    };
    Some(CanonicalErasureBody {
        expr: ctx.canonical_expr(body.value),
        span: body.value.span,
    })
}

struct ErasureCtx<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck_results: &'a rustc_middle::ty::TypeckResults<'tcx>,
    param_positions: &'a HashMap<HirId, usize>,
    /// Alpha-renaming: fresh names for HIR-local bindings. Two erasure
    /// bodies share name identity by traversal order — the Nth binding seen
    /// in each body gets the same fresh name. This lets `let a = foo(x); a`
    /// equate across bodies with different HirIds.
    local_names: HashMap<HirId, String>,
    next_local: usize,
}

impl<'tcx> ErasureCtx<'_, 'tcx> {
    fn fresh_local(&mut self) -> String {
        let name = format!("_v{}", self.next_local);
        self.next_local += 1;
        name
    }

    fn local_for(&mut self, hir_id: HirId) -> String {
        if let Some(name) = self.local_names.get(&hir_id) {
            return name.clone();
        }
        let name = self.fresh_local();
        self.local_names.insert(hir_id, name.clone());
        name
    }

    fn ghost_like(&self, ty: rustc_middle::ty::Ty<'tcx>) -> bool {
        is_ghost_like_type(self.tcx, ty)
    }

    fn canonical_expr(&mut self, expr: &Expr<'_>) -> ErasedExpr {
        // Only erase _leaf_ ghost values to Unit. Blocks and call expressions
        // can have ghost return types while containing meaningful runtime
        // sub-expressions (e.g., `quux2` returns `Ghost<Int>` but has
        // `let _ = foo2(*x, y);` as a runtime side-effecting statement). For
        // those non-leaf forms we recurse and let inner positions normalize.
        let ty = self.typeck_results.expr_ty(expr);
        if self.ghost_like(ty) && is_leaf_ghost_expr(expr) {
            return ErasedExpr::Unit;
        }
        self.canonical_expr_raw(expr)
    }

    fn canonical_expr_raw(&mut self, expr: &Expr<'_>) -> ErasedExpr {
        match expr.kind {
            ExprKind::DropTemps(inner) => self.canonical_expr(inner),
            ExprKind::Block(block, _) => self.canonical_block(expr, block),
            ExprKind::Ret(Some(inner)) => self.canonical_expr(inner),
            ExprKind::Tup(items) if items.is_empty() => ErasedExpr::Unit,
            ExprKind::Tup(items) => self.canonical_tuple(items),
            ExprKind::Lit(_) => ErasedExpr::Lit(normalized_span_snippet(self.tcx, expr.span)),
            ExprKind::Path(qpath) => self.canonical_path(&qpath, expr),
            ExprKind::Call(callee, args) => self.canonical_call(callee, args),
            ExprKind::MethodCall(_segment, receiver, args, _span) => {
                self.canonical_method_call(expr, receiver, args)
            }
            ExprKind::Binary(op, lhs, rhs) => ErasedExpr::Binary {
                op: format!("{:?}", op.node),
                lhs: Box::new(self.canonical_expr(lhs)),
                rhs: Box::new(self.canonical_expr(rhs)),
            },
            ExprKind::AddrOf(_, _, inner) => {
                let inner = self.canonical_expr(inner);
                strip_addrof_deref(ErasedExpr::AddrOf(Box::new(inner)))
            }
            ExprKind::Unary(UnOp::Deref, inner) => {
                let inner = self.canonical_expr(inner);
                strip_addrof_deref(ErasedExpr::Deref(Box::new(inner)))
            }
            ExprKind::Field(base, ident) => {
                let base = self.canonical_expr(base);
                ErasedExpr::Field {
                    base: Box::new(base),
                    field: ident.name.as_str().to_string(),
                }
            }
            ExprKind::If(cond, then, Some(else_)) => ErasedExpr::If {
                cond: Box::new(self.canonical_expr(cond)),
                then: Box::new(self.canonical_expr(then)),
                else_: Box::new(self.canonical_expr(else_)),
            },
            ExprKind::If(cond, then, None) => ErasedExpr::If {
                cond: Box::new(self.canonical_expr(cond)),
                then: Box::new(self.canonical_expr(then)),
                else_: Box::new(ErasedExpr::Unit),
            },
            // Closures appear in proof_assert! / snapshot! / ghost! macro
            // expansions as marker fences with no runtime effect.
            ExprKind::Closure(_) => ErasedExpr::Unit,
            // Loop expressions used directly as values (e.g., a tail-position
            // `while false {}` in a `()`-returning function). We model them
            // as a block containing a single while-statement so they equate
            // with semicolon-form loops in the other body.
            ExprKind::Loop(body, _label, _src, _span) => {
                if let Some((cond, body_expr)) = while_loop_components(body) {
                    let stmt = ErasedStmt::While {
                        cond: self.canonical_expr(cond),
                        body: self.canonical_expr(body_expr),
                    };
                    return ErasedExpr::Block {
                        stmts: vec![stmt],
                        tail: Box::new(ErasedExpr::Unit),
                    };
                }
                ErasedExpr::Unsupported(normalized_span_snippet(self.tcx, expr.span))
            }
            // `break` and `continue` inside lowered while-loops; we don't
            // need to model them precisely because we recognize the
            // outer while-shape via `while_loop_components`.
            ExprKind::Break(_, _) | ExprKind::Continue(_) => ErasedExpr::Unit,
            _ => ErasedExpr::Unsupported(normalized_span_snippet(self.tcx, expr.span)),
        }
    }

    fn canonical_block(&mut self, outer: &Expr<'_>, block: &rustc_hir::Block<'_>) -> ErasedExpr {
        let mut stmts: Vec<ErasedStmt> = Vec::new();
        for stmt in block.stmts {
            self.canonical_stmt(stmt, &mut stmts);
        }
        // Tail-expression handling. Ghost-typed tails erase to Unit. Loop
        // tails (`while cond { body }` lowering) are lifted into a While
        // statement so they equate with the same loop appearing as a
        // semicolon-terminated statement in the other body.
        let tail = match block.expr {
            Some(e) => {
                let ty = self.typeck_results.expr_ty(e);
                if self.ghost_like(ty) {
                    ErasedExpr::Unit
                } else if let ExprKind::Loop(body, _label, _src, _span) = e.kind {
                    if let Some((cond, body_expr)) = while_loop_components(body) {
                        stmts.push(ErasedStmt::While {
                            cond: self.canonical_expr(cond),
                            body: self.canonical_expr(body_expr),
                        });
                        ErasedExpr::Unit
                    } else {
                        self.canonical_expr(e)
                    }
                } else {
                    self.canonical_expr(e)
                }
            }
            None => ErasedExpr::Unit,
        };

        if stmts.is_empty() {
            return tail;
        }
        if matches!(tail, ErasedExpr::Unsupported(_)) || stmts.iter().any(stmt_is_unsupported) {
            return ErasedExpr::Unsupported(normalized_span_snippet(self.tcx, outer.span));
        }
        ErasedExpr::Block {
            stmts,
            tail: Box::new(tail),
        }
    }

    fn canonical_stmt(&mut self, stmt: &Stmt<'_>, out: &mut Vec<ErasedStmt>) {
        match stmt.kind {
            StmtKind::Let(let_stmt) => {
                let init_ty_is_ghost = let_stmt
                    .init
                    .map(|e| self.ghost_like(self.typeck_results.expr_ty(e)))
                    .unwrap_or(false);
                let pat_ty_is_ghost =
                    self.ghost_like(self.typeck_results.node_type(let_stmt.pat.hir_id));
                if init_ty_is_ghost || pat_ty_is_ghost {
                    return;
                }

                let init = let_stmt
                    .init
                    .map(|e| self.canonical_expr(e))
                    .unwrap_or(ErasedExpr::Unit);

                let pattern = self.canonical_pattern(let_stmt.pat);

                // Drop fully-erased let-statements. These cover Creusot
                // patterns like `let _ = snapshot!(...)`, where the RHS
                // ghost-strips to `()`, or `let (_, _) = ghost!{...}.split()`,
                // where the entire binding is over ghost components and the
                // pattern reduces to `()` after ghost-projection.
                let pat_is_wild =
                    matches!(let_stmt.pat.kind, PatKind::Wild) || pattern == "()" || pattern == "_";
                if pat_is_wild && canonical_is_runtime_inert(&init) {
                    return;
                }

                out.push(ErasedStmt::Let { pattern, init });
            }
            StmtKind::Expr(expr) | StmtKind::Semi(expr) => match expr.kind {
                ExprKind::Assign(place, value, _) => {
                    out.push(ErasedStmt::Assign {
                        place: self.canonical_expr(place),
                        value: self.canonical_expr(value),
                    });
                }
                ExprKind::AssignOp(op, place, value) => {
                    out.push(ErasedStmt::AssignOp {
                        op: format!("{:?}", op.node),
                        place: self.canonical_expr(place),
                        value: self.canonical_expr(value),
                    });
                }
                ExprKind::Loop(body, _label, _src, _span) => {
                    if let Some((cond, body_expr)) = while_loop_components(body) {
                        out.push(ErasedStmt::While {
                            cond: self.canonical_expr(cond),
                            body: self.canonical_expr(body_expr),
                        });
                        return;
                    }
                    out.push(ErasedStmt::Expr(self.canonical_expr(expr)));
                }
                _ => {
                    if expr_is_pure_ghost_call(self.tcx, self.typeck_results, expr) {
                        return;
                    }
                    // Even if this statement is ghost-typed, we keep it when
                    // the underlying expression carries non-ghost runtime
                    // effects (e.g., a call to a `#[erasure(target)]`-marked
                    // function — its runtime erasure is `target(args)`).
                    let stmt_ty_ghost = self.ghost_like(self.typeck_results.expr_ty(expr));
                    let canon = self.canonical_expr_raw(expr);
                    if stmt_ty_ghost && canonical_is_runtime_inert(&canon) {
                        return;
                    }
                    if matches!(canon, ErasedExpr::Unit) {
                        return;
                    }
                    out.push(ErasedStmt::Expr(canon));
                }
            },
            StmtKind::Item(_) => {}
        }
    }

    fn canonical_pattern(&mut self, pat: &rustc_hir::Pat<'_>) -> String {
        match pat.kind {
            PatKind::Wild => "_".to_string(),
            PatKind::Binding(_, hir_id, _ident, _) => self.local_for(hir_id),
            PatKind::Tuple(elems, _) => {
                // Project away ghost-typed sub-patterns so
                // `let (a, _) = foog(x)` (where the second slot is `Ghost<_>`)
                // canonicalizes to the same shape as `let a = foo(x)`.
                let mut kept: Vec<String> = Vec::new();
                for sub in elems {
                    if self.ghost_like(self.typeck_results.node_type(sub.hir_id)) {
                        continue;
                    }
                    kept.push(self.canonical_pattern(sub));
                }
                match kept.len() {
                    1 => kept.into_iter().next().unwrap(),
                    _ => format!("({})", kept.join(",")),
                }
            }
            PatKind::TupleStruct(_qpath, elems, _) => {
                let parts: Vec<String> = elems.iter().map(|p| self.canonical_pattern(p)).collect();
                format!("S({})", parts.join(","))
            }
            _ => normalized_span_snippet(self.tcx, pat.span),
        }
    }

    fn canonical_tuple(&mut self, items: &[Expr<'_>]) -> ErasedExpr {
        let mut kept: Vec<ErasedExpr> = Vec::new();
        for item in items {
            let item_ty = self.typeck_results.expr_ty(item);
            if self.ghost_like(item_ty) {
                continue;
            }
            kept.push(self.canonical_expr(item));
        }
        match kept.len() {
            0 => ErasedExpr::Unit,
            1 => kept.into_iter().next().unwrap(),
            _ => ErasedExpr::Call {
                callee: "tuple".to_string(),
                args: kept,
            },
        }
    }

    fn canonical_path(&mut self, qpath: &QPath<'_>, expr: &Expr<'_>) -> ErasedExpr {
        if let Res::Local(hir_id) = self.typeck_results.qpath_res(qpath, expr.hir_id) {
            if let Some(index) = self.param_positions.get(&hir_id) {
                return ErasedExpr::Param(*index);
            }
            return ErasedExpr::Local(self.local_for(hir_id));
        }
        if let Res::Def(_, def_id) = self.typeck_results.qpath_res(qpath, expr.hir_id) {
            let base_name = erased_callee_base_name(self.tcx, def_id);
            return ErasedExpr::Path(base_name);
        }
        ErasedExpr::Path(normalized_span_snippet(self.tcx, expr.span))
    }

    fn canonical_call(&mut self, callee: &Expr<'_>, args: &[Expr<'_>]) -> ErasedExpr {
        let callee_def_id_opt = callee_def_id(self.tcx, self.typeck_results, callee);
        let callee_name = canonical_erasure_callee(self.tcx, self.typeck_results, callee);

        if let Some(def_id) = callee_def_id_opt {
            let def_path = self.tcx.def_path_str(def_id);
            if is_perm_as_ref_or_mut(&def_path) {
                let mut non_ghost = self.non_ghost_args(args);
                if let Some(first) = non_ghost.pop_front() {
                    let deref = ErasedExpr::Deref(Box::new(first));
                    return strip_addrof_deref(ErasedExpr::AddrOf(Box::new(deref)));
                }
            }
        }

        let normalized_args: Vec<ErasedExpr> = self.non_ghost_args(args).into_iter().collect();
        ErasedExpr::Call {
            callee: callee_name,
            args: normalized_args,
        }
    }

    fn non_ghost_args(&mut self, args: &[Expr<'_>]) -> VecDeque<ErasedExpr> {
        let mut out = VecDeque::new();
        for arg in args {
            let ty = self.typeck_results.expr_ty(arg);
            if self.ghost_like(ty) {
                continue;
            }
            // Strip a single autoref / reborrow layer at the argument level.
            // This normalizes `takes_ref(&x)` to `takes_ref(x)` so it equates
            // with a method-call shape `x.takes_ref()` which canonicalizes
            // to `Call(takes_ref, [x])`.
            let canon = self.canonical_expr(arg);
            out.push_back(strip_outer_addrof(canon));
        }
        out
    }

    fn canonical_method_call(
        &mut self,
        method_expr: &Expr<'_>,
        receiver: &Expr<'_>,
        args: &[Expr<'_>],
    ) -> ErasedExpr {
        // Method calls whose receiver is ghost-typed (e.g.
        // `ghost!{...}.split()`) have no runtime effect and erase to Unit.
        let receiver_ty = self.typeck_results.expr_ty(receiver);
        if self.ghost_like(receiver_ty) {
            return ErasedExpr::Unit;
        }

        let method_def_id = self
            .typeck_results
            .type_dependent_def_id(method_expr.hir_id);
        let method_name = method_def_id
            .map(|did| erased_callee_base_name(self.tcx, did))
            .unwrap_or_else(|| normalized_span_snippet(self.tcx, method_expr.span));

        // `_perm` method aliasing: `s.as_ptr_perm()` returns
        // `(ptr, Ghost<...>)` but is semantically equivalent to `s.as_ptr()`.
        let canonical_method_name = method_name
            .strip_suffix("_perm")
            .map(str::to_string)
            .unwrap_or(method_name);

        let receiver_expr = self.canonical_expr(receiver);
        let mut all_args: Vec<ErasedExpr> = vec![receiver_expr];
        for arg in args {
            let ty = self.typeck_results.expr_ty(arg);
            if self.ghost_like(ty) {
                continue;
            }
            all_args.push(self.canonical_expr(arg));
        }

        ErasedExpr::Call {
            callee: canonical_method_name,
            args: all_args,
        }
    }
}

/// True if `expr` is a leaf ghost-typed value with no runtime sub-effects
/// worth preserving. We use this to decide between erasing to Unit and
/// recursing into the expression.
fn is_leaf_ghost_expr(expr: &Expr<'_>) -> bool {
    matches!(
        expr.kind,
        ExprKind::Path(_) | ExprKind::Lit(_) | ExprKind::Closure(_)
    )
}

/// True when an erased expression contains no observable runtime effects —
/// i.e., it's just a constant or a unit value. Used to decide whether to
/// drop a ghost-typed statement.
fn canonical_is_runtime_inert(expr: &ErasedExpr) -> bool {
    matches!(
        expr,
        ErasedExpr::Unit
            | ErasedExpr::Lit(_)
            | ErasedExpr::Path(_)
            | ErasedExpr::Param(_)
            | ErasedExpr::Local(_)
    )
}

fn stmt_is_unsupported(stmt: &ErasedStmt) -> bool {
    fn is_unsupported(expr: &ErasedExpr) -> bool {
        matches!(expr, ErasedExpr::Unsupported(_))
    }
    match stmt {
        ErasedStmt::Let { init, .. } => is_unsupported(init),
        ErasedStmt::Expr(e) => is_unsupported(e),
        ErasedStmt::Assign { place, value } | ErasedStmt::AssignOp { place, value, .. } => {
            is_unsupported(place) || is_unsupported(value)
        }
        ErasedStmt::While { cond, body } => is_unsupported(cond) || is_unsupported(body),
    }
}

/// Strip a single outermost `&` (AddrOf) layer. Used to normalize call
/// arguments so `f(&x)` matches `f(x)` and `x.f()` (after method-call
/// canonicalization, `x` is the receiver argument).
fn strip_outer_addrof(expr: ErasedExpr) -> ErasedExpr {
    match expr {
        ErasedExpr::AddrOf(inner) => *inner,
        other => other,
    }
}

/// Strip `&*x` ↔ `x` for reborrow / autoref normalization.
fn strip_addrof_deref(expr: ErasedExpr) -> ErasedExpr {
    match expr {
        ErasedExpr::AddrOf(inner) => match *inner {
            ErasedExpr::Deref(inner_inner) => *inner_inner,
            other => ErasedExpr::AddrOf(Box::new(other)),
        },
        ErasedExpr::Deref(inner) => match *inner {
            ErasedExpr::AddrOf(inner_inner) => *inner_inner,
            other => ErasedExpr::Deref(Box::new(other)),
        },
        other => other,
    }
}

/// Detect the `Perm::as_ref` / `Perm::as_mut` intrinsics by path string.
///
/// `tcx.def_path_str()` for impl methods can return forms like
/// `Perm::<*const T>::as_ref` or `trust_wp_std::ghost::Perm::<*const T>::as_ref`
/// depending on how rustc renders the impl segment, so we match on the trailing
/// segment plus a `Perm` ancestor.
fn is_perm_as_ref_or_mut(def_path: &str) -> bool {
    let trailing = def_path.rsplit("::").next().unwrap_or("");
    if !matches!(trailing, "as_ref" | "as_mut") {
        return false;
    }
    def_path.contains("Perm")
}

/// Detect calls that produce only verification-only side effects
/// (e.g. `proof_assert!` desugared to a closure).
fn expr_is_pure_ghost_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    typeck_results: &rustc_middle::ty::TypeckResults<'tcx>,
    expr: &Expr<'_>,
) -> bool {
    let ty = typeck_results.expr_ty(expr);
    if !ty.is_unit() {
        return false;
    }
    if let ExprKind::Call(callee, _) = expr.kind {
        if let Some(def_id) = callee_def_id(tcx, typeck_results, callee) {
            for attr in tcx.get_all_attrs(def_id) {
                if let Some(value) = crate::attr_utils::doc_marker_str(attr) {
                    let s = value.as_str();
                    if s.starts_with("trust-wp:ghost:")
                        || s.starts_with("trust-wp:proof_assert:")
                        || s.starts_with("trust-wp:trusted_proof_assert:")
                        || s.starts_with("trust-wp:snapshot:")
                    {
                        return true;
                    }
                }
            }
        }
    }
    false
}

/// Recognize `while cond { body }` from desugared HIR loops.
///
/// Rust lowers `while cond { body }` to
/// `loop { if cond { body } else { break; } }`. We pattern-match on that
/// shape so `#[invariant(false)] while false {}` (whose attribute is
/// stripped during canonicalization) matches a target `while false {}`.
fn while_loop_components<'a>(
    body: &'a rustc_hir::Block<'a>,
) -> Option<(&'a Expr<'a>, &'a Expr<'a>)> {
    if !body.stmts.is_empty() {
        return None;
    }
    let outer = body.expr?;
    match outer.kind {
        ExprKind::If(cond, then, Some(_)) => Some((cond, then)),
        _ => None,
    }
}

fn canonical_erasure_callee(
    tcx: TyCtxt<'_>,
    typeck_results: &rustc_middle::ty::TypeckResults<'_>,
    callee: &Expr<'_>,
) -> String {
    let base_name = callee_def_id(tcx, typeck_results, callee)
        .map(|def_id| erased_callee_base_name(tcx, def_id))
        .unwrap_or_else(|| normalized_callee_base_snippet(tcx, callee.span));
    let generic_suffix = generic_suffix_from_callee_snippet(tcx, callee.span);
    format!("{base_name}{generic_suffix}")
}

fn callee_def_id(
    _tcx: TyCtxt<'_>,
    typeck_results: &rustc_middle::ty::TypeckResults<'_>,
    callee: &Expr<'_>,
) -> Option<DefId> {
    if let TyKind::FnDef(def_id, _) = typeck_results.expr_ty(callee).kind() {
        return Some(*def_id);
    }
    if let ExprKind::Path(qpath) = &callee.kind {
        if let Res::Def(_, def_id) = typeck_results.qpath_res(qpath, callee.hir_id) {
            return Some(def_id);
        }
    }
    None
}

fn erased_callee_base_name(tcx: TyCtxt<'_>, def_id: DefId) -> String {
    crate::attr_utils::get_erasure_targets(tcx.get_all_attrs(def_id))
        .first()
        .and_then(|target| erasure_target_base_name(target))
        .unwrap_or_else(|| tcx.item_name(def_id).as_str().to_string())
}

fn generic_suffix_from_callee_snippet(tcx: TyCtxt<'_>, span: Span) -> String {
    let snippet = normalized_span_snippet(tcx, span);
    if let Some(index) = snippet.find("::<") {
        return snippet[index + 2..].to_string();
    }
    if let Some(index) = snippet.find('<') {
        return snippet[index..].to_string();
    }
    String::new()
}

fn normalized_callee_base_snippet(tcx: TyCtxt<'_>, span: Span) -> String {
    erasure_target_base_name(&normalized_span_snippet(tcx, span))
        .unwrap_or_else(|| normalized_span_snippet(tcx, span))
}

fn normalized_span_snippet(tcx: TyCtxt<'_>, span: Span) -> String {
    tcx.sess
        .source_map()
        .span_to_snippet(span)
        .unwrap_or_else(|_| format!("{span:?}"))
        .chars()
        .filter(|ch| !ch.is_whitespace())
        .collect()
}

/// Run the MIR-level erasure check for all functions containing ghost blocks.
///
/// For each function, retrieves the post-borrowck MIR body, identifies ghost
/// locals, and checks that no `SwitchInt` branches on them outside ghost regions.
pub(crate) fn check_ghost_erasure<'tcx>(
    tcx: TyCtxt<'tcx>,
    ghost_blocks: &[GhostBlock],
) -> Vec<GhostValidationError> {
    if ghost_blocks.is_empty() {
        return Vec::new();
    }

    // A `ghost!{ ... }` block may lexically contain nested closures (e.g.,
    // `ghost! { |c| { inv.open(tokens.into_inner(), |inv| ...) } }`). Each
    // closure becomes its own body owner with its own MIR, but the closure
    // body's terminator spans are nested inside the outer ghost span. Build
    // a global span list so the per-body check can recognise every ghost
    // region regardless of which closure registered the block. (#message-passing)
    let global_ghost_spans: Vec<Span> = ghost_blocks.iter().map(|block| block.span).collect();

    // Bodies that themselves register a ghost block are processed below.
    // Bodies without their own ghost blocks still get checked because the
    // global span list lets `check_body_for_ghost_leaks` recognise their
    // terminators as ghost-enclosed when applicable.
    let mut bodies_to_check: std::collections::HashSet<rustc_hir::def_id::LocalDefId> =
        ghost_blocks
            .iter()
            .map(|block| block.containing_fn)
            .collect();
    // Also include every body owner whose body span intersects a known ghost
    // span — these are the inner closures created inside `ghost! { ... }`.
    for local_def_id in tcx.hir_body_owners() {
        if bodies_to_check.contains(&local_def_id) {
            continue;
        }
        let body = tcx.hir_body_owned_by(local_def_id);
        let body_span = body.value.span;
        if global_ghost_spans
            .iter()
            .any(|gs| gs.contains(body_span) || body_span.contains(*gs))
        {
            bodies_to_check.insert(local_def_id);
        }
    }

    let mut errors = Vec::new();

    for def_id in &bodies_to_check {
        let body_with_facts = try_get_body_with_context(*def_id);
        let Some(body_with_facts) = body_with_facts else {
            debug!(
                "erasure check: no MIR body for {:?}, skipping",
                tcx.def_path_str(*def_id)
            );
            continue;
        };
        let body = &body_with_facts.body;

        // Step 1: Identify ghost locals and locals derived from ghost values.
        let ghost_dependent_locals = find_ghost_dependent_locals(tcx, body);
        if ghost_dependent_locals.is_empty() {
            continue;
        }

        debug!(
            "erasure check: {} ghost-dependent locals in {:?}",
            ghost_dependent_locals.len(),
            tcx.def_path_str(*def_id)
        );

        // Step 2: Walk MIR and check for ghost reads outside ghost regions
        let fn_errors =
            check_body_for_ghost_leaks(body, &ghost_dependent_locals, &global_ghost_spans);
        errors.extend(fn_errors);
    }

    errors
}

/// Check whether a candidate program function returns runtime data derived
/// from Ghost/Snapshot inputs.
///
/// This is intentionally body-level rather than signature-level. Creusot-style
/// code often passes `Ghost<T>`/`Snapshot<T>` as proof authority to ordinary
/// functions; that is sound as long as the erased runtime result is not derived
/// from the ghost value.
pub(crate) fn check_ghost_type_escape_body<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &Body<'tcx>,
    ghost_spans: &[Span],
    def_path: &str,
    output: rustc_middle::ty::Ty<'tcx>,
) -> Vec<GhostValidationError> {
    let ghost_dependent_locals = find_ghost_dependent_locals(tcx, body);
    if ghost_dependent_locals.is_empty() {
        return Vec::new();
    }

    let mut errors = check_body_for_ghost_leaks(body, &ghost_dependent_locals, ghost_spans)
        .into_iter()
        .map(|mut error| {
            error.message = format!("ghost type escape: function `{def_path}` {}", error.message);
            error
        })
        .collect::<Vec<_>>();

    if ghost_dependent_locals.contains(&RETURN_PLACE) {
        let span = body.local_decls[RETURN_PLACE].source_info.span;
        errors.push(GhostValidationError {
            span,
            message: format!(
                "ghost type escape: function `{def_path}` returns non-ghost type `{output}` \
                 derived from Ghost/Snapshot parameter(s). Ghost/Snapshot values cannot be \
                 extracted into program context. Use #[logic] or #[check(ghost)] for \
                 ghost-context functions."
            ),
        });
    }

    errors
}

/// Find all MIR locals whose type is `Ghost<T>`.
fn find_ghost_locals<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> HashSet<Local> {
    let mut ghost_locals = HashSet::new();
    for (local, decl) in body.local_decls.iter_enumerated() {
        if is_ghost_like_type(tcx, decl.ty) {
            ghost_locals.insert(local);
        }
    }
    ghost_locals
}

/// Find locals whose value is ghost-typed OR derived from a ghost local.
///
/// `ghost!` often lowers to a `Ghost<T>` local that is then deref'd or copied
/// into ordinary MIR locals before the eventual `SwitchInt`. Tracking only the
/// original ghost-typed local misses those derived discriminants.
fn find_ghost_dependent_locals<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> HashSet<Local> {
    let mut ghost_dependent_locals = find_ghost_locals(tcx, body);
    let mut changed = true;

    while changed {
        changed = false;

        for bb_data in body.basic_blocks.iter() {
            for stmt in &bb_data.statements {
                let StatementKind::Assign(box (place, rvalue)) = &stmt.kind else {
                    continue;
                };
                if rvalue_depends_on_ghost(rvalue, &ghost_dependent_locals) {
                    changed |= ghost_dependent_locals.insert(place.local);
                }
            }
            if let TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } = &bb_data.terminator().kind
            {
                let ghost_func = operand_depends_on_ghost(func, &ghost_dependent_locals);
                let ghost_arg_count = args
                    .iter()
                    .filter(|arg| operand_depends_on_ghost(&arg.node, &ghost_dependent_locals))
                    .count();

                // Guard: only propagate ghost dependency to the destination when
                // the destination type is itself Ghost-like. Without this check,
                // PermCell methods that accept a Ghost<&Perm<...>> permission token
                // and return a non-Ghost runtime value (e.g., `T` or `&T`) would
                // cause false positive ghost-dependency propagation. (#2316)
                let dest_is_ghost_typed =
                    is_ghost_like_type(tcx, body.local_decls[destination.local].ty);

                let all_args_ghost_derived = !args.is_empty() && ghost_arg_count == args.len();
                let erasure_marked_call = is_erasure_marked_call(tcx, func);

                if ghost_func
                    || is_ghost_deref_call(tcx, func) && ghost_arg_count > 0
                    || all_args_ghost_derived && (!erasure_marked_call || dest_is_ghost_typed)
                    || (args.len() == 1 && ghost_arg_count == 1 && dest_is_ghost_typed)
                {
                    changed |= ghost_dependent_locals.insert(destination.local);
                }
            }
        }
    }

    ghost_dependent_locals
}

/// Check whether a source span falls within any of the ghost block spans.
fn is_in_ghost_region(span: Span, ghost_spans: &[Span]) -> bool {
    ghost_spans.iter().any(|gs| gs.contains(span))
}

/// Walk MIR terminators to find SwitchInt branches that depend on ghost locals.
///
/// Only checks `SwitchInt` discriminants — general reads of Ghost<T> locals
/// are expected in verification MIR (the ghost! macro creates Ghost<T> locals
/// that are used by the outer let binding). The soundness concern is only
/// when runtime control flow depends on ghost values.
fn check_body_for_ghost_leaks(
    body: &Body<'_>,
    ghost_dependent_locals: &HashSet<Local>,
    ghost_spans: &[Span],
) -> Vec<GhostValidationError> {
    let mut errors = Vec::new();

    for (_bb, bb_data) in body.basic_blocks.iter_enumerated() {
        let terminator = bb_data.terminator();
        let term_span = terminator.source_info.span;

        // Terminators inside ghost regions are fine
        if is_in_ghost_region(term_span, ghost_spans) {
            continue;
        }

        // Only check SwitchInt — the one terminator where a ghost value
        // would cause runtime control flow to depend on ghost state
        if let TerminatorKind::SwitchInt { discr, .. } = &terminator.kind {
            if let Some(local) = operand_local(discr) {
                if ghost_dependent_locals.contains(&local) {
                    errors.push(GhostValidationError {
                        span: term_span,
                        message: format!(
                            "runtime control flow depends on ghost-derived local _{}: \
                             Ghost<T> values must not influence non-ghost branching",
                            local.as_u32()
                        ),
                    });
                }
            }
        }
    }

    errors
}

fn place_depends_on_ghost(
    place: rustc_middle::mir::Place<'_>,
    ghost_locals: &HashSet<Local>,
) -> bool {
    ghost_locals.contains(&place.local)
}

fn operand_depends_on_ghost(operand: &Operand<'_>, ghost_locals: &HashSet<Local>) -> bool {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => place_depends_on_ghost(*place, ghost_locals),
        // RuntimeChecks (UbChecks/ContractChecks/OverflowChecks) references no
        // place/local, so it can never depend on a ghost local — mirror Constant.
        Operand::Constant(_) | Operand::RuntimeChecks(_) => false,
    }
}

fn rvalue_depends_on_ghost(rvalue: &Rvalue<'_>, ghost_locals: &HashSet<Local>) -> bool {
    match rvalue {
        // A provenance retag is value-identity and cannot add or remove a
        // dependency on a ghost local.
        Rvalue::Use(op, _) | Rvalue::UnaryOp(_, op) | Rvalue::Cast(_, op, _) => {
            operand_depends_on_ghost(op, ghost_locals)
        }
        Rvalue::BinaryOp(_, box (lhs, rhs)) => {
            operand_depends_on_ghost(lhs, ghost_locals)
                || operand_depends_on_ghost(rhs, ghost_locals)
        }
        Rvalue::Ref(_, _, place)
        | Rvalue::Reborrow(_, _, place)
        | Rvalue::RawPtr(_, place)
        | Rvalue::Discriminant(place)
        | Rvalue::CopyForDeref(place) => place_depends_on_ghost(*place, ghost_locals),
        Rvalue::Aggregate(_, operands) => operands
            .iter()
            .any(|op| operand_depends_on_ghost(op, ghost_locals)),
        Rvalue::Repeat(op, _) | Rvalue::WrapUnsafeBinder(op, _) => {
            operand_depends_on_ghost(op, ghost_locals)
        }
        Rvalue::ThreadLocalRef(_) => false,
    }
}

/// Extract the local from an operand, if it references one.
fn operand_local(operand: &Operand<'_>) -> Option<Local> {
    match operand {
        Operand::Copy(place) | Operand::Move(place) => Some(place.local),
        // RuntimeChecks references no place/local — mirror Constant (no local).
        Operand::Constant(_) | Operand::RuntimeChecks(_) => None,
    }
}

fn is_ghost_deref_call(tcx: TyCtxt<'_>, func: &Operand<'_>) -> bool {
    let Some(def_id) = operand_fn_def_id(func) else {
        return false;
    };
    let path = tcx.def_path_str(def_id);
    path.ends_with("::deref")
}

fn is_erasure_marked_call(tcx: TyCtxt<'_>, func: &Operand<'_>) -> bool {
    let Some(def_id) = operand_fn_def_id(func) else {
        return false;
    };
    crate::attr_utils::has_erasure_marker(tcx.get_all_attrs(def_id))
}

fn operand_fn_def_id(func: &Operand<'_>) -> Option<DefId> {
    let Operand::Constant(box constant) = func else {
        return None;
    };
    let TyKind::FnDef(def_id, _) = constant.const_.ty().kind() else {
        return None;
    };
    Some(*def_id)
}

#[cfg(test)]
mod tests;
