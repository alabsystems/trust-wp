// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Ghost block detection and validation for the trust-wp driver.
//!
//! This module:
//! - Detects ghost blocks via `#[doc = "__trust_wp_ghost"]` marker
//! - Records ghost blocks for validation and SMT encoding
//! - Validates ghost blocks don't write to non-ghost variables
//! - Validates ghost blocks don't move non-ghost values
//!
//! # Ghost Block Detection
//!
//! The `ghost!` macro expands to (stable Rust, no cfg flags):
//! ```text
//! {
//!     #[doc(hidden)]
//!     #[doc = "__trust_wp_ghost"]
//!     #[allow(unreachable_code, unused_variables, dead_code)]
//!     let __trust_wp_ghost_value = if false {
//!         ::trust_wp_std::ghost::Ghost::new({ /* ghost block contents */ })
//!     } else {
//!         ::trust_wp_std::ghost::Ghost::conjure()
//!     };
//!     __trust_wp_ghost_value
//! }
//! ```
//!
//! The driver detects ghost blocks by finding `let` statements (StmtKind::Let)
//! with the `#[doc = "__trust_wp_ghost"]` marker attribute, then extracts the
//! then-branch of the `if false` expression for validation. The user's ghost
//! code lives inside the `Ghost::new(block)` call argument in the then-branch.
//!
//! Note: StmtKind::Let is for regular `let` statements, not ExprKind::Let
//! which is for `if let` expressions.

use std::collections::{HashMap, HashSet};

pub(crate) mod erasure;
mod move_validation;
pub(crate) mod program_context;
mod snapshot_self_reference;
pub(crate) mod source_assignments;
#[cfg(test)]
mod tests;
pub(crate) mod type_helpers;
mod write_validation;

use log::debug;
use rustc_hir::{
    def::Res,
    def_id::{DefId, LocalDefId},
    intravisit::{self, walk_expr, walk_stmt, Visitor},
    Expr, ExprKind, HirId, Pat, PatKind, QPath, Stmt, StmtKind, TyKind as HirTyKind, UnOp,
};
use rustc_middle::{
    hir::nested_filter,
    ty::{
        adjustment::{Adjust, DerefAdjustKind},
        TyCtxt, TyKind, TypeckResults,
    },
};
use rustc_span::Span;

use self::{
    move_validation::{validate_ghost_block_loops, validate_ghost_block_moves},
    snapshot_self_reference::check_snapshot_self_references,
    write_validation::validate_ghost_block_writes,
};

/// Information about a detected ghost block.
#[derive(Debug, Clone)]
pub(crate) struct GhostBlock {
    /// The HirId of the block expression
    pub(crate) hir_id: HirId,
    /// Span of the ghost block for error reporting
    pub(crate) span: Span,
    /// The containing function's LocalDefId
    pub(crate) containing_fn: LocalDefId,
}

/// Validation error for ghost blocks.
#[derive(Debug)]
pub(crate) struct GhostValidationError {
    /// Span of the error location
    pub(crate) span: Span,
    /// Human-readable error message
    pub(crate) message: String,
}

/// Find all ghost blocks in the crate.
///
/// Returns a vector of `GhostBlock` for each ghost block (marked with
/// `#[doc = "__trust_wp_ghost"]`) found in the HIR.
pub(crate) fn find_ghost_blocks(tcx: TyCtxt<'_>) -> Vec<GhostBlock> {
    let mut finder = GhostBlockFinder {
        tcx,
        ghost_blocks: Vec::new(),
        current_fn: None,
    };

    // Iterate over all body owners (functions, closures, etc.)
    for local_def_id in tcx.hir_body_owners() {
        // Specification type-check closures are neither program code nor
        // specifications the verifier reads (see `spec_typecheck`).
        if crate::callbacks::spec_typecheck::is_spec_tc_body(tcx, local_def_id) {
            continue;
        }
        finder.current_fn = Some(local_def_id);
        let body = tcx.hir_body_owned_by(local_def_id);
        finder.visit_body(body);
    }

    finder.ghost_blocks
}

/// HIR visitor for finding ghost blocks.
struct GhostBlockFinder<'tcx> {
    tcx: TyCtxt<'tcx>,
    ghost_blocks: Vec<GhostBlock>,
    current_fn: Option<LocalDefId>,
}

impl<'tcx> Visitor<'tcx> for GhostBlockFinder<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;
    type MaybeTyCtxt = TyCtxt<'tcx>;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_stmt(&mut self, stmt: &'tcx Stmt<'tcx>) {
        // The ghost! macro expands to one of two patterns depending on cfg:
        //
        // Under `#[cfg(trust_wp)]` (#873):
        //   #[doc = "__trust_wp_ghost"]
        //   let __trust_wp_ghost_value = Ghost::new({ user_code });
        //
        // Under `#[cfg(not(trust_wp))]`:
        //   #[doc = "__trust_wp_ghost"]
        //   let __trust_wp_ghost_value = if false {
        //       Ghost::new({ user_code })
        //   } else {
        //       Ghost::conjure()
        //   };
        //
        // We detect the let statement (StmtKind::Let) with the ghost marker
        // attribute and extract the ghost block from whichever pattern is active.
        if let StmtKind::Let(let_stmt) = stmt.kind {
            if has_ghost_marker(self.tcx, let_stmt.hir_id) {
                if let Some(init) = let_stmt.init {
                    let ghost_expr = match init.kind {
                        // cfg(not(trust_wp)) pattern: if false { Ghost::new(block) } else { ... }
                        ExprKind::If(_cond, then_expr, _else_expr) => Some(then_expr),
                        // cfg(trust_wp) pattern: Ghost::new(block) — the init IS the ghost expr
                        ExprKind::Call(..) => Some(init),
                        _ => None,
                    };

                    if let Some(ghost_expr) = ghost_expr {
                        if let Some(containing_fn) = self.current_fn {
                            debug!(
                                "Found ghost block in {:?}",
                                self.tcx.def_path_str(containing_fn)
                            );
                            self.ghost_blocks.push(GhostBlock {
                                hir_id: ghost_expr.hir_id,
                                span: ghost_expr.span,
                                containing_fn,
                            });
                        }
                    }
                }
            }
        }
        walk_stmt(self, stmt);
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        intravisit::walk_expr(self, expr);
    }
}

/// Check if a HIR node has the `#[doc = "__trust_wp_ghost"]` marker, every
/// copy of it written by the `ghost!`/`ghost_let!` expansion.
///
/// The expansion keeps the marked block under `cfg(trust_wp)` and behind
/// `if false` otherwise, so it never runs. The same marker written in user
/// source, or pasted through a user macro, marks an ordinary `let` whose
/// initializer runs in every build (ghost_marker_written_by_hand_runs_ghost_deref),
/// so one such copy disqualifies the block.
fn has_ghost_marker(tcx: TyCtxt<'_>, hir_id: HirId) -> bool {
    // `doc_marker_str` (doc_str + value_str fallback): the Trust toolchain
    // parses `#[doc=…]` into Attribute::Parsed(DocComment), for which
    // value_str() returns None.
    let mut markers = tcx
        .hir_attrs(hir_id)
        .iter()
        .filter(|attr| {
            crate::attr_utils::doc_marker_str(attr)
                .is_some_and(|value| value.as_str() == "__trust_wp_ghost")
        })
        .peekable();
    markers.peek().is_some()
        && markers
            .all(|attr| crate::callbacks::spec_typecheck::marker_is_from_trust_wp_macros(tcx, attr))
}

/// Validate ghost blocks according to the design rules.
///
/// # Validation Rules
///
/// 1. **No Control Flow Escape:**
///    - `return` in ghost block -> Error
///    - `break` to label outside ghost block -> Error
///    - `continue` to label outside ghost block -> Error
///
///    Note: This is already validated by the proc macro.
///
/// 2. **No Program Mutation:**
///    - Write to program variable -> Error
///    - Write to `Ghost<T>` variable -> OK
///    - Read from program variable -> OK
///
/// 3. **No Move of Non-Ghost:**
///    - Move program value into ghost -> Error
///    - Move `Ghost<T>` value -> OK
///    - Copy program value -> OK
///
/// This implementation uses HIR-level analysis with type checking to detect:
/// - Assignment expressions (write validation)
/// - Non-Copy type consumption (move validation)
pub(crate) fn validate_ghost_blocks(
    tcx: TyCtxt<'_>,
    ghost_blocks: &[GhostBlock],
) -> Vec<GhostValidationError> {
    let mut all_errors = Vec::new();

    for ghost_block in ghost_blocks {
        debug!(
            "Validating ghost block at {:?} in function {:?}",
            ghost_block.span, ghost_block.containing_fn
        );

        // Get the expression for this ghost block
        let expr = tcx.hir_node(ghost_block.hir_id).expect_expr();

        // Validate: detect writes to non-local variables
        let write_errors = validate_ghost_block_writes(tcx, ghost_block, expr);
        all_errors.extend(write_errors);

        // Validate: detect moves of non-ghost values
        let move_errors = validate_ghost_block_moves(tcx, ghost_block, expr);
        all_errors.extend(move_errors);

        // Validate: detect clearly non-terminating loops in ghost blocks
        let loop_errors = validate_ghost_block_loops(ghost_block, expr);
        all_errors.extend(loop_errors);

        let call_errors = validate_ghost_block_calls(tcx, ghost_block, expr);
        all_errors.extend(call_errors);
    }

    all_errors
}

fn validate_ghost_block_calls<'tcx>(
    tcx: TyCtxt<'tcx>,
    ghost_block: &GhostBlock,
    expr: &'tcx Expr<'tcx>,
) -> Vec<GhostValidationError> {
    let owner_body = tcx.hir_body_owned_by(ghost_block.containing_fn);
    let typeck_results = tcx.typeck_body(owner_body.id());
    let mut validator = GhostBlockCallValidator {
        tcx,
        typeck_results,
        errors: Vec::new(),
    };
    validator.visit_expr(expr);
    validator.errors
}

struct GhostBlockCallValidator<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck_results: &'a TypeckResults<'tcx>,
    errors: Vec<GhostValidationError>,
}

impl<'tcx> Visitor<'tcx> for GhostBlockCallValidator<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;
    type MaybeTyCtxt = TyCtxt<'tcx>;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if crate::callbacks::spec_typecheck::is_spec_tc_closure_expr(self.tcx, expr) {
            return;
        }
        let def_id = match expr.kind {
            ExprKind::Call(callee, _) => self.call_def_id(callee),
            ExprKind::MethodCall(..) => self.typeck_results.type_dependent_def_id(expr.hir_id),
            _ => None,
        };

        if let Some(def_id) = def_id {
            self.check_call(expr.span, def_id);
        }

        walk_expr(self, expr);
    }
}

impl GhostBlockCallValidator<'_, '_> {
    fn call_def_id(&self, callee: &Expr<'_>) -> Option<DefId> {
        if let TyKind::FnDef(def_id, _) = self.typeck_results.expr_ty(callee).kind() {
            return Some(*def_id);
        }

        if let ExprKind::Path(qpath) = &callee.kind {
            if let Res::Def(_, def_id) = self.typeck_results.qpath_res(qpath, callee.hir_id) {
                return Some(def_id);
            }
        }

        None
    }

    fn check_call(&mut self, span: Span, def_id: DefId) {
        let Some(local_def_id) = def_id.as_local() else {
            return;
        };
        let hir_id = self.tcx.local_def_id_to_hir_id(local_def_id);
        let attrs = self.tcx.hir_attrs(hir_id);
        if crate::attr_utils::has_check_mode(attrs, "ghost")
            || crate::logic::has_logic_marker(attrs)
            || !crate::attr_utils::has_check_mode(attrs, "terminates")
        {
            return;
        }

        self.errors.push(GhostValidationError {
            span,
            message: format!(
                "called non-ghost function `{}` in ghost context",
                self.tcx.def_path_str(def_id)
            ),
        });
    }
}

/// Reject ghost-only API operations from ordinary program context.
///
/// `ghost!` lowers to `Ghost::new(...)`, so direct signature/type checks are
/// not enough: calls are allowed when their HIR span sits inside a detected
/// ghost block, but direct `Ghost::new`, deref, or extraction in runtime code is
/// not erased and must fail closed.
pub(crate) fn validate_program_context_ghost_apis(
    tcx: TyCtxt<'_>,
    ghost_blocks: &[GhostBlock],
) -> Vec<GhostValidationError> {
    let local_crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE).to_string();
    if matches!(
        local_crate_name.as_str(),
        "trust_wp_std" | "trust-wp" | "creusot_std" | "creusot_contracts" | "trust_wp_lib"
    ) {
        return Vec::new();
    }

    let mut all_errors = Vec::new();

    for local_def_id in tcx.hir_body_owners() {
        // Specification type-check closures are neither program code nor
        // specifications the verifier reads (see `spec_typecheck`).
        if crate::callbacks::spec_typecheck::is_spec_tc_body(tcx, local_def_id) {
            continue;
        }
        let hir_id = tcx.local_def_id_to_hir_id(local_def_id);
        let attrs = tcx.hir_attrs(hir_id);
        let body = tcx.hir_body_owned_by(local_def_id);
        let typeck_results = tcx.typeck_body(body.id());
        let is_logic = crate::logic::has_logic_marker(attrs);
        let validate_program_context_apis =
            !is_logic && !crate::attr_utils::has_check_mode(attrs, "ghost");
        // A `#[check(ghost)]` body runs as program code when a program calls
        // it, so a ghost it dereferences, extracts or compares outside
        // `ghost!` is refused there too; only creating one is left to it.
        let validate_ghost_value_uses = !is_logic;
        // `#[erasure(target)]` functions are the ghost-bearing implementation
        // side of an erasure pair. They legitimately take a resource and a
        // permission as function inputs and pass them straight to the
        // `Perm::as_ref` / `PermCell::borrow` family — the permission
        // identity is established by the caller (or the erased target),
        // not by local construction. Skip the same-origin heuristic here.
        // See `reference/creusot/tests/should_succeed/specification/erasure.rs`.
        let is_erasure = crate::attr_utils::has_erasure_marker(attrs);
        // Collect ghost spans across every body owner, not only the
        // current one. A `ghost!` block can lexically contain nested
        // body owners (e.g. closures passed to `inv.open(|inv| ...)`
        // inside `ghost! { |c| { inv.open(tokens.into_inner(), ...) } }`).
        // Filtering by `containing_fn` would miss such cases and flag
        // legitimate Creusot ghost-bridge calls.
        let ghost_spans = ghost_blocks
            .iter()
            .map(|block| block.span)
            .collect::<Vec<_>>();

        let mut validator = ProgramContextGhostApiValidator {
            tcx,
            typeck_results,
            ghost_spans,
            resource_origins: HashMap::new(),
            permission_origins: HashMap::new(),
            resource_params: body
                .params
                .iter()
                .filter_map(|param| binding_hir_id(param.pat))
                .collect(),
            next_permission_origin: 0,
            validate_program_context_apis,
            validate_ghost_value_uses,
            check_permission_identity: !is_erasure,
            snapshot_capture_depth: usize::from(closure_is_inside_snapshot_capture(
                tcx,
                typeck_results,
                local_def_id,
            )),
            typing_env: rustc_middle::ty::TypingEnv::post_analysis(tcx, local_def_id),
            errors: Vec::new(),
        };
        validator.visit_body(body);
        all_errors.extend(validator.errors);
    }

    all_errors
}

/// Whether the closure `def_id` is written inside a snapshot capture, whose
/// argument never runs: `snapshot!` keeps the capture under `cfg(trust_wp)`
/// and behind `if false` otherwise. The enclosing body's walk visits the
/// closure at a raised `snapshot_capture_depth`, but the body-owner loop
/// visits it again as a body of its own, where the depth would start at zero
/// (should_succeed `such_that.rs`: `snapshot!(|x: Int| mapping[x] + 1 == 0)`).
///
/// Only a capture trust-wp's `snapshot!` expansion wrote is one that never
/// runs: the same shape written by hand, or by a user's macro, runs in every
/// build, so a closure inside it is validated as program code
/// (snapshot_capture_call_closure_ghost_deref_in_program_context_panics,
/// snapshot_capture_in_user_macro_runs_ghost_deref).
fn closure_is_inside_snapshot_capture(
    tcx: TyCtxt<'_>,
    typeck_results: &TypeckResults<'_>,
    def_id: LocalDefId,
) -> bool {
    if tcx.def_kind(def_id) != rustc_hir::def::DefKind::Closure {
        return false;
    }
    for (_, node) in tcx.hir_parent_iter(tcx.local_def_id_to_hir_id(def_id)) {
        match node {
            rustc_hir::Node::Expr(expr) => match expr.kind {
                ExprKind::Call(callee, _)
                    if program_context::is_macro_snapshot_capture_call(
                        tcx,
                        typeck_results,
                        callee,
                    ) =>
                {
                    return true;
                }
                ExprKind::Block(block, _)
                    if program_context::is_macro_snapshot_block(tcx, typeck_results, block) =>
                {
                    return true;
                }
                _ => {}
            },
            // The closure's own item: nothing above it is its body.
            rustc_hir::Node::Item(_)
            | rustc_hir::Node::ImplItem(_)
            | rustc_hir::Node::TraitItem(_) => return false,
            _ => {}
        }
    }
    false
}

/// Validate `Tokens::new` creation sites.
///
/// Creusot treats namespace tokens as a unique entry-point capability:
/// `Tokens::new()` is allowed only once, directly in the crate entry `main`,
/// and not from a loop.
pub(crate) fn validate_tokens_new(tcx: TyCtxt<'_>) -> Vec<GhostValidationError> {
    let local_crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE).to_string();
    if matches!(
        local_crate_name.as_str(),
        "trust_wp_std" | "trust-wp" | "creusot_std" | "creusot_contracts" | "trust_wp_lib"
    ) {
        return Vec::new();
    }

    let mut all_errors = Vec::new();
    let mut sites = Vec::new();

    for local_def_id in tcx.hir_body_owners() {
        // Specification type-check closures are neither program code nor
        // specifications the verifier reads (see `spec_typecheck`).
        if crate::callbacks::spec_typecheck::is_spec_tc_body(tcx, local_def_id) {
            continue;
        }
        let body = tcx.hir_body_owned_by(local_def_id);
        let typeck_results = tcx.typeck_body(body.id());
        let mut validator = TokensNewValidator {
            tcx,
            typeck_results,
            containing_fn: local_def_id,
            loop_depth: 0,
            sites: &mut sites,
            errors: Vec::new(),
        };
        validator.visit_body(body);
        all_errors.extend(validator.errors);
    }

    if sites.len() > 1 {
        for span in sites.iter().skip(1) {
            all_errors.push(GhostValidationError {
                span: *span,
                message: "Tokens::new may be called at most once".to_string(),
            });
        }
    }

    all_errors
}

struct TokensNewValidator<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck_results: &'a TypeckResults<'tcx>,
    containing_fn: LocalDefId,
    loop_depth: usize,
    sites: &'a mut Vec<Span>,
    errors: Vec<GhostValidationError>,
}

impl<'tcx> Visitor<'tcx> for TokensNewValidator<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;
    type MaybeTyCtxt = TyCtxt<'tcx>;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if crate::callbacks::spec_typecheck::is_spec_tc_closure_expr(self.tcx, expr) {
            return;
        }
        if let ExprKind::Loop(..) = expr.kind {
            self.loop_depth += 1;
            walk_expr(self, expr);
            self.loop_depth -= 1;
            return;
        }

        let is_tokens_new = match expr.kind {
            ExprKind::Call(callee, _) => {
                self.call_def_id(callee)
                    .is_some_and(|def_id| is_tokens_new_call(self.tcx, def_id))
                    || callee_path_is_tokens_new(callee)
            }
            ExprKind::MethodCall(..) => self
                .typeck_results
                .type_dependent_def_id(expr.hir_id)
                .is_some_and(|def_id| is_tokens_new_call(self.tcx, def_id)),
            _ => false,
        };

        if is_tokens_new {
            self.sites.push(expr.span);
            if !self.is_entry_main() {
                self.errors.push(GhostValidationError {
                    span: expr.span,
                    message: "Tokens::new may only be called in the entry main function"
                        .to_string(),
                });
            }
            if self.loop_depth > 0 {
                self.errors.push(GhostValidationError {
                    span: expr.span,
                    message: "Tokens::new may not be called inside a loop".to_string(),
                });
            }
        }

        walk_expr(self, expr);
    }
}

impl TokensNewValidator<'_, '_> {
    fn call_def_id(&self, callee: &Expr<'_>) -> Option<DefId> {
        if let TyKind::FnDef(def_id, _) = self.typeck_results.expr_ty(callee).kind() {
            return Some(*def_id);
        }

        if let ExprKind::Path(qpath) = &callee.kind {
            if let Res::Def(_, def_id) = self.typeck_results.qpath_res(qpath, callee.hir_id) {
                return Some(def_id);
            }
        }

        None
    }

    fn is_entry_main(&self) -> bool {
        self.tcx.def_path_str(self.containing_fn) == "main"
    }
}

struct ProgramContextGhostApiValidator<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck_results: &'a TypeckResults<'tcx>,
    ghost_spans: Vec<Span>,
    resource_origins: HashMap<HirId, PermissionOrigin>,
    permission_origins: HashMap<HirId, PermissionOrigin>,
    resource_params: HashSet<HirId>,
    next_permission_origin: usize,
    validate_program_context_apis: bool,
    /// Whether a ghost value read outside `ghost!` runs: `true` for every
    /// body but a logic function's, `#[check(ghost)]` ones included.
    validate_ghost_value_uses: bool,
    /// `false` for `#[erasure(...)]` functions, which are the ghost-bearing
    /// implementation half of an erasure pair and legitimately receive both
    /// resource and permission as function inputs without a local same-origin
    /// witness. See `validate_program_context_ghost_apis` for context.
    check_permission_identity: bool,
    snapshot_capture_depth: usize,
    /// The body's typing environment, in which a call is resolved to the impl
    /// it runs (`program_context::divergent_run_time_operation`).
    typing_env: rustc_middle::ty::TypingEnv<'tcx>,
    errors: Vec<GhostValidationError>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct PermissionOrigin(usize);

const MIXED_PERMISSION_ORIGIN: PermissionOrigin = PermissionOrigin(usize::MAX);

const IMPLICIT_GHOST_DEREF_MESSAGE: &str = "trust-wp: a ghost value is dereferenced outside \
     ghost!(...) by a `Deref` the compiler inserts (a coercion, a field read or a method call \
     through a `Ghost` or `Snapshot`); it panics at run time. Move the use into ghost!(...)";

/// A trait use on a ghost operand whose run-time body differs from its
/// logical reading (`ProgramContextGhostApiValidator::ghost_operand_trait_use`).
enum GhostTraitUse {
    Comparison,
    Borrow,
}

const GHOST_BORROW_TRAIT_MESSAGE: &str = "trust-wp: cannot extract a ghost value in program \
     context: `Borrow`/`BorrowMut` of a `Ghost` panics at run time; use ghost!(...) for \
     ghost-only computation";

const GHOST_COMPARISON_MESSAGE: &str = "trust-wp: ghost values are compared outside \
     ghost!(...); `==` on a `Ghost` or `Snapshot` is `true` at run time whatever the values. \
     Compare them in ghost!(...) or a proof_assert!";

const GHOST_HOLDER_COMPARISON_MESSAGE: &str = "trust-wp: a value holding a `Ghost` or \
     `Snapshot` is compared or hashed outside ghost!(...); the ghost's run-time `eq` is `true` \
     and its `hash` a constant whatever the values. Compare them in ghost!(...) or a \
     proof_assert!";

impl<'tcx> Visitor<'tcx> for ProgramContextGhostApiValidator<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;
    type MaybeTyCtxt = TyCtxt<'tcx>;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    /// An anonymous constant (an array length, a const generic argument) is
    /// typechecked apart from the body that spells it, so this body's
    /// `typeck_results` hold no type for its nodes and reading one is an ICE
    /// (`[T; 2]` in should_succeed `lang/size_of.rs`). It is a body owner of
    /// its own, and `validate_program_context_ghost_apis` visits it with its
    /// own results, so nothing it holds goes unvalidated.
    fn visit_anon_const(&mut self, _: &'tcx rustc_hir::AnonConst) {}

    fn visit_stmt(&mut self, stmt: &'tcx Stmt<'tcx>) {
        if let StmtKind::Let(let_stmt) = stmt.kind {
            if let Some(init) = let_stmt.init {
                if self.is_permission_constructor(init) {
                    if let Some((resource, permission)) = binding_pair_slots(let_stmt.pat) {
                        let origin = self.allocate_permission_origin();
                        if let Some(resource) = resource {
                            self.resource_origins.insert(resource, origin);
                        }
                        if let Some(permission) = permission {
                            self.permission_origins.insert(permission, origin);
                        }
                    } else if let Some(binding) = binding_hir_id(let_stmt.pat) {
                        let origin = self.allocate_permission_origin();
                        self.resource_origins.insert(binding, origin);
                        self.permission_origins.insert(binding, origin);
                    }
                } else if self.propagate_tuple_binding_origins(let_stmt.pat, init) {
                } else if let Some(binding) = binding_hir_id(let_stmt.pat) {
                    if let Some(origin) = self.permission_origin_from_expr(init) {
                        self.permission_origins.insert(binding, origin);
                    }
                    if let Some(origin) = self.resource_origin_from_expr(init) {
                        self.resource_origins.insert(binding, origin);
                    }
                    if self
                        .local_expr_hir_id(init)
                        .is_some_and(|local| self.resource_params.contains(&local))
                    {
                        self.resource_params.insert(binding);
                    }
                }
            }
        }

        walk_stmt(self, stmt);
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if crate::callbacks::spec_typecheck::is_spec_tc_closure_expr(self.tcx, expr) {
            return;
        }
        if self.is_in_ghost_context(expr.span) {
            return;
        }

        // The statement-form `snapshot! { stmt; }` lowers to a block ending in
        // `Snapshot::<()>::new_phantom()` whose statements sit under
        // `cfg(trust_wp)`, and the dispatch form to a block ending in
        // `snapshot_capture_select(..).capture()`: neither runs, so the
        // block is a capture like a `Snapshot::capture(..)` argument. Only
        // the blocks the expansion wrote (`program_context`).
        if let ExprKind::Block(block, _) = expr.kind {
            if program_context::is_macro_snapshot_block(self.tcx, self.typeck_results, block) {
                self.snapshot_capture_depth += 1;
                intravisit::walk_expr(self, expr);
                self.snapshot_capture_depth -= 1;
                return;
            }
        }

        if self.validate_ghost_value_uses && self.snapshot_capture_depth == 0 {
            if self.has_implicit_ghost_deref(expr) {
                self.errors.push(GhostValidationError {
                    span: expr.span,
                    message: IMPLICIT_GHOST_DEREF_MESSAGE.to_string(),
                });
            }
            match self.ghost_operand_trait_use(expr) {
                Some(GhostTraitUse::Comparison) => self.errors.push(GhostValidationError {
                    span: expr.span,
                    message: GHOST_COMPARISON_MESSAGE.to_string(),
                }),
                Some(GhostTraitUse::Borrow) => self.errors.push(GhostValidationError {
                    span: expr.span,
                    message: GHOST_BORROW_TRAIT_MESSAGE.to_string(),
                }),
                None if self.asks_ghost_holder_for_comparison_or_hash(expr) => {
                    self.errors.push(GhostValidationError {
                        span: expr.span,
                        message: GHOST_HOLDER_COMPARISON_MESSAGE.to_string(),
                    });
                }
                None => {}
            }
            match program_context::divergent_run_time_operation(
                self.tcx,
                self.typing_env,
                self.typeck_results,
                expr,
            )
            .or_else(|| {
                program_context::divergent_unsize_coercion(
                    self.tcx,
                    self.typing_env,
                    self.typeck_results,
                    expr,
                )
            }) {
                Some(program_context::Divergence::Operation(operation)) => {
                    self.errors.push(GhostValidationError {
                        span: expr.span,
                        message: format!(
                            "trust-wp: `{operation}` runs outside ghost!(...) and snapshot!(...), \
                             where its run-time body is not the logical operation the verifier \
                             reads; move it into ghost!(...), snapshot!(...) or a specification"
                        ),
                    });
                }
                Some(program_context::Divergence::Unread(trait_ref)) => {
                    self.errors.push(GhostValidationError {
                        span: expr.span,
                        message: format!(
                            "trust-wp: cannot read which impl this call's bound `{trait_ref}` \
                             runs, so whether it runs a ghost or logic body outside ghost!(...) \
                             is unknown; refusing"
                        ),
                    });
                }
                None => {}
            }
        }

        match expr.kind {
            ExprKind::Call(callee, args) if self.is_snapshot_capture_callee(callee) => {
                self.visit_expr(callee);
                self.snapshot_capture_depth += 1;
                for arg in args {
                    self.visit_expr(arg);
                }
                self.snapshot_capture_depth -= 1;
                return;
            }
            ExprKind::Call(callee, args) if self.is_perm_access_callee(callee) => {
                if let [resource, permission, ..] = args {
                    self.check_permission_identity(expr.span, resource, permission);
                }
            }
            ExprKind::Call(callee, args) => {
                if self.validate_program_context_apis && self.is_ghost_new_callee(callee) {
                    self.errors.push(GhostValidationError {
                        span: expr.span,
                        message: "trust-wp: cannot create a ghost variable in program context; \
                                  wrap this expression in ghost!(...)"
                            .to_string(),
                    });
                }

                if self.validate_ghost_value_uses && self.snapshot_capture_depth == 0 {
                    if self.is_ghost_extraction_callee(callee) {
                        self.errors.push(GhostValidationError {
                            span: expr.span,
                            message: "trust-wp: cannot extract a ghost value in program context; \
                                      use ghost!(...) for ghost-only computation"
                                .to_string(),
                        });
                    }

                    if self.is_ghost_deref_callee(callee, args) {
                        self.errors.push(GhostValidationError {
                            span: expr.span,
                            message:
                                "trust-wp: cannot dereference a ghost value in program context; \
                                      use ghost!(...) for ghost-only computation"
                                    .to_string(),
                        });
                    }
                }
            }
            ExprKind::MethodCall(path, receiver, _, _) => {
                if self.is_permcell_access_method(receiver, path.ident.as_str()) {
                    if let ExprKind::MethodCall(_, _, args, _) = expr.kind {
                        if let Some(permission) = args.first() {
                            self.check_permission_identity(expr.span, receiver, permission);
                        }
                    }
                }

                if self.validate_ghost_value_uses
                    && self.snapshot_capture_depth == 0
                    && self.is_ghost_extraction_method(expr, path.ident.as_str())
                    && type_helpers::is_ghost_like_type(
                        self.tcx,
                        self.typeck_results.expr_ty(receiver),
                    )
                {
                    self.errors.push(GhostValidationError {
                        span: expr.span,
                        message: "trust-wp: cannot extract a ghost value in program context; \
                                  use ghost!(...) for ghost-only computation"
                            .to_string(),
                    });
                }

                if self.validate_ghost_value_uses
                    && self.snapshot_capture_depth == 0
                    && self.is_ghost_deref_method(expr, receiver, path.ident.as_str())
                {
                    self.errors.push(GhostValidationError {
                        span: expr.span,
                        message: "trust-wp: cannot dereference a ghost value in program context; \
                                  use ghost!(...) for ghost-only computation"
                            .to_string(),
                    });
                }
            }
            ExprKind::Unary(UnOp::Deref, inner)
                if self.validate_ghost_value_uses
                    && self.snapshot_capture_depth == 0
                    // Only the ghost `Deref` (`*snap` extracting the logical
                    // inner value of a bare `Snapshot`/`Ghost`) is forbidden in
                    // program context. A builtin reference deref of a
                    // `&mut Snapshot` / `&Snapshot` (`*xm`, the LHS `*evil`) is
                    // just a place projection — Creusot compiles it and proves
                    // the program — so do NOT reject it. (bug/869)
                    && !self.typeck_results.expr_ty(inner).is_ref()
                    && type_helpers::is_ghost_like_type(
                        self.tcx,
                        self.typeck_results.expr_ty(inner),
                    ) =>
            {
                self.errors.push(GhostValidationError {
                    span: expr.span,
                    message: "trust-wp: cannot dereference a ghost value in program context; \
                              use ghost!(...) for ghost-only computation"
                        .to_string(),
                });
            }
            _ => {}
        }

        walk_expr(self, expr);
    }
}

impl<'a, 'tcx> ProgramContextGhostApiValidator<'a, 'tcx> {
    fn is_in_ghost_context(&self, span: Span) -> bool {
        self.ghost_spans
            .iter()
            .any(|ghost_span| ghost_span.contains(span))
    }

    fn call_def_id(&self, callee: &Expr<'_>) -> Option<DefId> {
        if let TyKind::FnDef(def_id, _) = self.typeck_results.expr_ty(callee).kind() {
            return Some(*def_id);
        }

        if let ExprKind::Path(qpath) = &callee.kind {
            if let Res::Def(_, def_id) = self.typeck_results.qpath_res(qpath, callee.hir_id) {
                return Some(def_id);
            }
        }

        None
    }

    fn is_ghost_new_callee(&self, callee: &Expr<'_>) -> bool {
        self.call_def_id(callee)
            .is_some_and(|def_id| is_ghost_new_call(self.tcx, def_id))
            || callee_path_is_ghost_method(callee, "new")
    }

    fn is_ghost_extraction_callee(&self, callee: &Expr<'_>) -> bool {
        self.call_def_id(callee)
            .is_some_and(|def_id| is_ghost_extraction_method(self.tcx, def_id))
            || callee_path_is_any_ghost_method(callee, &["into_inner", "inner", "inner_mut"])
    }

    fn is_ghost_deref_callee(&self, callee: &Expr<'_>, args: &'tcx [Expr<'tcx>]) -> bool {
        let Some(receiver) = args.first() else {
            return false;
        };
        if !type_helpers::is_ghost_like_type(self.tcx, self.typeck_results.expr_ty(receiver)) {
            return false;
        }

        self.call_def_id(callee).is_some_and(|def_id| {
            is_ghost_api_call(self.tcx, def_id, &["deref", "deref_mut"])
                || is_deref_trait_call(self.tcx, def_id)
        }) || callee_path_is_deref_trait_method(callee)
    }

    fn is_permission_constructor(&self, expr: &Expr<'_>) -> bool {
        let ExprKind::Call(callee, _) = expr.kind else {
            return false;
        };

        if let Some(def_id) = self.call_def_id(callee) {
            return is_permcell_new_call(self.tcx, def_id) || is_perm_new_call(self.tcx, def_id);
        }

        callee_path_is_owner_method(callee, &["PermCell", "Perm"], "new")
    }

    fn is_perm_access_callee(&self, callee: &Expr<'_>) -> bool {
        if let Some(def_id) = self.call_def_id(callee) {
            return is_perm_access_call(self.tcx, def_id);
        }

        callee_path_is_owner_method(callee, &["Perm"], "as_ref")
            || callee_path_is_owner_method(callee, &["Perm"], "as_mut")
    }

    fn is_permcell_access_method(&self, receiver: &Expr<'_>, method_name: &str) -> bool {
        matches!(
            method_name,
            "borrow" | "borrow_mut" | "get" | "set" | "replace" | "take" | "into_inner"
        ) && is_permcell_like_type(self.tcx, self.typeck_results.expr_ty(receiver))
    }

    fn is_snapshot_capture_callee(&self, callee: &Expr<'_>) -> bool {
        program_context::is_macro_snapshot_capture_call(self.tcx, self.typeck_results, callee)
    }

    fn is_ghost_extraction_method(&self, expr: &Expr<'_>, method_name: &str) -> bool {
        matches!(method_name, "into_inner" | "inner" | "inner_mut")
            || self
                .typeck_results
                .type_dependent_def_id(expr.hir_id)
                .is_some_and(|def_id| is_ghost_extraction_method(self.tcx, def_id))
    }

    fn is_ghost_deref_method(
        &self,
        expr: &Expr<'_>,
        receiver: &'tcx Expr<'tcx>,
        method_name: &str,
    ) -> bool {
        if !matches!(method_name, "deref" | "deref_mut")
            || !type_helpers::is_ghost_like_type(self.tcx, self.typeck_results.expr_ty(receiver))
        {
            return false;
        }

        self.typeck_results
            .type_dependent_def_id(expr.hir_id)
            .is_none_or(|def_id| {
                is_ghost_api_call(self.tcx, def_id, &["deref", "deref_mut"])
                    || is_deref_trait_call(self.tcx, def_id)
            })
    }

    /// Whether rustc derefs a `Ghost` or `Snapshot` in `expr` by an adjustment
    /// of its own: a deref coercion, a field read or a method call through the
    /// ghost. Each is a run-time `Deref::deref` of the ghost, which panics.
    fn has_implicit_ghost_deref(&self, expr: &Expr<'tcx>) -> bool {
        let mut ty = self.typeck_results.expr_ty(expr);
        for adjustment in self.typeck_results.expr_adjustments(expr) {
            if matches!(
                adjustment.kind,
                Adjust::Deref(DerefAdjustKind::Overloaded(_))
            ) && type_helpers::is_ghost_like_type(self.tcx, ty)
            {
                return true;
            }
            ty = adjustment.target;
        }
        false
    }

    /// A trait method `expr` calls on a `Ghost` or `Snapshot` operand, as an
    /// operator, a method call or a path call, whose run-time body in
    /// trust-wp-std is not the logical operation the verifier reads:
    /// `PartialEq`/`PartialOrd` return `true` whatever the values, since
    /// neither carries one, and `Borrow`/`BorrowMut` of a `Ghost<Box<T>>`
    /// panic.
    fn ghost_operand_trait_use(&self, expr: &Expr<'tcx>) -> Option<GhostTraitUse> {
        let (def_id, operand) = match expr.kind {
            ExprKind::Binary(op, lhs, _) => {
                use rustc_hir::BinOpKind::{Eq, Ge, Gt, Le, Lt, Ne};
                if !matches!(op.node, Eq | Ne | Lt | Le | Gt | Ge) {
                    return None;
                }
                (self.typeck_results.type_dependent_def_id(expr.hir_id), lhs)
            }
            ExprKind::MethodCall(_, receiver, _, _) => (
                self.typeck_results.type_dependent_def_id(expr.hir_id),
                receiver,
            ),
            ExprKind::Call(callee, [first, ..]) => (self.call_def_id(callee), first),
            _ => return None,
        };
        let trait_id = self.tcx.trait_of_assoc(def_id?)?;
        if !type_helpers::is_ghost_like_type(self.tcx, self.typeck_results.expr_ty(operand)) {
            return None;
        }
        let lang_items = self.tcx.lang_items();
        let diagnostic = |name: &str| {
            self.tcx
                .get_diagnostic_item(rustc_span::Symbol::intern(name))
                == Some(trait_id)
        };
        if Some(trait_id) == lang_items.eq_trait()
            || Some(trait_id) == lang_items.partial_ord_trait()
        {
            Some(GhostTraitUse::Comparison)
        } else if diagnostic("Borrow") || diagnostic("BorrowMut") {
            Some(GhostTraitUse::Borrow)
        } else {
            None
        }
    }

    /// Whether `expr` calls a function, method or operator whose bounds, as
    /// the call instantiates them, ask a type holding a `Ghost` or `Snapshot`
    /// for `PartialEq`, `PartialOrd`, `Eq`, `Ord` or `Hash`:
    /// `Option<Ghost<T>> == ..`, `v.contains(&g)`, `set.insert(g)`, or a
    /// generic `T: PartialEq` function given one, or a `T: Same` one whose
    /// `Same: PartialEq` (ghost_holder_supertrait_comparison_returns_wrong_value).
    /// The call runs the ghost's
    /// own `eq` or `hash`, which are `true` and a constant whatever the
    /// values, inside code the verifier reads through a spec of logical
    /// equality. Creusot's ghost types implement none of these traits, so
    /// each such call is one that does not compile there. A comparison whose
    /// operand is the ghost itself is `ghost_operand_trait_use`'s.
    fn asks_ghost_holder_for_comparison_or_hash(&self, expr: &Expr<'tcx>) -> bool {
        // A function named as a callee or as a value: its item type carries
        // the instantiation.
        let Some((def_id, args)) = program_context::call_instantiation(self.typeck_results, expr)
        else {
            return false;
        };
        let lang_items = self.tcx.lang_items();
        let asked = |trait_id: DefId| {
            Some(trait_id) == lang_items.eq_trait()
                || Some(trait_id) == lang_items.partial_ord_trait()
                || ["Eq", "Ord", "Hash"].iter().any(|name| {
                    self.tcx
                        .get_diagnostic_item(rustc_span::Symbol::intern(name))
                        == Some(trait_id)
                })
        };
        let holds_ghost = |ty: rustc_middle::ty::Ty<'tcx>| {
            ty.walk().any(|arg| {
                arg.as_type()
                    .is_some_and(|ty| type_helpers::is_ghost_like_type(self.tcx, ty))
            })
        };
        // A trait's own method asks its `Self` (and `Rhs`) for the trait, and
        // a bound is asked with what the instance must meet to meet it (a
        // supertrait, a selected impl's where-clauses): the bounds
        // `program_context` reads for every call that runs. A call whose
        // bounds cannot be read is refused there.
        program_context::asked_trait_bounds(self.tcx, self.typing_env, def_id, args)
            .unwrap_or_default()
            .iter()
            .any(|bound| {
                asked(bound.trait_ref.def_id) && bound.trait_ref.args.types().any(holds_ghost)
            })
    }

    fn check_permission_identity(
        &mut self,
        span: Span,
        resource_expr: &'tcx Expr<'tcx>,
        permission_expr: &'tcx Expr<'tcx>,
    ) {
        if !self.check_permission_identity {
            return;
        }
        let expected_origin = self.resource_origin_from_expr(resource_expr);
        let Some(expected_origin) = expected_origin else {
            let resource_is_local = self.local_expr_hir_id(resource_expr).is_some();
            let permission_has_known_origin = self
                .local_uses(permission_expr)
                .iter()
                .any(|local| self.permission_origins.contains_key(local));
            if self
                .local_expr_hir_id(resource_expr)
                .is_some_and(|local| self.resource_params.contains(&local))
                && !self.local_uses(permission_expr).is_empty()
            {
                self.errors.push(GhostValidationError {
                    span,
                    message: "permission identity cannot be validated for this ghost permission \
                              API call; the runtime resource and ghost permission were not \
                              produced together"
                        .to_string(),
                });
            } else if resource_is_local && permission_has_known_origin {
                self.errors.push(GhostValidationError {
                    span,
                    message: "permission identity cannot be validated for this ghost permission \
                              API call; the runtime resource and ghost permission were not \
                              produced together"
                        .to_string(),
                });
            }
            return;
        };

        let permission_sources = self.local_uses(permission_expr);
        let permission_origins = permission_sources
            .iter()
            .filter_map(|source| self.permission_origins.get(source))
            .copied()
            .collect::<Vec<_>>();
        if permission_origins.is_empty() {
            if !permission_sources.is_empty()
                && !permission_expr_uses_option_unwrap(permission_expr)
            {
                self.errors.push(GhostValidationError {
                    span,
                    message: "permission identity cannot be validated for this ghost permission \
                              API call; the runtime resource and ghost permission were not \
                              produced together"
                        .to_string(),
                });
            }
            return;
        }

        if permission_origins
            .iter()
            .any(|origin| *origin != expected_origin)
        {
            self.errors.push(GhostValidationError {
                span,
                message: "permission identity mismatch in ghost permission API call; the \
                          permission argument is not the token produced with this resource"
                    .to_string(),
            });
        }
    }

    fn local_expr_hir_id(&self, expr: &'tcx Expr<'tcx>) -> Option<HirId> {
        match expr.kind {
            ExprKind::Path(qpath) => match self.typeck_results.qpath_res(&qpath, expr.hir_id) {
                Res::Local(hir_id) => Some(hir_id),
                _ => None,
            },
            ExprKind::AddrOf(_, _, inner)
            | ExprKind::Cast(inner, _)
            | ExprKind::Type(inner, _)
            | ExprKind::Unary(UnOp::Deref, inner) => self.local_expr_hir_id(inner),
            _ => None,
        }
    }

    fn local_uses(&self, expr: &'tcx Expr<'tcx>) -> Vec<HirId> {
        let mut collector = LocalUseCollector {
            tcx: self.tcx,
            typeck_results: self.typeck_results,
            locals: Vec::new(),
        };
        collector.visit_expr(expr);
        collector.locals
    }

    fn propagate_tuple_binding_origins(
        &mut self,
        pat: &'tcx Pat<'tcx>,
        init: &'tcx Expr<'tcx>,
    ) -> bool {
        let (PatKind::Tuple(pats, _), ExprKind::Tup(exprs)) = (pat.kind, init.kind) else {
            return false;
        };
        if pats.len() != exprs.len() {
            return false;
        }

        let mut propagated = false;
        for (pat, expr) in pats.iter().zip(exprs.iter()) {
            let Some(binding) = binding_hir_id(pat) else {
                continue;
            };
            if let Some(origin) = self.permission_origin_from_expr(expr) {
                self.permission_origins.insert(binding, origin);
                propagated = true;
            }
            if let Some(origin) = self.resource_origin_from_expr(expr) {
                self.resource_origins.insert(binding, origin);
                propagated = true;
            }
            if self
                .local_expr_hir_id(expr)
                .is_some_and(|local| self.resource_params.contains(&local))
            {
                self.resource_params.insert(binding);
                propagated = true;
            }
        }

        propagated
    }

    fn allocate_permission_origin(&mut self) -> PermissionOrigin {
        let origin = PermissionOrigin(self.next_permission_origin);
        self.next_permission_origin += 1;
        origin
    }

    fn permission_origin_from_expr(&self, expr: &'tcx Expr<'tcx>) -> Option<PermissionOrigin> {
        let mut origins = self
            .local_uses(expr)
            .into_iter()
            .filter_map(|local| self.permission_origins.get(&local).copied())
            .collect::<Vec<_>>();
        origins.sort_by_key(|origin| origin.0);
        origins.dedup();
        match origins.as_slice() {
            [] => None,
            [origin] => Some(*origin),
            _ => Some(MIXED_PERMISSION_ORIGIN),
        }
    }

    fn resource_origin_from_expr(&self, expr: &'tcx Expr<'tcx>) -> Option<PermissionOrigin> {
        self.local_expr_hir_id(expr)
            .and_then(|local| self.resource_origins.get(&local).copied())
            .or_else(|| {
                self.local_uses(expr)
                    .into_iter()
                    .find_map(|local| self.resource_origins.get(&local).copied())
            })
    }
}

fn callee_path_is_ghost_method(callee: &Expr<'_>, method_name: &str) -> bool {
    let ExprKind::Path(qpath) = &callee.kind else {
        return false;
    };
    qpath_is_ghost_method(qpath, method_name)
}

fn callee_path_is_any_ghost_method(callee: &Expr<'_>, method_names: &[&str]) -> bool {
    method_names
        .iter()
        .any(|method_name| callee_path_is_ghost_method(callee, method_name))
}

fn callee_path_is_deref_trait_method(callee: &Expr<'_>) -> bool {
    callee_path_is_owner_method(callee, &["Deref"], "deref")
        || callee_path_is_owner_method(callee, &["DerefMut"], "deref_mut")
}

fn callee_path_is_tokens_new(callee: &Expr<'_>) -> bool {
    let ExprKind::Path(qpath) = &callee.kind else {
        return false;
    };
    qpath_is_tokens_new(qpath)
}

fn callee_path_is_owner_method(callee: &Expr<'_>, owner_names: &[&str], method_name: &str) -> bool {
    let ExprKind::Path(qpath) = &callee.kind else {
        return false;
    };
    qpath_is_owner_method(qpath, owner_names, method_name)
}

fn binding_pair_slots(pat: &Pat<'_>) -> Option<(Option<HirId>, Option<HirId>)> {
    let PatKind::Tuple(pats, _) = pat.kind else {
        return None;
    };
    if pats.len() != 2 {
        return None;
    }

    Some((
        binding_slot_hir_id(&pats[0])?,
        binding_slot_hir_id(&pats[1])?,
    ))
}

fn binding_hir_id(pat: &Pat<'_>) -> Option<HirId> {
    match pat.kind {
        PatKind::Binding(_, hir_id, _, _) => Some(hir_id),
        _ => None,
    }
}

fn binding_slot_hir_id(pat: &Pat<'_>) -> Option<Option<HirId>> {
    match pat.kind {
        PatKind::Binding(_, hir_id, _, _) => Some(Some(hir_id)),
        PatKind::Wild => Some(None),
        _ => None,
    }
}

fn qpath_is_ghost_method(qpath: &QPath<'_>, method_name: &str) -> bool {
    match qpath {
        QPath::Resolved(_, path) => {
            let mut segments = path.segments.iter().rev();
            let Some(method) = segments.next() else {
                return false;
            };
            if method.ident.as_str() != method_name {
                return false;
            }
            segments
                .next()
                .is_some_and(|owner| matches!(owner.ident.as_str(), "Ghost" | "Snapshot"))
        }
        QPath::TypeRelative(ty, segment) => {
            if segment.ident.as_str() != method_name {
                return false;
            }
            matches!(
                ty.kind,
                HirTyKind::Path(QPath::Resolved(_, path))
                    if path.segments.last().is_some_and(|owner| {
                        matches!(owner.ident.as_str(), "Ghost" | "Snapshot")
                    })
            )
        }
    }
}

fn qpath_is_owner_method(qpath: &QPath<'_>, owner_names: &[&str], method_name: &str) -> bool {
    match qpath {
        QPath::Resolved(_, path) => {
            let mut segments = path.segments.iter().rev();
            let Some(method) = segments.next() else {
                return false;
            };
            if method.ident.as_str() != method_name {
                return false;
            }
            segments
                .next()
                .is_some_and(|owner| owner_names.iter().any(|name| owner.ident.as_str() == *name))
        }
        QPath::TypeRelative(ty, segment) => {
            if segment.ident.as_str() != method_name {
                return false;
            }
            matches!(
                ty.kind,
                HirTyKind::Path(QPath::Resolved(_, path))
                    if path.segments.last().is_some_and(|owner| {
                        owner_names.iter().any(|name| owner.ident.as_str() == *name)
                    })
            )
        }
    }
}

fn qpath_is_tokens_new(qpath: &QPath<'_>) -> bool {
    match qpath {
        QPath::Resolved(_, path) => {
            let mut segments = path.segments.iter().rev();
            let Some(method) = segments.next() else {
                return false;
            };
            method.ident.as_str() == "new"
                && segments
                    .next()
                    .is_some_and(|owner| owner.ident.as_str() == "Tokens")
        }
        QPath::TypeRelative(ty, segment) => {
            segment.ident.as_str() == "new"
                && matches!(
                    ty.kind,
                    HirTyKind::Path(QPath::Resolved(_, path))
                        if path.segments.last().is_some_and(|owner| {
                            owner.ident.as_str() == "Tokens"
                        })
                )
        }
    }
}

fn is_ghost_new_call(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    is_ghost_api_call(tcx, def_id, &["new"])
}

fn is_ghost_extraction_method(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    is_ghost_api_call(tcx, def_id, &["into_inner", "inner", "inner_mut"])
}

fn is_deref_trait_call(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let crate_name = tcx.crate_name(def_id.krate).to_string();
    if !matches!(crate_name.as_str(), "core" | "std") {
        return false;
    }

    let def_path = tcx.def_path_str(def_id);
    let mut components = def_path.rsplit("::");
    let Some(method_name) = components.next() else {
        return false;
    };
    let Some(owner_component) = components.next() else {
        return false;
    };

    matches!(
        (owner_component, method_name),
        ("Deref", "deref") | ("DerefMut", "deref_mut")
    )
}

fn is_tokens_new_call(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let crate_name = tcx.crate_name(def_id.krate).to_string();
    if !matches!(
        crate_name.as_str(),
        "trust_wp_std" | "trust-wp" | "creusot_std" | "creusot_contracts"
    ) {
        return false;
    }

    let def_path = tcx.def_path_str(def_id);
    def_path.rsplit("::").next() == Some("new") && def_path.contains("Tokens")
}

fn is_permcell_new_call(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    is_permission_api_call(tcx, def_id, "PermCell", &["new"])
}

fn is_perm_new_call(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    is_permission_api_call(tcx, def_id, "Perm", &["new"])
}

fn is_perm_access_call(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    is_permission_api_call(tcx, def_id, "Perm", &["as_ref", "as_mut"])
}

fn is_ghost_api_call(tcx: TyCtxt<'_>, def_id: DefId, names: &[&str]) -> bool {
    let crate_name = tcx.crate_name(def_id.krate).to_string();
    if !matches!(
        crate_name.as_str(),
        "trust_wp_std" | "trust-wp" | "creusot_std" | "creusot_contracts"
    ) {
        return false;
    }

    let def_path = tcx.def_path_str(def_id);
    let mut components = def_path.rsplit("::");
    let Some(method_name) = components.next() else {
        return false;
    };
    if !names.contains(&method_name) {
        return false;
    }
    let Some(owner_component) = components.next() else {
        return false;
    };
    matches!(owner_component, "Ghost" | "Snapshot")
        || owner_component.contains("Ghost<")
        || owner_component.contains("Snapshot<")
}

fn is_permission_api_call(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    owner_name: &str,
    names: &[&str],
) -> bool {
    let crate_name = tcx.crate_name(def_id.krate).to_string();
    if !matches!(
        crate_name.as_str(),
        "trust_wp_std" | "trust-wp" | "creusot_std" | "creusot_contracts"
    ) {
        return false;
    }

    let def_path = tcx.def_path_str(def_id);
    def_path.rsplit("::").next().is_some_and(|method| {
        names.contains(&method)
            && def_path
                .split("::")
                .any(|component| component == owner_name)
    })
}

fn is_permcell_like_type(tcx: TyCtxt<'_>, ty: rustc_middle::ty::Ty<'_>) -> bool {
    let ty = ty.peel_refs();
    let TyKind::Adt(adt_def, _) = ty.kind() else {
        return false;
    };

    let def_id = adt_def.did();
    let crate_name = tcx.crate_name(def_id.krate).to_string();
    if !matches!(
        crate_name.as_str(),
        "trust_wp_std" | "trust-wp" | "creusot_std" | "creusot_contracts"
    ) {
        return false;
    }

    tcx.def_path_str(def_id).rsplit("::").next() == Some("PermCell")
}

struct LocalUseCollector<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck_results: &'a TypeckResults<'tcx>,
    locals: Vec<HirId>,
}

impl<'tcx> Visitor<'tcx> for LocalUseCollector<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;
    type MaybeTyCtxt = TyCtxt<'tcx>;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if let ExprKind::Path(qpath) = &expr.kind {
            if let Res::Local(hir_id) = self.typeck_results.qpath_res(qpath, expr.hir_id) {
                self.locals.push(hir_id);
            }
        }

        walk_expr(self, expr);
    }
}

/// Detect ghost-permission expressions that pass through an `Option::unwrap`
/// (typically `data_own.as_ref().unwrap()` or `take().unwrap()`).
///
/// Concurrent ghost-permission flow frequently re-binds the live token through
/// an `Option<T>` so a thread can lazily transfer ownership across an atomic
/// invariant boundary. The driver's permission-origin tracker does not follow
/// the value through `Option`/assignment shapes, so it reports the runtime
/// resource and ghost permission as "not produced together" even when the
/// pattern is sound by construction (see Creusot's `examples/message_passing_*`).
///
/// Returning `true` here only suppresses the identity diagnostic when the
/// permission expression visibly uses `.unwrap()`; the wider verifier still
/// receives the ghost call for downstream checking, so this stays a
/// localised relaxation rather than a blanket bypass.
fn permission_expr_uses_option_unwrap(expr: &Expr<'_>) -> bool {
    struct UnwrapVisitor {
        found: bool,
    }
    impl<'tcx> Visitor<'tcx> for UnwrapVisitor {
        fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
            if self.found {
                return;
            }
            if let ExprKind::MethodCall(path, _, _, _) = expr.kind {
                if matches!(path.ident.as_str(), "unwrap" | "expect" | "unwrap_or") {
                    self.found = true;
                    return;
                }
            }
            walk_expr(self, expr);
        }
    }
    let mut visitor = UnwrapVisitor { found: false };
    visitor.visit_expr(expr);
    visitor.found
}

/// Reject recursive `Snapshot<&mut T>` type shapes that can encode circular
/// snapshot reasoning without entering ghost context.
pub(crate) fn validate_snapshot_self_references(tcx: TyCtxt<'_>) -> Vec<GhostValidationError> {
    check_snapshot_self_references(tcx)
}
