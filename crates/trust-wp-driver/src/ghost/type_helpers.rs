// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Type classification helpers for ghost block validation.
//!
//! Pure utility functions that classify types as ghost-like, logic types,
//! interior-mutability mutators, etc. No mutable state; all functions are
//! stateless predicates.

use std::collections::HashSet;

use rustc_hir::{intravisit::Visitor, ExprKind, HirId, Node, Pat, PatKind};
use rustc_middle::ty::{TyCtxt, TyKind, TypeckResults};

/// Check if a type is Ghost/Snapshot from trust-wp-compatible crates.
///
/// Uses crate-name validation to avoid false positives with unrelated types
/// named `Ghost` in other crates. Sibling fix to #1113 (loop ghost-return).
pub(crate) fn is_ghost_like_type(tcx: TyCtxt<'_>, ty: rustc_middle::ty::Ty<'_>) -> bool {
    // Peel references: `&T` / `&mut T` should still be recognized as ghost-like
    // when `T` is a Ghost/Snapshot type. This handles auto-ref adjustments.
    let inner = ty.peel_refs();
    if let TyKind::Adt(adt_def, _) = inner.kind() {
        let adt_def_id = adt_def.did();
        let crate_name = tcx.crate_name(adt_def_id.krate).to_string();
        let def_path = tcx.def_path_str(adt_def_id);
        return is_trust_wp_ghost_like_path(&crate_name, &def_path);
    }
    false
}

/// Check if a type is a trust-wp/creusot logical specification type (Seq, FMap, FSet, Int).
///
/// These types are specification-only and exist purely for verification purposes.
/// Mutations to them inside ghost blocks are allowed because they have no runtime
/// effect — they are erased by cfg-gating just like Ghost<T>.
pub(super) fn is_trust_wp_logic_type(tcx: TyCtxt<'_>, ty: rustc_middle::ty::Ty<'_>) -> bool {
    // Peel references: `&Seq<T>` / `&mut Seq<T>` should still be recognized.
    let inner = ty.peel_refs();
    if let TyKind::Adt(adt_def, _) = inner.kind() {
        let adt_def_id = adt_def.did();
        let crate_name = tcx.crate_name(adt_def_id.krate).to_string();
        let def_path = tcx.def_path_str(adt_def_id);
        return is_trust_wp_logic_type_path(&crate_name, &def_path);
    }
    false
}

/// Check if a (crate_name, def_path) pair identifies a trust-wp/creusot logical type.
///
/// Covers Seq, FMap, FSet, and Int — specification-only collection and numeric types.
pub(super) fn is_trust_wp_logic_type_path(crate_name: &str, def_path: &str) -> bool {
    if !matches!(
        crate_name,
        "trust_wp_std" | "trust-wp" | "creusot_std" | "creusot_contracts"
    ) {
        return false;
    }
    // Match the type name suffix after the last `::`
    let type_name = def_path.rsplit("::").next().unwrap_or("");
    matches!(type_name, "Seq" | "FMap" | "FSet" | "Int" | "Mapping")
}

/// Check whether a type is a mutable reference (`&mut T`).
pub(super) fn is_mutable_reference_type(ty: rustc_middle::ty::Ty<'_>) -> bool {
    matches!(
        ty.kind(),
        TyKind::Ref(_, _, rustc_middle::ty::Mutability::Mut)
    )
}

/// Check whether a method path is a known interior-mutability mutator.
///
/// These methods are write-capable despite taking `&self`.
pub(super) fn is_known_interior_mutability_mutator_path(def_path: &str) -> bool {
    matches!(
        def_path,
        "core::cell::Cell::set"
            | "core::cell::Cell::replace"
            | "core::cell::Cell::swap"
            | "core::cell::Cell::take"
            | "std::cell::Cell::set"
            | "std::cell::Cell::replace"
            | "std::cell::Cell::swap"
            | "std::cell::Cell::take"
            | "cell::Cell::set"
            | "cell::Cell::replace"
            | "cell::Cell::swap"
            | "cell::Cell::take"
            | "core::cell::RefCell::replace"
            | "core::cell::RefCell::replace_with"
            | "core::cell::RefCell::swap"
            | "core::cell::RefCell::take"
            | "core::cell::RefCell::borrow_mut"
            | "core::cell::RefCell::try_borrow_mut"
            | "std::cell::RefCell::replace"
            | "std::cell::RefCell::replace_with"
            | "std::cell::RefCell::swap"
            | "std::cell::RefCell::take"
            | "std::cell::RefCell::borrow_mut"
            | "std::cell::RefCell::try_borrow_mut"
            | "cell::RefCell::replace"
            | "cell::RefCell::replace_with"
            | "cell::RefCell::swap"
            | "cell::RefCell::take"
            | "cell::RefCell::borrow_mut"
            | "cell::RefCell::try_borrow_mut"
    )
}

/// Check whether the callee def-id is a known interior-mutability mutator.
pub(super) fn is_known_interior_mutability_mutator(
    tcx: TyCtxt<'_>,
    def_id: rustc_hir::def_id::DefId,
) -> bool {
    let def_path = tcx.def_path_str(def_id);
    is_known_interior_mutability_mutator_path(def_path.as_str())
}

/// Check whether a method is a `_ghost` helper defined on trust-wp/creusot logic types.
///
/// Ghost helper methods (e.g., `Seq::push_back_ghost`, `FMap::insert_ghost`) are
/// specification-only operations that exist purely for use inside `ghost!` blocks.
/// They take `&mut self` but are erased at runtime, so their receiver mutations
/// should not be flagged by ghost write validation. Part of #1581.
pub(super) fn is_trust_wp_ghost_helper_method(
    tcx: TyCtxt<'_>,
    def_id: rustc_hir::def_id::DefId,
) -> bool {
    let crate_name = tcx.crate_name(def_id.krate).to_string();
    if !matches!(
        crate_name.as_str(),
        "trust_wp_std" | "trust-wp" | "creusot_std" | "creusot_contracts"
    ) {
        return false;
    }
    let def_path = tcx.def_path_str(def_id);
    // Match method names ending with `_ghost` on known logic types
    let method_name = def_path.rsplit("::").next().unwrap_or("");
    method_name.ends_with("_ghost")
}

/// Check if a local binding originates from a ghost-like initializer.
///
/// This catches cases where type adjustments on later uses obscure the original
/// Ghost/Snapshot wrapper type.
pub(super) fn is_binding_from_ghost_like_init(
    tcx: TyCtxt<'_>,
    typeck_results: &TypeckResults<'_>,
    hir_id: HirId,
) -> bool {
    for (_parent_id, node) in tcx.hir_parent_iter(hir_id) {
        match node {
            Node::LetStmt(local) => {
                if let Some(init) = local.init {
                    return is_ghost_like_type(tcx, typeck_results.expr_ty(init));
                }
                return false;
            }
            Node::Param(_) => return false,
            _ => {}
        }
    }

    false
}

/// If a local binding is initialized from `&mut <target>`, return `<target>`.
pub(super) fn binding_mut_borrow_target<'tcx>(
    tcx: TyCtxt<'tcx>,
    hir_id: HirId,
) -> Option<&'tcx rustc_hir::Expr<'tcx>> {
    for (_parent_id, node) in tcx.hir_parent_iter(hir_id) {
        match node {
            Node::LetStmt(local) => {
                let init = local.init?;
                if let ExprKind::AddrOf(_, rustc_hir::Mutability::Mut, inner) = &init.kind {
                    return Some(*inner);
                }
                if let ExprKind::Path(rustc_hir::QPath::Resolved(_, path)) = &init.kind {
                    if let rustc_hir::def::Res::Local(alias_hir_id) = path.res {
                        if alias_hir_id != hir_id {
                            return binding_mut_borrow_target(tcx, alias_hir_id);
                        }
                    }
                }
                return None;
            }
            Node::Param(_) => return None,
            _ => {}
        }
    }

    None
}

/// Check if a (crate_name, def_path) pair identifies trust-wp-compatible
/// Ghost/Snapshot types.
///
/// Extracted for testability. Same logic as `loop_verify::is_trust_wp_ghost_def_path`.
/// Issue #1130: bare `"Ghost"` match without crate validation.
pub(super) fn is_trust_wp_ghost_like_path(crate_name: &str, def_path: &str) -> bool {
    matches!(
        (crate_name, def_path),
        (
            "trust_wp_std",
            "trust_wp_std::ghost::Ghost"
                | "trust_wp_std::ghost::Snapshot"
                | "trust_wp_std::Ghost"
                | "trust_wp_std::Snapshot"
                | "trust_wp::Ghost"
                | "trust_wp::Snapshot"
                | "creusot_std::Ghost"
                | "creusot_std::Snapshot"
                | "ghost::Ghost"
                | "ghost::Snapshot"
        ) | (
            "trust-wp",
            "trust_wp::Ghost" | "trust_wp::Snapshot" | "Ghost" | "Snapshot"
        ) | (
            "creusot_std",
            "creusot_std::ghost::Ghost"
                | "creusot_std::ghost::Snapshot"
                | "creusot_std::Ghost"
                | "creusot_std::Snapshot"
                | "ghost::Ghost"
                | "ghost::Snapshot"
        ) | (
            "creusot_contracts",
            "creusot_contracts::Ghost"
                | "creusot_contracts::Snapshot"
                | "creusot_contracts::ghost::Ghost"
                | "creusot_contracts::ghost::Snapshot"
        )
    )
}

/// Collects all variables bound (declared) within an expression.
pub(super) struct BoundVariableCollector {
    pub(super) bound_variables: HashSet<HirId>,
}

impl BoundVariableCollector {
    pub(super) fn new() -> Self {
        Self {
            bound_variables: HashSet::new(),
        }
    }
}

impl<'tcx> Visitor<'tcx> for BoundVariableCollector {
    fn visit_pat(&mut self, pat: &'tcx Pat<'tcx>) {
        // Collect binding patterns (let x = ...)
        if let PatKind::Binding(_, hir_id, _, _) = pat.kind {
            self.bound_variables.insert(hir_id);
        }
        // Continue walking to find nested bindings
        rustc_hir::intravisit::walk_pat(self, pat);
    }
}
