// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The leaves of a `use` item.
//!
//! HIR lowers `use a::{b, c::*};` to ONE item whose `UseKind::Nested` holds
//! the subtrees; each subtree has its own `LocalDefId` (a
//! `Node::NestedUseTree`), the path segments it spells, and its own
//! resolution. A reader asks about the leaves: each `Single` or `Glob` with
//! the `UsePath` whose `res` is that leaf's own. A leaf's segments are the
//! ones it spells, not the full path.

use rustc_hir::{ItemKind, Node, UseKind, UsePath, UseTree};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;

/// Every `Single` and `Glob` leaf of `tree`, in source order. A `Nested`
/// kind is never returned.
pub(crate) fn use_leaves<'hir>(tree: &UseTree<'hir>) -> Vec<(&'hir UsePath<'hir>, UseKind<'hir>)> {
    let mut leaves = Vec::new();
    collect_leaves(tree, &mut leaves);
    leaves
}

fn collect_leaves<'hir>(tree: &UseTree<'hir>, out: &mut Vec<(&'hir UsePath<'hir>, UseKind<'hir>)>) {
    match tree.kind {
        UseKind::Single(_) | UseKind::Glob => out.push((tree.prefix, tree.kind)),
        UseKind::Nested { items } => {
            for (subtree, _, _) in items {
                collect_leaves(subtree, out);
            }
        }
    }
}

/// The leaves of a `use` item; an item of any other kind has none.
pub(crate) fn item_use_leaves<'hir>(
    item: &rustc_hir::Item<'hir>,
) -> Vec<(&'hir UsePath<'hir>, UseKind<'hir>)> {
    match item.kind {
        ItemKind::Use(ref tree) => use_leaves(tree),
        _ => Vec::new(),
    }
}

/// The use tree a `DefKind::Use` definition names: a `use` item's whole tree,
/// or a nested subtree, which has its own `LocalDefId`. A reader walking every
/// `DefKind::Use` definition reads each tree's own kind and skips a `Nested`
/// one, whose subtrees it meets as definitions of their own -- the old
/// lowering's leaf items and its skipped `ListStem`.
pub(crate) fn use_tree_of_def<'tcx>(
    tcx: TyCtxt<'tcx>,
    def: LocalDefId,
) -> Option<&'tcx UseTree<'tcx>> {
    match tcx.hir_node_by_def_id(def) {
        Node::Item(rustc_hir::Item {
            kind: ItemKind::Use(tree),
            ..
        }) => Some(tree),
        Node::NestedUseTree(tree) => Some(tree),
        _ => None,
    }
}
