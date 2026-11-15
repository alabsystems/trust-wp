// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The scopes rustc consults between a clause and its owner's module.
//!
//! rustc resolves a name innermost first: the clause's own binders, the
//! owner's generics, then every block that encloses the place the clause is
//! resolved — its locals (only where the clause stands inside a body) and its
//! items and imports, through any number of enclosing items — and only then
//! the module. Creusot and the type-check vehicle both place a function's
//! `requires`/`ensures` as the FIRST statement of its body, so the body's own
//! top-level items are in that scope too; a closure's contract and a loop
//! invariant or assertion are resolved inside the enclosing body.
//!
//! [`lookup`] answers the block part and nothing else: `Unbound` hands the
//! name to the module lookup the caller already performs. It answers exactly
//! where HIR records rustc's answer (items, single imports, globs over a
//! module) and refuses wherever the answer depends on something HIR does not
//! give it here: a clause's position inside a body, a local binding, an
//! unenumerable glob, or opaque macro hygiene. A refusal leaves the name
//! unresolved and the encoder refuses the clause; a guess would give the
//! grant and the obligation one wrong meaning
//! (block_local_logic_fn_name_resolved_in_module_granted.rs and its siblings).

use rustc_hir::{
    def::{DefKind, Namespace, Res},
    def_id::{DefId, LocalDefId},
    intravisit::{self, Visitor},
    Block, Body, ExprKind, ItemKind, Node, Pat, PatKind, StmtKind, UseKind, UsePath,
};
use rustc_middle::{hir::nested_filter, ty::TyCtxt};
use rustc_span::Symbol;

/// Where a clause stands relative to its owner's body, which decides whether
/// the owner's locals can be in its scope.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum ClausePosition {
    /// A function's `requires`/`ensures`, a logic function's body or clauses:
    /// resolved at the top of the body, before any local is bound.
    Signature,
    /// A loop invariant or variant, or an assertion: resolved somewhere
    /// inside the owner's body, after locals the text cannot place.
    Body,
}

/// What the block scopes around a clause bind a name to.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum BlockBinding {
    /// No block between the clause and its module binds the name.
    Unbound,
    /// The innermost block binding, exactly as rustc resolves it.
    Def(DefKind, DefId),
    /// A block binds the name to something this lookup cannot pin down.
    Refused,
}

/// Resolve `name` in `ns` through the block scopes around a clause of
/// `owner` (see the module documentation for the order).
pub(crate) fn lookup(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    name: &str,
    ns: Namespace,
    position: ClausePosition,
) -> BlockBinding {
    lookup_until(tcx, owner, name, ns, position, None)
}

/// `lookup` restricted to the block scopes INSIDE the item `until` (the
/// owner itself, or an item whose body encloses it): the scopes that shadow
/// what `until` itself declares, such as its generic parameters. Nothing at
/// or above `until` is consulted.
pub(crate) fn lookup_within(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    name: &str,
    ns: Namespace,
    position: ClausePosition,
    until: LocalDefId,
) -> BlockBinding {
    lookup_until(tcx, owner, name, ns, position, Some(until))
}

fn lookup_until(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    name: &str,
    ns: Namespace,
    position: ClausePosition,
    until: Option<LocalDefId>,
) -> BlockBinding {
    if tcx.def_kind(owner) == DefKind::Mod {
        return BlockBinding::Unbound;
    }
    // A clause of an item an opaque (`macro` 2.0) expansion wrote is resolved
    // at that expansion's definition site, which clause TEXT does not carry.
    if !written_at_root_context(tcx, owner) {
        return BlockBinding::Refused;
    }
    let symbol = Symbol::intern(name);
    if ns == Namespace::ValueNS && local_may_shadow(tcx, owner, symbol, position) {
        return BlockBinding::Refused;
    }
    if let Some(body) = tcx.hir_maybe_body_owned_by(owner) {
        match own_body_binding(tcx, owner, body, symbol, ns) {
            BlockBinding::Unbound => {}
            answered => return answered,
        }
    }
    if until == Some(owner) {
        return BlockBinding::Unbound;
    }
    for (_, node) in tcx.hir_parent_iter(tcx.local_def_id_to_hir_id(owner)) {
        let item = match node {
            Node::Item(item) => Some(item.owner_id.def_id),
            Node::ImplItem(item) => Some(item.owner_id.def_id),
            Node::TraitItem(item) => Some(item.owner_id.def_id),
            _ => None,
        };
        if until.is_some() && item == until {
            break;
        }
        match node {
            Node::Block(block) => {
                if let Some(binding) = block_binding(tcx, owner, block, symbol, ns) {
                    return binding;
                }
            }
            // A module is a barrier: nothing outside it is in scope by a bare
            // name, and the caller's module lookup takes over from here.
            Node::Item(item) if matches!(item.kind, ItemKind::Mod(..)) => break,
            Node::Crate(_) => break,
            _ => {}
        }
    }
    BlockBinding::Unbound
}

/// Whether `owner` was written where a user-written clause's names resolve:
/// no opaque macro mark survives on its name (`macro_rules!` and proc-macro
/// call-site/mixed-site marks do not hide names and normalize away).
fn written_at_root_context(tcx: TyCtxt<'_>, owner: LocalDefId) -> bool {
    let span = tcx
        .def_ident_span(owner)
        .unwrap_or_else(|| tcx.def_span(owner));
    span.normalize_to_macros_2_0().ctxt().is_root()
}

/// Whether a local binding named `symbol` may be in scope of the clause.
///
/// A closure's clauses are resolved inside the body that encloses the
/// closure, and a `Body`-position clause inside its owner's own body; a local
/// shadows every item there. Which bindings precede the clause is a question
/// of position the clause text does not answer, so any binding of the name in
/// that body refuses. A `Signature` clause of an item stands before every
/// local of its body, and no item sees the locals of the body around it.
fn local_may_shadow(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    symbol: Symbol,
    position: ClausePosition,
) -> bool {
    let scope_body = if tcx.is_typeck_child(owner.to_def_id()) {
        Some(tcx.typeck_root_def_id_local(owner))
    } else if position == ClausePosition::Body {
        Some(owner)
    } else {
        None
    };
    let Some(body) = scope_body.and_then(|root| tcx.hir_maybe_body_owned_by(root)) else {
        return false;
    };
    let mut finder = BindingFinder {
        tcx,
        symbol,
        found: false,
    };
    finder.visit_body(body);
    finder.found
}

/// Finds a pattern binding of one name in a body and every closure inside it
/// (nested items have their own bodies and are not visited).
struct BindingFinder<'tcx> {
    tcx: TyCtxt<'tcx>,
    symbol: Symbol,
    found: bool,
}

impl<'tcx> Visitor<'tcx> for BindingFinder<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;
    type MaybeTyCtxt = TyCtxt<'tcx>;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_pat(&mut self, pat: &'tcx Pat<'tcx>) {
        if let PatKind::Binding(_, _, ident, _) = pat.kind {
            if ident.name == self.symbol {
                self.found = true;
            }
        }
        intravisit::walk_pat(self, pat);
    }
}

/// The owner's own body: its top-level block is the scope a `Signature`
/// clause of a function is resolved in (Creusot's expansion and the
/// type-check vehicle both put the clause there). A binding in any nested
/// block is visible to some positions of a `Body` clause and not others, and
/// a closure's clauses are resolved outside its body; either way refuse.
fn own_body_binding<'tcx>(
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    body: &'tcx Body<'tcx>,
    symbol: Symbol,
    ns: Namespace,
) -> BlockBinding {
    let mut blocks = BlocksBinding {
        tcx,
        owner,
        symbol,
        ns,
        found: Vec::new(),
    };
    blocks.visit_body(body);
    let top_level = match body.value.kind {
        ExprKind::Block(block, _) => Some(block.hir_id),
        _ => None,
    };
    match blocks.found.as_slice() {
        [] => BlockBinding::Unbound,
        [(block, binding)]
            if Some(*block) == top_level && !tcx.is_typeck_child(owner.to_def_id()) =>
        {
            *binding
        }
        _ => BlockBinding::Refused,
    }
}

/// Every block of one body (closures included, nested items not) that binds
/// the name, with what it binds.
struct BlocksBinding<'tcx> {
    tcx: TyCtxt<'tcx>,
    owner: LocalDefId,
    symbol: Symbol,
    ns: Namespace,
    found: Vec<(rustc_hir::HirId, BlockBinding)>,
}

impl<'tcx> Visitor<'tcx> for BlocksBinding<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;
    type MaybeTyCtxt = TyCtxt<'tcx>;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_block(&mut self, block: &'tcx Block<'tcx>) {
        if let Some(binding) = block_binding(self.tcx, self.owner, block, self.symbol, self.ns) {
            self.found.push((block.hir_id, binding));
        }
        intravisit::walk_block(self, block);
    }
}

/// What one block binds `symbol` to in `ns`, or `None` when it does not bind
/// it. Rust's order within one scope: an explicit item or import wins over a
/// glob; two explicit bindings, or two globs bringing different items, are
/// an error rustc reports, and are refused here.
fn block_binding(
    tcx: TyCtxt<'_>,
    owner: LocalDefId,
    block: &Block<'_>,
    symbol: Symbol,
    ns: Namespace,
) -> Option<BlockBinding> {
    let mut explicit: Vec<Res> = Vec::new();
    let mut globs: Vec<&UsePath<'_>> = Vec::new();
    for stmt in block.stmts {
        let StmtKind::Item(item_id) = stmt.kind else {
            continue;
        };
        let item = tcx.hir_item(item_id);
        // A use item holds every leaf of its tree: its globs go here,
        // its single imports are bindings below.
        globs.extend(
            crate::hir_use::item_use_leaves(item)
                .into_iter()
                .filter_map(|(path, kind)| matches!(kind, UseKind::Glob).then_some(path)),
        );
        for (ident, binding_ns, res) in item_bindings(tcx, item) {
            // An opaque (`macro` 2.0) mark hides the item from a clause
            // written at the root context (`written_at_root_context`).
            if ident.name == symbol
                && binding_ns == ns
                && ident.span.normalize_to_macros_2_0().ctxt().is_root()
            {
                explicit.push(res);
            }
        }
    }
    match explicit.as_slice() {
        [res] => return Some(binding_of(*res)),
        [] => {}
        _ => return Some(BlockBinding::Refused),
    }
    let module = tcx.parent_module_from_def_id(owner).to_def_id();
    let mut brought: Vec<Res> = Vec::new();
    for path in globs {
        // rustc records a module glob in the type namespace; anything else (an
        // enum's variants, an unresolved path) is not enumerated here.
        let Some(Res::Def(DefKind::Mod, target)) = path.res.type_ns else {
            return Some(BlockBinding::Refused);
        };
        let children = match target.as_local() {
            Some(local) => tcx.module_children_local(local),
            None => tcx.module_children(target),
        };
        for child in children {
            if child.ident.name == symbol
                && child.res.ns() == Some(ns)
                && child.vis.is_accessible_from(module, tcx)
            {
                let res = child.res.expect_non_local();
                if !brought.contains(&res) {
                    brought.push(res);
                }
            }
        }
    }
    match brought.as_slice() {
        [] => None,
        [res] => Some(binding_of(*res)),
        _ => Some(BlockBinding::Refused),
    }
}

fn binding_of(res: Res) -> BlockBinding {
    match res {
        Res::Def(kind, def_id) => BlockBinding::Def(kind, def_id),
        _ => BlockBinding::Refused,
    }
}

/// The names one block item binds, each with its namespace and meaning.
fn item_bindings(
    tcx: TyCtxt<'_>,
    item: &rustc_hir::Item<'_>,
) -> Vec<(rustc_span::Ident, Namespace, Res)> {
    let def_id = item.owner_id.to_def_id();
    let mut out = Vec::new();
    match item.kind {
        ItemKind::Use(_) => {
            for (path, kind) in crate::hir_use::item_use_leaves(item) {
                let UseKind::Single(ident) = kind else {
                    continue;
                };
                if let Some(res) = path.res.type_ns {
                    out.push((ident, Namespace::TypeNS, res));
                }
                if let Some(res) = path.res.value_ns {
                    out.push((ident, Namespace::ValueNS, res));
                }
            }
        }
        ItemKind::Macro(..) => {}
        // Refused wherever it binds: `Res::Err` is never a definition.
        ItemKind::ExternCrate(_, ident) => out.push((ident, Namespace::TypeNS, Res::Err)),
        ItemKind::ForeignMod { items, .. } => {
            for foreign in items {
                let foreign = tcx.hir_foreign_item(*foreign);
                let foreign_def = foreign.owner_id.to_def_id();
                let kind = tcx.def_kind(foreign_def);
                if let Some(ns) = kind.ns() {
                    out.push((foreign.ident, ns, Res::Def(kind, foreign_def)));
                }
            }
        }
        _ => {
            let Some(ident) = item.kind.ident() else {
                return out;
            };
            let kind = tcx.def_kind(def_id);
            if let Some(ns) = kind.ns() {
                out.push((ident, ns, Res::Def(kind, def_id)));
            }
            // A tuple or unit struct also binds its constructor as a value.
            if let ItemKind::Struct(_, _, data) | ItemKind::Union(_, _, data) = item.kind {
                if let Some((ctor_kind, _, ctor_def)) = data.ctor() {
                    out.push((
                        ident,
                        Namespace::ValueNS,
                        Res::Def(
                            DefKind::Ctor(rustc_hir::def::CtorOf::Struct, ctor_kind),
                            ctor_def.to_def_id(),
                        ),
                    ));
                }
            }
        }
    }
    out
}

#[cfg(test)]
#[path = "block_scope_tests.rs"]
mod tests;
