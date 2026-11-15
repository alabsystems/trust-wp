// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The type names the contract parser reads by their spelling (`u8`, `Int`,
//! `Seq`, ..: `trust_wp_core::contract_parser::spelled_types`) that this
//! crate gives another meaning somewhere: a local type, module, trait or
//! generic parameter of that name, or an import that binds the name to
//! anything but the item it spells. The parser refuses a clause that spells
//! one of them in a type position or as a path's head (D-202).
//!
//! It also collects the names the crate binds to a type holding a machine
//! integer where the parser cannot see it (`type Byte = u8;`, `type Out =
//! u8;`, `Self` in `impl Tr for u8`): the parser reads no such name, so a
//! binder of one would get no range (D-205).
//!
//! And the names it binds to a module or a crate (a module of any scope, an
//! extern crate, the extern prelude, a module import): a written type's path
//! through one of them names an item the parser cannot see (D-206).
//!
//! The sets are crate-wide because the parser has no scope: which binding a
//! clause sees depends on where it stands, and every clause of the crate is
//! parsed by the same code whatever lane reads it (the owner's verification,
//! a call site reading a callee's contract, a loop clause, an assertion, a
//! logic function's body).

use std::collections::BTreeSet;

use rustc_hir::{
    def::{DefKind, Namespace, Res},
    def_id::DefId,
    PrimTy, UseKind,
};
use rustc_middle::ty::{GenericParamDefKind, TyCtxt, TyKind};
use trust_wp_core::contract_parser::spelled_types::is_spelled_type_name;

/// The crates whose items ARE the meanings the parser reads a spelled name
/// with: the standard library's primitives' modules and collections, and the
/// model crates' `Int` and `Seq`.
const CANONICAL_CRATES: &[&str] = &[
    "core",
    "std",
    "alloc",
    "trust_wp_std",
    "trust_wp",
    "creusot_std",
    "creusot_contracts",
];

/// Every spelled type name this crate binds in the type namespace to
/// something other than what the parser reads it as.
pub(super) fn shadowed_type_names(tcx: TyCtxt<'_>) -> BTreeSet<String> {
    let mut shadowed = BTreeSet::new();
    for local in tcx.iter_local_def_id() {
        match tcx.def_kind(local) {
            DefKind::Use => {
                // Each use tree is its own definition: a nested one is
                // read when its own def id comes up.
                let Some(tree) = crate::hir_use::use_tree_of_def(tcx, local) else {
                    continue;
                };
                let (path, kind) = (tree.prefix, tree.kind);
                match kind {
                    UseKind::Single(ident) => {
                        let name = ident.name.as_str();
                        if is_spelled_type_name(name) {
                            if let Some(res) = path.res.type_ns {
                                if !is_canonical(tcx, name, res) {
                                    shadowed.insert(name.to_string());
                                }
                            }
                        }
                    }
                    UseKind::Glob => glob_bindings(tcx, path.res.type_ns, &mut shadowed),
                    UseKind::Nested { .. } => {}
                }
            }
            DefKind::Struct
            | DefKind::Enum
            | DefKind::Union
            | DefKind::TyAlias
            | DefKind::Trait
            | DefKind::TraitAlias
            | DefKind::Mod
            | DefKind::ForeignTy
            | DefKind::TyParam
            | DefKind::ExternCrate => {
                if let Some(name) = tcx.opt_item_name(local.to_def_id()) {
                    if is_spelled_type_name(name.as_str()) {
                        shadowed.insert(name.to_string());
                    }
                }
            }
            _ => {}
        }
    }
    shadowed
}

/// The spelled names a glob import brings into scope other than as what they
/// spell: a module's type-namespace children, an enum's variants.
fn glob_bindings(tcx: TyCtxt<'_>, target: Option<Res>, shadowed: &mut BTreeSet<String>) {
    match target {
        Some(Res::Def(DefKind::Mod, module)) => {
            let children = match module.as_local() {
                Some(local) => tcx.module_children_local(local),
                None => tcx.module_children(module),
            };
            for child in children {
                let name = child.ident.name.as_str();
                if is_spelled_type_name(name)
                    && child.res.ns() == Some(Namespace::TypeNS)
                    && !is_canonical(tcx, name, child.res.expect_non_local())
                {
                    shadowed.insert(name.to_string());
                }
            }
        }
        Some(Res::Def(DefKind::Enum, adt)) => {
            for variant in tcx.adt_def(adt).variants() {
                if is_spelled_type_name(variant.name.as_str()) {
                    shadowed.insert(variant.name.to_string());
                }
            }
        }
        _ => {}
    }
}

/// Whether `res`, bound to `name`, is the meaning the parser reads `name`
/// with: the primitive itself, or the standard or model crates' item of that
/// name (`core::u8`, the prelude's `Int`).
fn is_canonical(tcx: TyCtxt<'_>, name: &str, res: Res) -> bool {
    match res {
        Res::PrimTy(prim) => prim.name_str() == name,
        Res::Def(_, def_id) => {
            !def_id.is_local()
                && tcx
                    .opt_item_name(def_id)
                    .is_some_and(|item| item.as_str() == name)
                && CANONICAL_CRATES.contains(&tcx.crate_name(def_id.krate).as_str())
        }
        _ => false,
    }
}

/// Every name this crate binds in the type namespace to a type that holds a
/// machine integer where the parser does not see the integer: a `type N =
/// ..` of any scope (a body's included), a single import of such an alias
/// under any name, an integer primitive imported under a name other than its
/// own, a glob's children of either kind, an associated type an impl (or a
/// trait's default) sets to one (`type Out = u8;`, spelled `Self::Out`), and
/// `Self` where an impl's self type holds one (`impl Tr for u8`, whose
/// inherited clauses are restated with `Self` = `u8`, D-110). The target is
/// read through rustc (`type_of`), so an alias of an alias is seen through.
pub(super) fn machine_int_alias_names(tcx: TyCtxt<'_>) -> BTreeSet<String> {
    let mut names = BTreeSet::new();
    for local in tcx.iter_local_def_id() {
        match tcx.def_kind(local) {
            DefKind::TyAlias => {
                if alias_holds_machine_int(tcx, local.to_def_id()) {
                    if let Some(name) = tcx.opt_item_name(local.to_def_id()) {
                        names.insert(name.to_string());
                    }
                }
            }
            DefKind::AssocTy => {
                // Only a value has a type: an impl's, or a trait default's
                // (`defaultness` is asked of a trait item only).
                let has_value = match tcx.def_kind(tcx.local_parent(local)) {
                    DefKind::Impl { .. } => true,
                    DefKind::Trait => tcx.defaultness(local.to_def_id()).has_value(),
                    _ => false,
                };
                if has_value && alias_holds_machine_int(tcx, local.to_def_id()) {
                    if let Some(name) = tcx.opt_item_name(local.to_def_id()) {
                        names.insert(name.to_string());
                    }
                }
            }
            DefKind::Impl { .. } => {
                if alias_holds_machine_int(tcx, local.to_def_id()) {
                    names.insert("Self".to_string());
                }
            }
            DefKind::Use => {
                // Each use tree is its own definition: a nested one is
                // read when its own def id comes up.
                let Some(tree) = crate::hir_use::use_tree_of_def(tcx, local) else {
                    continue;
                };
                let (path, kind) = (tree.prefix, tree.kind);
                match kind {
                    UseKind::Single(ident) => {
                        if let Some(res) = path.res.type_ns {
                            if binds_machine_int(tcx, ident.name.as_str(), res) {
                                names.insert(ident.name.to_string());
                            }
                        }
                    }
                    UseKind::Glob => {
                        let Some(Res::Def(DefKind::Mod, module)) = path.res.type_ns else {
                            continue;
                        };
                        let children = match module.as_local() {
                            Some(local) => tcx.module_children_local(local),
                            None => tcx.module_children(module),
                        };
                        for child in children {
                            let name = child.ident.name.as_str();
                            if child.res.ns() == Some(Namespace::TypeNS)
                                && binds_machine_int(tcx, name, child.res.expect_non_local())
                            {
                                names.insert(name.to_string());
                            }
                        }
                    }
                    UseKind::Nested { .. } => {}
                }
            }
            _ => {}
        }
    }
    names
}

/// Whether `res`, bound to `name`, is a type alias holding a machine integer
/// or an integer primitive the parser does not read under `name`.
fn binds_machine_int(tcx: TyCtxt<'_>, name: &str, res: Res) -> bool {
    match res {
        Res::PrimTy(prim @ (PrimTy::Int(_) | PrimTy::Uint(_))) => prim.name_str() != name,
        Res::Def(DefKind::TyAlias, alias) => alias_holds_machine_int(tcx, alias),
        _ => false,
    }
}

/// Whether the type `alias` stands for (an alias's target, an associated
/// type's value, an impl's self type) holds a machine integer anywhere a type
/// walk reaches (itself, a reference's referent, a tuple's or a generic
/// argument's component). A projection it is not normalized through
/// (`<S as Tr>::Out`) may be one, and counts.
///
/// A parameter's default is a type the name stands for too: spelled without
/// arguments, `type B<T = u8> = T;` is `u8`
/// (quantifier_binder_alias_generic_default_of_machine_int_read_unbounded_granted.rs,
/// D-207).
fn alias_holds_machine_int(tcx: TyCtxt<'_>, alias: DefId) -> bool {
    let holds = |def_id: DefId| {
        let ty = tcx.type_of(def_id).instantiate_identity().skip_norm_wip();
        ty.walk().any(|arg| {
            arg.as_type().is_some_and(|ty| {
                matches!(
                    ty.kind(),
                    TyKind::Int(_) | TyKind::Uint(_) | TyKind::Alias(..)
                )
            })
        })
    };
    holds(alias)
        || tcx.generics_of(alias).own_params.iter().any(|param| {
            matches!(
                param.kind,
                GenericParamDefKind::Type {
                    has_default: true,
                    ..
                }
            ) && holds(param.def_id)
        })
}

/// Every name this crate binds in the type namespace to a module or a crate:
/// the standard crates, every crate the extern prelude holds or the crate
/// graph loads, a module or `extern crate` of any scope (a body's included),
/// and a module or crate root a single or glob import binds (D-206).
pub(super) fn module_names(tcx: TyCtxt<'_>) -> BTreeSet<String> {
    let mut names: BTreeSet<String> = ["core", "std", "alloc"]
        .into_iter()
        .map(String::from)
        .collect();
    names.extend(tcx.sess.opts.externs.iter().map(|(name, _)| name.clone()));
    names.extend(
        tcx.crates(())
            .iter()
            .map(|&krate| tcx.crate_name(krate).to_string()),
    );
    let is_module = |res: Res| matches!(res, Res::Def(DefKind::Mod, _));
    for local in tcx.iter_local_def_id() {
        match tcx.def_kind(local) {
            DefKind::Mod | DefKind::ExternCrate => {
                if let Some(name) = tcx.opt_item_name(local.to_def_id()) {
                    names.insert(name.to_string());
                }
            }
            DefKind::Use => {
                // Each use tree is its own definition: a nested one is
                // read when its own def id comes up.
                let Some(tree) = crate::hir_use::use_tree_of_def(tcx, local) else {
                    continue;
                };
                let (path, kind) = (tree.prefix, tree.kind);
                match kind {
                    UseKind::Single(ident) => {
                        if path.res.type_ns.is_some_and(is_module) {
                            names.insert(ident.name.to_string());
                        }
                    }
                    UseKind::Glob => {
                        let Some(Res::Def(DefKind::Mod, module)) = path.res.type_ns else {
                            continue;
                        };
                        let children = match module.as_local() {
                            Some(local) => tcx.module_children_local(local),
                            None => tcx.module_children(module),
                        };
                        for child in children {
                            if is_module(child.res.expect_non_local()) {
                                names.insert(child.ident.name.to_string());
                            }
                        }
                    }
                    UseKind::Nested { .. } => {}
                }
            }
            _ => {}
        }
    }
    names
}
