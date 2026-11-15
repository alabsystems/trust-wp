// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The value a bare constant name in a clause stands for.
//!
//! Clauses are unscoped text, and a bare `K` in one is substituted by NAME
//! with the value of the local constant item called `K`, never looked up in
//! the scope of the item whose clause it is. That is sound only when nothing
//! else in the crate can be spelled `K`: a same-named constant in another
//! module, an import of another crate's constant under that name, a static,
//! a unit constructor, a const generic parameter or a local binding each give
//! the spelling a meaning the substituted value is not
//! (const_short_name_collision_other_module_granted.rs and its siblings).
//! Such a name is refused wherever the substitution reaches — replaced by a
//! marker the encoder refuses — instead of being given one of its meanings.
//!
//! A name whose meanings include no constant item or static is left alone:
//! nothing substitutes it by value, and whatever resolves it elsewhere is not
//! this table's to second-guess.

use std::collections::{HashMap, HashSet};

use rustc_hir::{
    def::{CtorKind, DefKind, Res},
    def_id::DefId,
    intravisit::{self, Visitor},
    HirId, ItemKind, Pat, PatKind, UseKind,
};
use rustc_middle::ty::TyCtxt;
use trust_wp_core::{
    formula::PureExpr,
    logic::identity::{is_refused_logic_fn_marker, logic_fn_unresolved_marker},
};

/// One thing a bare spelling can denote somewhere in the crate.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Meaning {
    Item(DefId),
    Binding(HirId),
    /// A block-level glob import whose names are not listed here: it may give
    /// any name a meaning.
    UnlistedGlob,
}

/// Whether a bare spelling may be substituted by a constant's value here: a
/// constant item or a static gives it a value-level meaning the table would
/// otherwise stand in for.
fn is_constant_item(kind: DefKind) -> bool {
    matches!(
        kind,
        DefKind::Const { .. } | DefKind::AssocConst { .. } | DefKind::Static { .. }
    )
}

/// Every kind a bare value-namespace spelling can resolve to that could be
/// read as a value in a clause.
fn is_value_meaning(kind: DefKind) -> bool {
    is_constant_item(kind)
        || matches!(
            kind,
            DefKind::ConstParam | DefKind::Ctor(_, CtorKind::Const)
        )
}

/// Collects every pattern binding of one body (parameters, `let`, match arms).
struct BindingNames<'a> {
    names: &'a mut HashMap<String, HashSet<Meaning>>,
}

impl<'v> Visitor<'v> for BindingNames<'_> {
    fn visit_pat(&mut self, pat: &'v Pat<'v>) {
        if let PatKind::Binding(_, hir_id, ident, _) = pat.kind {
            self.names
                .entry(ident.name.to_string())
                .or_default()
                .insert(Meaning::Binding(hir_id));
        }
        intravisit::walk_pat(self, pat);
    }
}

/// Every meaning each bare name has somewhere in the crate.
fn bare_name_meanings(tcx: TyCtxt<'_>) -> HashMap<String, HashSet<Meaning>> {
    let mut meanings: HashMap<String, HashSet<Meaning>> = HashMap::new();
    for local in tcx.iter_local_def_id() {
        let def_id = local.to_def_id();
        let kind = tcx.def_kind(def_id);
        if is_value_meaning(kind) {
            if let Some(name) = tcx.opt_item_name(def_id) {
                meanings
                    .entry(name.to_string())
                    .or_default()
                    .insert(Meaning::Item(def_id));
            }
        }
        // What a module binds by name: its own items and every import,
        // including another crate's constants and glob-imported names.
        if kind == DefKind::Mod {
            for child in tcx.module_children_local(local) {
                if let Res::Def(child_kind, child_def_id) = child.res {
                    if is_value_meaning(child_kind) {
                        meanings
                            .entry(child.ident.name.to_string())
                            .or_default()
                            .insert(Meaning::Item(child_def_id));
                    }
                }
            }
        }
    }
    // What an import declared in a BLOCK binds: module children cover only
    // the imports of modules (block_use_const_resolved_as_module_const_granted.rs).
    for item_id in tcx.hir_crate_items(()).free_items() {
        let item = tcx.hir_item(item_id);
        let ItemKind::Use(_) = item.kind else {
            continue;
        };
        if tcx.def_kind(tcx.parent(item.owner_id.to_def_id())) == DefKind::Mod {
            continue;
        }
        for (path, use_kind) in crate::hir_use::item_use_leaves(item) {
            for (name, meaning) in block_import_value_meanings(tcx, path, use_kind) {
                meanings.entry(name).or_default().insert(meaning);
            }
        }
    }
    for owner in tcx.hir_body_owners() {
        let body = tcx.hir_body_owned_by(owner);
        let mut visitor = BindingNames {
            names: &mut meanings,
        };
        for param in body.params {
            visitor.visit_pat(param.pat);
        }
        visitor.visit_expr(body.value);
    }
    meanings
}

/// The value meanings one block-level import gives names. A glob over a
/// module brings every child the module has (visible or not: an extra
/// meaning can only refuse) and a glob over an enum its unit variants; a
/// glob this cannot list is read as giving every constant name a meaning.
fn block_import_value_meanings(
    tcx: TyCtxt<'_>,
    path: &rustc_hir::UsePath<'_>,
    use_kind: UseKind<'_>,
) -> Vec<(String, Meaning)> {
    let mut out = Vec::new();
    match use_kind {
        UseKind::Single(ident) => {
            if let Some(Res::Def(kind, def_id)) = path.res.value_ns {
                if is_value_meaning(kind) {
                    out.push((ident.name.to_string(), Meaning::Item(def_id)));
                }
            }
        }
        UseKind::Glob => {
            let target = [path.res.type_ns, path.res.value_ns]
                .into_iter()
                .flatten()
                .find_map(|res| match res {
                    Res::Def(kind @ (DefKind::Mod | DefKind::Enum), def_id) => Some((kind, def_id)),
                    _ => None,
                });
            match target {
                Some((DefKind::Mod, target)) => {
                    let children = match target.as_local() {
                        Some(local) => tcx.module_children_local(local),
                        None => tcx.module_children(target),
                    };
                    for child in children {
                        if let Res::Def(kind, def_id) = child.res {
                            if is_value_meaning(kind) {
                                out.push((child.ident.name.to_string(), Meaning::Item(def_id)));
                            }
                        }
                    }
                }
                Some((_, enum_def)) => {
                    for variant in tcx.adt_def(enum_def).variants() {
                        if let Some((CtorKind::Const, ctor)) = variant.ctor {
                            out.push((variant.name.to_string(), Meaning::Item(ctor)));
                        }
                    }
                }
                None => out.push((UNLISTED_GLOB.to_string(), Meaning::UnlistedGlob)),
            }
        }
        UseKind::Nested { .. } => {}
    }
    out
}

/// The key under which a glob this module cannot enumerate is recorded.
const UNLISTED_GLOB: &str = "*";

/// Bare names a clause may not be given a value for: a constant item or a
/// static is one of their meanings, and they have another.
fn ambiguous_constant_names(tcx: TyCtxt<'_>) -> HashSet<String> {
    let mut meanings = bare_name_meanings(tcx);
    let unlisted_glob = meanings.remove(UNLISTED_GLOB).is_some();
    meanings
        .into_iter()
        .filter(|(_, meanings)| {
            (meanings.len() > 1 || unlisted_glob)
                && meanings.iter().any(|meaning| match meaning {
                    Meaning::Item(def_id) => is_constant_item(tcx.def_kind(*def_id)),
                    Meaning::Binding(_) | Meaning::UnlistedGlob => false,
                })
        })
        .map(|(name, _)| name)
        .collect()
}

/// The encoder's refusal for a bare name with more than one meaning.
fn refused_constant_name(name: &str) -> PureExpr {
    PureExpr::LogicFnCall {
        name: logic_fn_unresolved_marker(&format!("ambiguous_constant_{name}")),
        args: Vec::new(),
    }
}

/// Bare constant name -> the value every clause spelling it is given.
///
/// A local constant item's value stands in for its bare name only when that
/// name has no other meaning in the crate; a name with several is mapped to a
/// refusal, so a clause spelling it is refused rather than read as one of
/// them. Generic associated constants are keyed by their qualified spellings.
pub(super) fn const_item_substitutions(tcx: TyCtxt<'_>) -> HashMap<String, PureExpr> {
    let ambiguous = ambiguous_constant_names(tcx);
    let mut map = HashMap::new();
    for local_def_id in tcx.hir_body_owners() {
        let def_id = local_def_id.to_def_id();
        if !matches!(
            tcx.def_kind(def_id),
            DefKind::Const { .. } | DefKind::AssocConst { .. }
        ) {
            continue;
        }
        let Some(name) = tcx.opt_item_name(def_id).map(|name| name.to_string()) else {
            continue;
        };
        if ambiguous.contains(&name) {
            continue;
        }
        if let Some(expr) = crate::mir_analysis::translate::resolve_const_item_value(tcx, def_id) {
            map.insert(name, expr);
        }
    }
    // Generic associated constant definitions: <SelfType as Trait>::CONST (#2550)
    map.extend(crate::mir_analysis::extract::collect_generic_assoc_const_definitions(tcx));
    // Last, so that no other spelling of the table can stand in for a refusal.
    for name in ambiguous {
        let refused = refused_constant_name(&name);
        map.insert(name, refused);
    }
    map
}

/// The entries of a table from `const_item_substitutions` that refuse a name.
pub(super) fn refusals_only(table: &HashMap<String, PureExpr>) -> HashMap<String, PureExpr> {
    table
        .iter()
        .filter(|(_, value)| {
            matches!(value, PureExpr::LogicFnCall { name, .. } if is_refused_logic_fn_marker(name))
        })
        .map(|(name, value)| (name.clone(), value.clone()))
        .collect()
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use trust_wp_core::{formula::PureExpr, logic::identity::is_refused_logic_fn_marker};

    use super::{refusals_only, refused_constant_name};

    #[test]
    fn an_ambiguous_name_becomes_a_call_the_encoder_refuses() {
        match refused_constant_name("K") {
            PureExpr::LogicFnCall { name, args } => {
                assert!(is_refused_logic_fn_marker(&name), "{name}");
                assert!(args.is_empty());
            }
            other => panic!("expected a refused call, got {other:?}"),
        }
    }

    /// An import declared in a block gives its name a meaning the module
    /// children do not list: a single import and a glob each make a root
    /// constant of that name ambiguous, and a glob re-importing the one
    /// constant a name has adds no second meaning.
    #[test]
    fn an_import_declared_in_a_block_is_a_meaning() {
        const SOURCE: &str = r#"
pub const K: u8 = 10;
pub const MAX: u8 = 7;
pub const N: u8 = 3;
pub mod other {
    pub const L: u8 = 2;
}
pub fn single() -> u8 {
    use core::u8::MAX as K;
    K
}
pub fn globs() -> u8 {
    use core::u8::*;
    use crate::other::*;
    0
}
"#;
        crate::logic::identity_test_support::probe("tw_const_block_imports", SOURCE, |tcx| {
            let ambiguous = super::ambiguous_constant_names(tcx);
            assert!(ambiguous.contains("K"), "{ambiguous:?}");
            assert!(ambiguous.contains("MAX"), "{ambiguous:?}");
            assert!(!ambiguous.contains("N"), "{ambiguous:?}");
            assert!(!ambiguous.contains("L"), "{ambiguous:?}");
        });
    }

    #[test]
    fn only_refusals_reach_the_logic_pass() {
        let table: HashMap<String, PureExpr> = [
            ("K".to_string(), refused_constant_name("K")),
            ("M".to_string(), PureExpr::Int(3)),
        ]
        .into_iter()
        .collect();
        let refusals = refusals_only(&table);
        assert_eq!(refusals.len(), 1);
        assert!(refusals.contains_key("K"));
    }
}
