// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Which discriminant value says a list is `Nil`, for the match-exit lanes
//! (`synthesize_post_loop_match_exit_goals`, `synthesize_nested_match_exit_facts`).
//!
//! Those lanes read a loop's exit fact `discriminant(l) != K` as "`l` is
//! `Nil`", and from it every `l.get(i)` as `None`. That holds only when `K` is
//! the discriminant of `Cons` in the enum `get` matches on, the enum has no
//! other variant, and `discriminant` is the MIR discriminant read and not a
//! logic function of that name. The lanes once took `K == 1` on faith; with
//! `enum L { Cons(..), Nil }` the exit fact `discriminant(l) != 1` says `l`
//! IS a `Cons` (D-237). The enum is read here instead, and a `get` whose
//! enum cannot be found is no premise.

use rustc_hir::def::DefKind;
use rustc_middle::ty::TyCtxt;
use trust_wp_core::{
    formula::{resolve_sort_name, ExprSort},
    logic::LogicFnDef,
};

/// The discriminant value of `Cons` in the two-variant `Cons`/`Nil` enum of
/// the current crate that `get`'s first parameter has, or `None` when that
/// enum cannot be named exactly.
pub(super) fn cons_discriminant_of(tcx: TyCtxt<'_>, get: &LogicFnDef) -> Option<i64> {
    let mut sort = get.param_sorts().first()?.as_ref()?;
    while let ExprSort::Ref(inner) | ExprSort::MutRef(inner) = sort {
        sort = inner;
    }
    let ExprSort::Datatype(id) = sort else {
        return None;
    };
    let name = resolve_sort_name(*id);
    let mut enums = tcx
        .hir_crate_items(())
        .definitions()
        .filter(|def_id| tcx.def_kind(*def_id) == DefKind::Enum)
        .filter(|def_id| tcx.def_path_str(def_id.to_def_id()) == name);
    let enum_def_id = enums.next()?;
    if enums.next().is_some() {
        return None;
    }
    let adt = tcx.adt_def(enum_def_id);
    if adt.variants().len() != 2 {
        return None;
    }
    let mut cons = None;
    let mut saw_nil = false;
    for (index, discr) in adt.discriminants(tcx) {
        match adt.variant(index).name.as_str() {
            "Cons" => cons = i64::try_from(discr.val).ok(),
            "Nil" => saw_nil = true,
            _ => return None,
        }
    }
    cons.filter(|_| saw_nil)
}

/// The value `K` for which `discriminant(l) != K` says that the receiver `l`
/// of the logic function `method` is `Nil`: the one definition named
/// `method` that `is_list_get` accepts, read through `cons_discriminant`.
/// `None` when no single such definition exists, or when a logic function is
/// itself named `discriminant` (its calls are spelled as the MIR read is).
pub(super) fn list_exit_discriminant(
    logic_fns: &[LogicFnDef],
    method: &str,
    is_list_get: impl Fn(&LogicFnDef) -> bool,
    cons_discriminant: &dyn Fn(&LogicFnDef) -> Option<i64>,
) -> Option<i64> {
    if logic_fns.iter().any(|def| {
        def.name() == "discriminant" || def.full_path().rsplit("::").next() == Some("discriminant")
    }) {
        return None;
    }
    let mut named = logic_fns.iter().filter(|def| def.name() == method);
    let def = named.next()?;
    if named.next().is_some() || !is_list_get(def) {
        return None;
    }
    cons_discriminant(def)
}

#[cfg(test)]
mod tests {
    use trust_wp_core::formula::PureExpr;

    use super::*;

    fn def(name: &str) -> LogicFnDef {
        LogicFnDef::new(
            name.to_string(),
            format!("crate::{name}"),
            vec!["self".to_string()],
            PureExpr::Bool(true),
        )
    }

    #[test]
    fn the_cons_value_is_the_enums_not_one() {
        let fns = [def("get")];
        assert_eq!(
            list_exit_discriminant(&fns, "get", |_| true, &|_| Some(0)),
            Some(0)
        );
        assert_eq!(
            list_exit_discriminant(&fns, "get", |_| true, &|_| None),
            None
        );
    }

    #[test]
    fn a_logic_fn_named_discriminant_closes_the_lane() {
        let fns = [def("get"), def("discriminant")];
        assert_eq!(
            list_exit_discriminant(&fns, "get", |_| true, &|_| Some(1)),
            None
        );
    }

    #[test]
    fn two_definitions_of_get_close_the_lane() {
        let fns = [def("get"), def("get")];
        assert_eq!(
            list_exit_discriminant(&fns, "get", |_| true, &|_| Some(1)),
            None
        );
        assert_eq!(
            list_exit_discriminant(&[def("get")], "get", |_| false, &|_| Some(1)),
            None
        );
    }
}
