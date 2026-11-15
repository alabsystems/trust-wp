// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! How a written call's SPELLING decides what it may resolve to: a bare name
//! is a value-namespace binding, never a method; a trait path names that
//! trait's method; a module path names that module's function. Each test is a
//! real compilation and a direct call of the resolver.

use std::sync::Arc;

use trust_wp_core::{formula::PureExpr, logic::identity::logic_fn_unresolved_marker};

use super::{
    resolve_logic_fn_paths_in_scope, visible_generic_type_param, ClausePosition, GenericTypeParam,
};
use crate::logic::{
    identity_test_support::{def_id_of, families_for, member, probe},
    spec_calls::ClauseRef,
};

const SOURCE: &str = r#"
#[derive(Clone, Copy)]
pub struct S;

impl S {
    #[doc = "trust-wp:logic:"]
    pub fn m(self) -> i64 { 0 }
}

pub trait Tr1: Sized {
    #[doc = "trust-wp:logic:"]
    fn m(self) -> i64 { 10 }
}
impl Tr1 for S {}

pub trait Tr2 {
    #[doc = "trust-wp:logic:"]
    fn m(self) -> i64;
}
impl Tr2 for S {
    #[doc = "trust-wp:logic:"]
    fn m(self) -> i64 { 5 }
}

pub fn m(_x: S) -> i64 { 0 }

pub mod other {
    pub fn m(_x: super::S) -> i64 { 0 }
}

pub fn owner(s: S) -> i64 { 0 }

#[derive(Clone, Copy)]
pub struct R;
impl R {
    #[doc = "trust-wp:logic:"]
    pub fn m(self) -> i64 { 0 }
}
impl Tr1 for R {}

pub fn owner_r(r: R) -> i64 { 0 }

pub fn shadowed<W>() -> i64 {
    struct W;
    0
}

pub fn outer_block() -> i64 {
    struct W;
    fn inner<W>() -> i64 { 0 }
    0
}

pub fn nested_block<W>() -> i64 {
    {
        struct W;
    }
    0
}
"#;

fn call(name: &str) -> PureExpr {
    PureExpr::LogicFnCall {
        name: name.to_string(),
        args: vec![PureExpr::Var("s".to_string(), None)],
    }
}

fn resolved_name(expr: &PureExpr) -> String {
    match expr {
        PureExpr::LogicFnCall { name, .. } => name.clone(),
        other => format!("{other:?}"),
    }
}

/// `m(s)` is the root's program function whatever methods named `m` exist,
/// and `other::m(s)` is `other`'s: neither may be read as a logic method, nor
/// left for the encoder to dispatch on `s`'s sort.
#[test]
fn a_bare_or_module_path_call_of_a_family_of_methods_is_refused() {
    probe("tw_spelling_bare", SOURCE, |tcx| {
        let _ = families_for(tcx, "tw_spelling_bare", "m");
        let owner = def_id_of(tcx, "owner");
        // Each refused call is a symbol of its own (D-164), spelled with the
        // name's refusal marker as its prefix.
        let refused = logic_fn_unresolved_marker("m");
        for written in ["m", "other::m"] {
            let resolved = resolve_logic_fn_paths_in_scope(
                tcx,
                owner,
                &call(written),
                ClausePosition::Signature,
                &ClauseRef::HandLookupUnderTest,
            );
            assert!(
                resolved_name(&resolved).starts_with(&refused),
                "`{written}(s)`: {}",
                resolved_name(&resolved)
            );
        }
    });
}

/// `Tr1::m(s)` and `<S as Tr1>::m(s)` are Tr1's default body at `S` (its impl
/// overrides nothing), however many other `m`s `S` has; `Tr2::m(s)` is Tr2's
/// impl for `S`.
#[test]
fn a_trait_path_names_its_own_trait_s_method() {
    probe("tw_spelling_trait_path", SOURCE, |tcx| {
        let family = families_for(tcx, "tw_spelling_trait_path", "m");
        let tr1_default = member(&family, "Tr1::m").id.clone();
        let tr2_impl = member(&family, "<S as Tr2>::m").id.clone();
        let owner = def_id_of(tcx, "owner");
        let at = |written: &str| {
            resolved_name(&resolve_logic_fn_paths_in_scope(
                tcx,
                owner,
                &call(written),
                ClausePosition::Signature,
                &ClauseRef::HandLookupUnderTest,
            ))
        };
        assert_eq!(at("Tr1::m"), tr1_default);
        assert_eq!(at("<S as Tr1>::m"), tr1_default);
        assert_eq!(at("Tr2::m"), tr2_impl);
    });
}

/// Method syntax `r.m()` where `R` has an inherent `m` and Tr1's default
/// body also runs at `R`: Rust's lookup takes the inherent method at `R`
/// itself, but the receiver lookup counts the default as a candidate beside
/// it (D-161) and refuses rather than ranks them (D-208's price).
#[test]
fn method_syntax_beside_a_trait_default_that_runs_is_refused() {
    probe("tw_spelling_method", SOURCE, |tcx| {
        let family = families_for(tcx, "tw_spelling_method", "m");
        let inherent = member(&family, "::R::m").id.clone();
        let owner = def_id_of(tcx, "owner_r");
        let expr = PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("r".to_string(), None)),
            method: "m".to_string(),
            args: Vec::new(),
        };
        let resolved = resolve_logic_fn_paths_in_scope(
            tcx,
            owner,
            &expr,
            ClausePosition::Signature,
            &ClauseRef::HandLookupUnderTest,
        );
        let name = resolved_name(&resolved);
        assert_ne!(name, inherent);
        assert!(
            !name.starts_with(trust_wp_core::logic::identity::LOGIC_FN_ID_PREFIX),
            "no definition is chosen: {name}"
        );
    });
}

/// A body's items shadow its item's generic parameters (the clause stands at
/// the top of the body); a block AROUND the item does not, the item's
/// generics being closer to its clause; a nested block of the body may hold
/// the clause or not, which the text does not say.
#[test]
fn a_body_item_shadows_a_generic_parameter_and_an_outer_block_does_not() {
    probe("tw_spelling_generic_shadow", SOURCE, |tcx| {
        let _ = families_for(tcx, "tw_spelling_generic_shadow", "m");
        let shadowed = def_id_of(tcx, "shadowed");
        assert_eq!(
            visible_generic_type_param(tcx, shadowed, "W", ClausePosition::Signature),
            GenericTypeParam::NotParam,
            "`struct W` in `shadowed`'s body is the `W` its clause names"
        );
        let inner = def_id_of(tcx, "outer_block::inner");
        assert_eq!(
            visible_generic_type_param(tcx, inner, "W", ClausePosition::Signature),
            GenericTypeParam::Visible(0),
            "`inner`'s own parameter is closer than `outer_block`'s struct"
        );
        let nested = def_id_of(tcx, "nested_block");
        assert_eq!(
            visible_generic_type_param(tcx, nested, "W", ClausePosition::Signature),
            GenericTypeParam::Refused,
            "a struct in a nested block of the body is neither read nor ruled out"
        );
        assert_eq!(
            visible_generic_type_param(tcx, nested, "V", ClausePosition::Signature),
            GenericTypeParam::NotParam,
        );
    });
}
