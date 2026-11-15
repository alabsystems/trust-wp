// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for `block_scope::lookup`: each pins one rule of rustc's
//! block-scope resolution the lookup answers exactly, or one place it must
//! refuse, against a real compilation.

use rustc_hir::def::{DefKind, Namespace};
use rustc_middle::ty::TyCtxt;
use trust_wp_core::formula::PureExpr;

use super::{lookup, BlockBinding, ClausePosition};
use crate::logic::{
    identity::resolve_logic_fn_paths_in_scope,
    identity_test_support::{def_id_of, families_for, probe},
    spec_calls::ClauseRef,
};

const SOURCE: &str = r#"
pub fn k() -> i64 { 10 }

pub mod other {
    pub fn k() -> i64 { 0 }
    pub fn zero() -> i64 { 0 }
    fn hidden() -> i64 { 0 }
}

pub fn shadowing_host() -> i64 {
    fn k() -> i64 { 0 }
    fn in_block() -> i64 { 0 }
    mod walled {
        pub fn in_module() -> i64 { 0 }
    }
    fn mid() -> i64 {
        fn two_out() -> i64 { 0 }
        two_out()
    }
    in_block() + walled::in_module() + mid()
}

pub fn import_host() -> i64 {
    use crate::other::zero as k;
    fn via_rename() -> i64 { 0 }
    via_rename() + k()
}

pub fn glob_host() -> i64 {
    #[allow(unused_imports)]
    use crate::other::*;
    fn via_glob() -> i64 { 0 }
    via_glob()
}

pub fn hidden_glob_host() -> i64 {
    #[allow(unused_imports)]
    use crate::other::*;
    fn sees_hidden() -> i64 { 0 }
    sees_hidden()
}

pub fn own_body() -> i64 {
    fn k() -> i64 { 0 }
    k()
}

pub fn nested_body() -> i64 {
    {
        fn k() -> i64 { 0 }
        k()
    }
}

pub fn closure_host() -> i64 {
    let k = || 0i64;
    let c = || 1i64;
    k() + c()
}

pub fn local_host() -> i64 {
    let k = 3i64;
    k
}
"#;

fn at(
    tcx: TyCtxt<'_>,
    owner_suffix: &str,
    name: &str,
    ns: Namespace,
    position: ClausePosition,
) -> BlockBinding {
    let owner = def_id_of(tcx, owner_suffix).expect_local();
    lookup(tcx, owner, name, ns, position)
}

fn def_path(tcx: TyCtxt<'_>, binding: BlockBinding) -> String {
    match binding {
        BlockBinding::Def(_, def_id) => tcx.def_path_str(def_id),
        other => format!("{other:?}"),
    }
}

/// An item of the block that encloses the owner shadows the module's item of
/// that name, and a module declared in the block walls its own items off
/// from the block.
#[test]
fn a_block_item_shadows_the_module_and_a_module_is_a_barrier() {
    probe("tw_block_scope_shadow", SOURCE, |tcx| {
        let binding = at(
            tcx,
            "shadowing_host::in_block",
            "k",
            Namespace::ValueNS,
            ClausePosition::Signature,
        );
        assert!(matches!(binding, BlockBinding::Def(DefKind::Fn, _)));
        assert_eq!(def_path(tcx, binding), "shadowing_host::k");
        assert_eq!(
            at(
                tcx,
                "walled::in_module",
                "k",
                Namespace::ValueNS,
                ClausePosition::Signature
            ),
            BlockBinding::Unbound,
            "`walled` is a module: `k` is looked up in it, not in the block around it"
        );
        assert_eq!(
            def_path(
                tcx,
                at(
                    tcx,
                    "mid::two_out",
                    "k",
                    Namespace::ValueNS,
                    ClausePosition::Signature
                )
            ),
            "shadowing_host::k",
            "an item sees the blocks of every body that encloses it"
        );
        assert_eq!(
            def_path(
                tcx,
                at(
                    tcx,
                    "shadowing_host::in_block",
                    "walled",
                    Namespace::TypeNS,
                    ClausePosition::Signature
                )
            ),
            "shadowing_host::walled",
            "a path's first segment is looked up in the type namespace of the block"
        );
    });
}

/// A renamed import binds its new name to the imported definition; a glob
/// brings what the module exports to the block, and nothing it keeps private.
#[test]
fn imports_bind_what_rustc_binds() {
    probe("tw_block_scope_imports", SOURCE, |tcx| {
        assert_eq!(
            def_path(
                tcx,
                at(
                    tcx,
                    "via_rename",
                    "k",
                    Namespace::ValueNS,
                    ClausePosition::Signature
                )
            ),
            "other::zero"
        );
        assert_eq!(
            def_path(
                tcx,
                at(
                    tcx,
                    "via_glob",
                    "k",
                    Namespace::ValueNS,
                    ClausePosition::Signature
                )
            ),
            "other::k"
        );
        assert_eq!(
            at(
                tcx,
                "sees_hidden",
                "hidden",
                Namespace::ValueNS,
                ClausePosition::Signature
            ),
            BlockBinding::Unbound,
            "a private item is not brought by a glob outside its module"
        );
    });
}

/// A function's `requires`/`ensures` stand at the top of its body: an item of
/// that top-level block answers. The same name in a nested block is visible
/// to some positions of a loop clause and not others, so it refuses.
#[test]
fn the_owner_body_answers_only_from_its_top_level_block() {
    probe("tw_block_scope_own_body", SOURCE, |tcx| {
        assert_eq!(
            def_path(
                tcx,
                at(
                    tcx,
                    "own_body",
                    "k",
                    Namespace::ValueNS,
                    ClausePosition::Signature
                )
            ),
            "own_body::k"
        );
        assert_eq!(
            at(
                tcx,
                "nested_body",
                "k",
                Namespace::ValueNS,
                ClausePosition::Signature
            ),
            BlockBinding::Refused
        );
    });
}

/// A local shadows every item where it is in scope. It is in scope of a
/// closure's clauses and of a clause inside the body; it is never in scope of
/// a function's own `requires`/`ensures`.
#[test]
fn a_local_refuses_only_where_it_can_be_in_scope() {
    probe("tw_block_scope_locals", SOURCE, |tcx| {
        let closure = tcx
            .iter_local_def_id()
            .filter(|def_id| tcx.def_kind(*def_id) == DefKind::Closure)
            .find(|def_id| {
                tcx.def_path_str(def_id.to_def_id())
                    .starts_with("closure_host")
            })
            .expect("closure_host has a closure");
        assert_eq!(
            lookup(
                tcx,
                closure,
                "k",
                Namespace::ValueNS,
                ClausePosition::Signature
            ),
            BlockBinding::Refused,
            "`let k` in the enclosing body shadows the root's `k` for a closure's contract"
        );
        assert_eq!(
            at(
                tcx,
                "local_host",
                "k",
                Namespace::ValueNS,
                ClausePosition::Body
            ),
            BlockBinding::Refused,
            "a loop clause or assertion of `local_host` may stand after `let k`"
        );
        assert_eq!(
            at(
                tcx,
                "local_host",
                "k",
                Namespace::ValueNS,
                ClausePosition::Signature
            ),
            BlockBinding::Unbound,
            "`requires`/`ensures` stand before every local of the body"
        );
        assert_eq!(
            at(
                tcx,
                "local_host",
                "k",
                Namespace::TypeNS,
                ClausePosition::Body
            ),
            BlockBinding::Unbound,
            "a local is a value: it never shadows a path's first segment"
        );
    });
}

/// Two logic functions declared in different blocks of one body print the
/// same path (`host::k`), and every identity table is keyed by that path.
const DUPLICATED: &str = r#"
pub fn host() -> i64 {
    {
        #[doc = "trust-wp:logic:"]
        fn k() -> i64 { 10 }
    }
    {
        #[doc = "trust-wp:logic:"]
        fn k() -> i64 { 0 }
        #[doc = "trust-wp:logic:"]
        fn j() -> i64 { 5 }
        fn user() -> i64 { 0 }
        user()
    }
}
"#;

fn resolved_call(tcx: TyCtxt<'_>, owner_suffix: &str, name: &str) -> String {
    let call = PureExpr::LogicFnCall {
        name: name.to_string(),
        args: Vec::new(),
    };
    match resolve_logic_fn_paths_in_scope(
        tcx,
        def_id_of(tcx, owner_suffix),
        &call,
        ClausePosition::Signature,
        &ClauseRef::HandLookupUnderTest,
    ) {
        PureExpr::LogicFnCall { name, .. } => name,
        other => panic!("a call stays a call: {other:?}"),
    }
}

/// The block lookup finds the second block's `k` exactly, and the id it
/// would map to stands for either definition: the call stays unresolved. The
/// block's `j` is alone on its path, but `host`'s body declares it, and D-174's
/// withholding answers before the block lookup (D-213): it stays unresolved too.
#[test]
fn a_path_two_block_items_share_resolves_to_neither() {
    probe("tw_block_scope_dup_path", DUPLICATED, |tcx| {
        let family = families_for(tcx, "tw_block_scope_dup_path", "k");
        assert_eq!(family.len(), 2);
        assert_eq!(resolved_call(tcx, "host::user", "k"), "k");
        assert_eq!(families_for(tcx, "tw_block_scope_dup_path", "j").len(), 1);
        assert_eq!(resolved_call(tcx, "host::user", "j"), "j");
    });
}
