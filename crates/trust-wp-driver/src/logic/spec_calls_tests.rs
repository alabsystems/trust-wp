// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for reading a specification's calls as rustc resolved them.
//!
//! Each probe crate writes the call inside a closure, as the type-check
//! vehicle does, and the test asks whether rustc's resolution of that closure
//! confirms a reading. The shapes are the ones the hand lookup misread: a
//! by-value blanket impl ahead of a bound's by-reference method, a user
//! `Deref` level, a path through a named trait. Pairing a clause with its
//! body (`paired_bodies`) needs the macros' marker and tag, so it is pinned
//! by the adversarial corpus, not here.

use rustc_hir::{
    def::DefKind,
    def_id::{DefId, LocalDefId},
};
use rustc_middle::ty::{Ty, TyCtxt};

use super::{CallForm, SpecCalls};
use crate::logic::identity_test_support::{def_id_of, first_param_ty, probe};

/// Whether `calls` confirm `chosen` for a method call of `name` with no
/// argument besides its receiver.
fn by_method<'tcx>(
    calls: &SpecCalls<'tcx>,
    tcx: TyCtxt<'tcx>,
    name: &str,
    receiver: Option<Ty<'tcx>>,
    root: Option<&str>,
    chosen: DefId,
) -> bool {
    calls.confirms(tcx, CallForm::Method, name, None, 1, receiver, root, chosen)
}

/// The closures written in the body of the function whose path ends in
/// `function`.
fn closures_in(tcx: TyCtxt<'_>, function: &str) -> Vec<LocalDefId> {
    let owner = def_id_of(tcx, function);
    tcx.iter_local_def_id()
        .filter(|&local| {
            tcx.def_kind(local) == DefKind::Closure
                && tcx.typeck_root_def_id(local.to_def_id()) == owner
        })
        .collect()
}

const BLANKET_OVER_BOUND: &str = r#"
pub trait Other { fn holds(self) -> bool; }
impl<U> Other for U { fn holds(self) -> bool { false } }

pub trait Bound { fn holds(&self) -> bool; }

pub struct S;
impl Bound for S { fn holds(&self) -> bool { true } }

pub fn on_generic<T: Bound>(t: T) -> bool { let _c = move || t.holds(); true }
pub fn on_concrete(s: S) -> bool { let _c = move || s.holds(); true }
"#;

/// `t.holds()` with `T: Bound`: the blanket `Other::holds(self)` is taken by
/// value before `Bound::holds(&self)` is reached by autoref, so the bound's
/// declaration is NOT what the call names, and the blanket method is.
#[test]
fn a_by_value_blanket_impl_is_what_a_generic_receiver_s_call_names() {
    probe("tw_spec_calls_blanket_generic", BLANKET_OVER_BOUND, |tcx| {
        let calls = SpecCalls::of_bodies(tcx, &closures_in(tcx, "on_generic"))
            .expect("the closure has a type-checked form");
        let bound = def_id_of(tcx, "Bound::holds");
        let other = def_id_of(tcx, "Other::holds");
        let ty = first_param_ty(tcx, "on_generic");
        assert!(!by_method(&calls, tcx, "holds", Some(ty), None, bound));
        assert!(by_method(&calls, tcx, "holds", Some(ty), None, other));
        assert_eq!(
            calls.trait_method_resolved(tcx, CallForm::Method, "holds", None, 1, Some(ty), None),
            Some(other)
        );
    });
}

/// The same at a concrete receiver: the call is the blanket impl's item, not
/// the bound trait's impl for `S`.
#[test]
fn a_by_value_blanket_impl_is_what_a_concrete_receiver_s_call_names() {
    probe(
        "tw_spec_calls_blanket_concrete",
        BLANKET_OVER_BOUND,
        |tcx| {
            let calls = SpecCalls::of_bodies(tcx, &closures_in(tcx, "on_concrete"))
                .expect("the closure has a type-checked form");
            let bound_impl = def_id_of(tcx, "<S as Bound>::holds");
            let blanket_impl = def_id_of(tcx, "<U as Other>::holds");
            assert!(!by_method(&calls, tcx, "holds", None, None, bound_impl));
            assert!(by_method(&calls, tcx, "holds", None, None, blanket_impl));
        },
    );
}

const PLAIN: &str = r#"
pub trait Plain { fn check(&self) -> bool; }
pub trait WithDefault { fn dflt(&self) -> bool { true } }

pub struct S;
impl Plain for S { fn check(&self) -> bool { true } }
impl WithDefault for S {}

pub fn on_generic<T: Plain>(t: T) -> bool { let _c = move || t.check(); true }
pub fn on_concrete(s: S) -> bool { let _c = move || s.check(); true }
pub fn on_default(s: S) -> bool { let _c = move || s.dflt(); true }
pub fn by_path(s: S) -> bool { let _c = move || Plain::check(&s); true }
pub fn two_receivers<T: Plain>(s: S, t: T) -> bool {
    let _c = move || s.check() && t.check();
    true
}
"#;

/// A generic receiver's call is the declaration of its bound, and only it.
#[test]
fn a_bound_method_at_a_generic_receiver_is_its_declaration() {
    probe("tw_spec_calls_plain_generic", PLAIN, |tcx| {
        let calls = SpecCalls::of_bodies(tcx, &closures_in(tcx, "on_generic"))
            .expect("the closure has a type-checked form");
        let decl = def_id_of(tcx, "Plain::check");
        let impl_item = def_id_of(tcx, "<S as Plain>::check");
        assert!(by_method(&calls, tcx, "check", None, None, decl));
        assert!(!by_method(&calls, tcx, "check", None, None, impl_item));
    });
}

/// A concrete receiver's call is the impl item that runs, never the
/// declaration; where the impl inherits a default, the default is.
#[test]
fn a_concrete_receiver_s_call_is_the_item_that_runs() {
    probe("tw_spec_calls_plain_concrete", PLAIN, |tcx| {
        let decl = def_id_of(tcx, "Plain::check");
        let impl_item = def_id_of(tcx, "<S as Plain>::check");
        let calls = SpecCalls::of_bodies(tcx, &closures_in(tcx, "on_concrete"))
            .expect("the closure has a type-checked form");
        assert!(by_method(&calls, tcx, "check", None, None, impl_item));
        assert!(!by_method(&calls, tcx, "check", None, None, decl));
        let defaulted = SpecCalls::of_bodies(tcx, &closures_in(tcx, "on_default"))
            .expect("the closure has a type-checked form");
        let default = def_id_of(tcx, "WithDefault::dflt");
        assert!(by_method(&defaulted, tcx, "dflt", None, None, default));
    });
}

/// A path call is confirmed only as a path call, and a method-call reading
/// finds no counterpart in it.
#[test]
fn a_path_call_is_read_only_as_a_path_call() {
    probe("tw_spec_calls_plain_path", PLAIN, |tcx| {
        let calls = SpecCalls::of_bodies(tcx, &closures_in(tcx, "by_path"))
            .expect("the closure has a type-checked form");
        let impl_item = def_id_of(tcx, "<S as Plain>::check");
        assert!(calls.confirms(
            tcx,
            CallForm::Path,
            "check",
            Some("Plain::check"),
            1,
            None,
            None,
            impl_item
        ));
        assert!(!by_method(&calls, tcx, "check", None, None, impl_item));
        assert!(calls.holds(CallForm::Path, "check", 1));
    });
}

/// Calls of one name on receivers of different types are told apart by the
/// receiver's type; with no type to tell them by, they must all agree.
#[test]
fn a_receiver_s_type_selects_its_own_calls() {
    probe("tw_spec_calls_plain_two", PLAIN, |tcx| {
        let calls = SpecCalls::of_bodies(tcx, &closures_in(tcx, "two_receivers"))
            .expect("the closure has a type-checked form");
        let decl = def_id_of(tcx, "Plain::check");
        let impl_item = def_id_of(tcx, "<S as Plain>::check");
        let owner = def_id_of(tcx, "two_receivers");
        let sig = tcx.fn_sig(owner).instantiate_identity().skip_binder();
        let (s_ty, t_ty) = (sig.inputs()[0], sig.inputs()[1]);
        assert!(by_method(&calls, tcx, "check", Some(s_ty), None, impl_item));
        assert!(by_method(&calls, tcx, "check", Some(t_ty), None, decl));
        assert!(!by_method(&calls, tcx, "check", None, None, decl));
        assert!(!by_method(&calls, tcx, "check", None, None, impl_item));
    });
}

const USER_DEREF: &str = r#"
pub trait Tr { fn holds(self) -> bool; }

#[derive(Clone, Copy)]
pub struct S;
impl Tr for S { fn holds(self) -> bool { false } }

pub struct W(pub S);
impl std::ops::Deref for W {
    type Target = S;
    fn deref(&self) -> &S { &self.0 }
}

pub mod other {
    pub trait Other { fn holds(self) -> bool; }
    impl Other for super::W { fn holds(self) -> bool { true } }
}

pub fn through_deref(w: W) -> bool { let _c = move || w.holds(); true }
"#;

/// `other::Other` is not in scope, so `w.holds()` derefs through `W` and is
/// `<S as Tr>::holds`; the one candidate at `W` itself is not the call.
#[test]
fn a_trait_out_of_scope_is_passed_by_for_a_deref_level() {
    probe("tw_spec_calls_user_deref", USER_DEREF, |tcx| {
        let calls = SpecCalls::of_bodies(tcx, &closures_in(tcx, "through_deref"))
            .expect("the closure has a type-checked form");
        let at_w = def_id_of(tcx, "<W as other::Other>::holds");
        let at_s = def_id_of(tcx, "<S as Tr>::holds");
        assert!(!by_method(&calls, tcx, "holds", None, None, at_w));
        assert!(by_method(&calls, tcx, "holds", None, None, at_s));
    });
}

const SHADOWED: &str = r#"
pub struct A;
pub struct B;
impl A { pub fn holds(self) -> bool { true } }
impl B { pub fn holds(self) -> bool { false } }

pub fn shadowed(x: A, y: A) -> bool {
    let x = B;
    let _c = move || x.holds() && y.holds();
    true
}
"#;

/// A body binding shadows the parameter `x` where the clause is written, so
/// rustc types the clause's `x` as `B`. Read by type alone, the lookup's `A`
/// finds `y.holds()` and confirms `A::holds` for `x.holds()`; rooted at `x`,
/// rustc's typing of `x` is not the lookup's and nothing is confirmed.
#[test]
fn a_receiver_is_read_at_the_variable_the_lookup_typed() {
    probe("tw_spec_calls_shadowed", SHADOWED, |tcx| {
        let calls = SpecCalls::of_bodies(tcx, &closures_in(tcx, "shadowed"))
            .expect("the closure has a type-checked form");
        let a_holds = def_id_of(tcx, "A::holds");
        let b_holds = def_id_of(tcx, "B::holds");
        let a_ty = first_param_ty(tcx, "shadowed");
        assert!(!by_method(
            &calls,
            tcx,
            "holds",
            Some(a_ty),
            Some("x"),
            a_holds
        ));
        assert!(!by_method(
            &calls,
            tcx,
            "holds",
            Some(a_ty),
            Some("x"),
            b_holds
        ));
        assert!(by_method(
            &calls,
            tcx,
            "holds",
            Some(a_ty),
            Some("y"),
            a_holds
        ));
        assert!(
            by_method(&calls, tcx, "holds", Some(a_ty), None, a_holds),
            "by type alone `y.holds()` stands in for `x.holds()`: the reading the root rules out"
        );
    });
}

const QUALIFIED: &str = r#"
pub trait Tr { fn m(x: u32) -> u32; }
pub trait Other { fn m(x: u32) -> u32; }
pub struct S;
pub struct U;
impl Tr for S { fn m(x: u32) -> u32 { x + 1 } }
impl Tr for U { fn m(x: u32) -> u32 { x } }
impl Other for S { fn m(x: u32) -> u32 { x + 2 } }

pub fn qualified(x: u32) -> bool {
    let _c = move || <S as Tr>::m(x) == <U as Tr>::m(x);
    true
}
pub fn two_traits(x: u32) -> bool {
    let _c = move || <S as Tr>::m(x) == <S as Other>::m(x);
    true
}
"#;

/// A path call's qualifier decides what it names, and its first argument
/// does not: `<S as Tr>::m(x)` and `<U as Tr>::m(x)` share a name, an arity
/// and an argument, and each is confirmed by its own call only. Pooled by
/// the argument, neither is confirmed, and the two refusals are one symbol.
#[test]
fn a_path_call_is_read_at_its_own_qualifier() {
    probe("tw_spec_calls_qualified", QUALIFIED, |tcx| {
        let path = CallForm::Path;
        let calls = SpecCalls::of_bodies(tcx, &closures_in(tcx, "qualified"))
            .expect("the closure has a type-checked form");
        let at_s = def_id_of(tcx, "<S as Tr>::m");
        let at_u = def_id_of(tcx, "<U as Tr>::m");
        assert!(calls.confirms(tcx, path, "m", Some("<S as Tr>::m"), 1, None, None, at_s));
        assert!(calls.confirms(tcx, path, "m", Some("<U as Tr>::m"), 1, None, None, at_u));
        assert!(calls.confirms(tcx, path, "m", Some("< S  as Tr >::m"), 1, None, None, at_s));
        assert!(!calls.confirms(tcx, path, "m", Some("<S as Tr>::m"), 1, None, None, at_u));
        assert!(!calls.confirms(
            tcx,
            path,
            "m",
            Some("<crate::S as Tr>::m"),
            1,
            None,
            None,
            at_s
        ));
        assert!(!calls.confirms(tcx, path, "m", None, 1, None, None, at_s));
        let traits = SpecCalls::of_bodies(tcx, &closures_in(tcx, "two_traits"))
            .expect("the closure has a type-checked form");
        let other = def_id_of(tcx, "<S as Other>::m");
        assert!(traits.confirms(
            tcx,
            path,
            "m",
            Some("<S as Other>::m"),
            1,
            None,
            None,
            other
        ));
        assert!(!traits.confirms(tcx, path, "m", Some("<S as Other>::m"), 1, None, None, at_s));
    });
}

/// A path's spelling is its tokens: spacing is not part of it, and a token
/// boundary is.
#[test]
fn a_path_is_compared_by_its_tokens() {
    assert_eq!(
        super::path_tokens("<S as Tr>::m"),
        super::path_tokens("< S  as\tTr >:: m")
    );
    assert_ne!(
        super::path_tokens("<S as Tr>::m"),
        super::path_tokens("<Sas Tr>::m")
    );
    assert_ne!(super::path_tokens("a::b::m"), super::path_tokens("a::bm"));
}

/// No body, no reading.
#[test]
fn no_body_is_no_reading() {
    probe("tw_spec_calls_none", PLAIN, |tcx| {
        assert!(SpecCalls::of_bodies(tcx, &[]).is_none());
    });
}

const UNIT_VALUE: &str = r#"
pub struct A;
pub struct B;
impl A { pub fn holds(self) -> bool { true } }
impl B { pub fn holds(self) -> bool { false } }
pub mod m {
    pub struct C;
    impl C { pub fn holds(self) -> bool { true } }
}

pub fn ty_a(_a: A) {}
pub fn ty_b(_b: B) {}
pub fn ty_c(_c: m::C) {}

pub fn bare(_x: B) -> bool { let _c = move || A.holds(); true }
pub fn qualified(_x: B) -> bool { let _c = move || m::C.holds(); true }
"#;

/// A bare name that rustc resolves to a unit struct's constructor roots its
/// calls as the lookup does (`identity::unit_struct_value_type` types the
/// same name as that struct), so `A.holds()` is confirmed at the root `A`
/// and only as `A`'s own method, and only where the lookup typed `A` as
/// rustc did. A qualified `m::C` is not a bare name and roots nothing. (No
/// binding can shadow a unit struct in scope: Rust reads `let A = ..` as a
/// pattern of the struct.)
#[test]
fn a_unit_struct_value_is_a_receiver_root_of_its_bare_name() {
    probe("tw_spec_calls_unit_value", UNIT_VALUE, |tcx| {
        let a_holds = def_id_of(tcx, "A::holds");
        let b_holds = def_id_of(tcx, "B::holds");
        let c_holds = def_id_of(tcx, "C::holds");
        let a_ty = first_param_ty(tcx, "ty_a");
        let b_ty = first_param_ty(tcx, "ty_b");
        let c_ty = first_param_ty(tcx, "ty_c");

        let bare = SpecCalls::of_bodies(tcx, &closures_in(tcx, "bare"))
            .expect("the closure has a type-checked form");
        assert!(by_method(
            &bare,
            tcx,
            "holds",
            Some(a_ty),
            Some("A"),
            a_holds
        ));
        assert!(!by_method(
            &bare,
            tcx,
            "holds",
            Some(a_ty),
            Some("A"),
            b_holds
        ));
        assert!(!by_method(
            &bare,
            tcx,
            "holds",
            Some(b_ty),
            Some("A"),
            a_holds
        ));
        assert!(!by_method(
            &bare,
            tcx,
            "holds",
            Some(b_ty),
            Some("A"),
            b_holds
        ));

        let qualified = SpecCalls::of_bodies(tcx, &closures_in(tcx, "qualified"))
            .expect("the closure has a type-checked form");
        assert!(!by_method(
            &qualified,
            tcx,
            "holds",
            Some(c_ty),
            Some("C"),
            c_holds
        ));
        assert!(by_method(
            &qualified,
            tcx,
            "holds",
            Some(c_ty),
            None,
            c_holds
        ));
    });
}
