// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for `method_lookup::selects_only`: each pins one way Rust's
//! method lookup can select a method other than the pick, or one shape where
//! it cannot, against a real compilation.

use rustc_middle::ty::{Ty, TyCtxt};

use super::{reset, selects_only};
use crate::logic::identity_test_support::{def_id_of, probe};

const SOURCE: &str = r#"
#[derive(Clone, Copy)]
pub struct S;
pub trait Tr1: Sized {
    fn m(self) -> i64 { 10 }
}
impl Tr1 for S {}
pub mod other {
    pub trait Tr2 {
        fn m(self) -> i64;
    }
    impl Tr2 for super::S {
        fn m(self) -> i64 { 0 }
    }
}

#[derive(Clone, Copy)]
pub struct P;
impl P {
    pub fn n(self) -> i64 { 0 }
}
pub trait Tr3 {
    fn n(self) -> i64;
}
impl Tr3 for P {
    fn n(self) -> i64 { 10 }
}

#[derive(Clone, Copy)]
pub struct Q;
impl Q {
    pub fn m(self) -> i64 { 0 }
}
impl Tr1 for Q {}

pub struct U;
pub trait Tr4 {
    fn only(self) -> i64;
}
impl Tr4 for U {
    fn only(self) -> i64 { 0 }
}

#[derive(Clone)]
pub struct V;
pub trait Owned {
    fn to_owned(self) -> i64;
}
impl Owned for V {
    fn to_owned(self) -> i64 { 0 }
}

pub struct W;
impl Clone for W {
    fn clone(&self) -> W { W }
}

pub struct X;
pub trait Tr5 {
    fn fwd(self) -> i64;
}
impl Tr5 for X {
    fn fwd(self) -> i64 { 0 }
}
impl Tr5 for &X {
    fn fwd(self) -> i64 { 1 }
}

pub struct Y;
impl Y {
    pub fn peek(&self) -> i64 { 5 }
}
pub trait Peek {
    fn peek(&self) -> i64;
}
impl Peek for Box<Y> {
    fn peek(&self) -> i64 { 7 }
}
"#;

/// The type of the local struct named `name` (not its constructor, which
/// prints the same path).
fn adt<'tcx>(tcx: TyCtxt<'tcx>, name: &str) -> Ty<'tcx> {
    let adt = tcx
        .iter_local_def_id()
        .find(|def_id| {
            tcx.def_kind(*def_id) == rustc_hir::def::DefKind::Struct
                && tcx.def_path_str(def_id.to_def_id()) == name
        })
        .unwrap_or_else(|| panic!("no struct `{name}`"));
    tcx.type_of(adt).instantiate_identity().skip_norm_wip()
}

fn by_ref<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
    Ty::new_imm_ref(tcx, tcx.lifetimes.re_erased, ty)
}

/// Only `Tr1` is in scope at a clause of the crate root, and `S` takes its
/// default body; an impl of `other::Tr2` is no evidence it is the callee.
#[test]
fn a_trait_default_competes_with_an_impl_of_another_trait() {
    probe("tw_method_lookup_default", SOURCE, |tcx| {
        reset();
        let s = adt(tcx, "S");
        let tr2_m = def_id_of(tcx, "<S as other::Tr2>::m");
        assert!(!selects_only(tcx, "m", s, tr2_m, true));
    });
}

/// An inherent method is found before any trait method, program or not.
#[test]
fn an_inherent_program_method_competes_with_a_trait_impl() {
    probe("tw_method_lookup_inherent_program", SOURCE, |tcx| {
        reset();
        let p = adt(tcx, "P");
        let tr3_n = def_id_of(tcx, "<P as Tr3>::n");
        assert!(!selects_only(tcx, "n", p, tr3_n, true));
    });
}

/// At its own type, by value, an inherent `self` method is selected before
/// every trait method; through a reference the first step is `&Q`, where a
/// trait method may be selected first, so the pick is not certain there.
#[test]
fn an_inherent_method_by_value_wins_only_at_its_own_type() {
    probe("tw_method_lookup_inherent_first", SOURCE, |tcx| {
        reset();
        let q = adt(tcx, "Q");
        let inherent_m = def_id_of(tcx, "Q::m");
        assert!(selects_only(tcx, "m", q, inherent_m, true));
        assert!(!selects_only(tcx, "m", by_ref(tcx, q), inherent_m, true));
        assert!(
            !selects_only(tcx, "m", q, inherent_m, false),
            "a receiver the caller cannot pin to `Q` itself gets no inherent-first shortcut"
        );
    });
}

/// The one method of its name anywhere is selected on the type and through a
/// reference to it.
#[test]
fn a_sole_trait_method_is_selected_on_the_type_and_through_a_reference() {
    probe("tw_method_lookup_sole", SOURCE, |tcx| {
        reset();
        let u = adt(tcx, "U");
        let only = def_id_of(tcx, "<U as Tr4>::only");
        assert!(selects_only(tcx, "only", u, only, true));
        assert!(selects_only(tcx, "only", by_ref(tcx, u), only, true));
    });
}

/// A dependency's trait is a candidate too: `ToOwned::to_owned` applies to
/// every `Clone` type, `V` among them.
#[test]
fn a_standard_library_trait_method_competes() {
    probe("tw_method_lookup_std_trait", SOURCE, |tcx| {
        reset();
        let v = adt(tcx, "V");
        let owned = def_id_of(tcx, "<V as Owned>::to_owned");
        assert!(!selects_only(tcx, "to_owned", v, owned, true));
    });
}

/// Through a reference, the standard library's `impl Clone for &T` is
/// selected at the first step, and it forwards to nothing of the pick's: it
/// does not compete. A LOCAL impl of the pick's trait for the reference does.
#[test]
fn only_a_local_impl_of_the_same_trait_for_a_reference_competes() {
    probe("tw_method_lookup_forwarding", SOURCE, |tcx| {
        reset();
        let w = adt(tcx, "W");
        let clone = def_id_of(tcx, "<W as std::clone::Clone>::clone");
        assert!(selects_only(tcx, "clone", by_ref(tcx, w), clone, true));

        let x = adt(tcx, "X");
        let fwd = def_id_of(tcx, "<X as Tr5>::fwd");
        assert!(selects_only(tcx, "fwd", x, fwd, true));
        assert!(!selects_only(tcx, "fwd", by_ref(tcx, x), fwd, true));
    });
}

/// Lookup stops at the first step where a method applies: the box's own
/// `peek` is selected at `Box<Y>`, and `Y`'s inherent `peek`, one step
/// further, never competes with it.
#[test]
fn no_step_past_the_pick_s_own_type_competes() {
    probe("tw_method_lookup_box", SOURCE, |tcx| {
        reset();
        let boxed = Ty::new_box(tcx, adt(tcx, "Y"));
        let box_peek = def_id_of(tcx, "<std::boxed::Box<Y> as Peek>::peek");
        assert!(selects_only(
            tcx,
            "peek",
            by_ref(tcx, boxed),
            box_peek,
            true
        ));
        let inherent = def_id_of(tcx, "Y::peek");
        assert!(
            !selects_only(tcx, "peek", by_ref(tcx, boxed), inherent, true),
            "the box's trait method is found at `Box<Y>`, before `Y`'s inherent one"
        );
    });
}
