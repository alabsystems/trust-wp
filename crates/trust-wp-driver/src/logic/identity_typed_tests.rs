// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for the three type-directed decisions that pick a logic
//! function's definition from a receiver's Rust type — or refuse.
//!
//! Every decision is pinned in BOTH directions and at the boundary between
//! them, because the boundary is what a later edit moves:
//!
//! - `impl_self_may_apply` OVER-approximates. Its cost of a `true` it did not
//!   owe is a REFUSAL (two candidates), never a wrong pick — so the test that
//!   matters is the one where a second candidate on the same ADT must make
//!   the whole resolution refuse.
//! - `impl_self_covers_all` UNDER-approximates. The one surviving candidate
//!   has to answer for EVERY instantiation of an open receiver, so `impl<A>
//!   P<A, A>` (a repeated parameter) and any impl carrying a const argument
//!   must be refused even though they are the only candidate.
//! - `peel_transparent_boxes` lists the levels a receiver's autoderef reaches
//!   through `Box` (the encoder gives `Box<T>` exactly `T`'s sort). A
//!   candidate at one level decides the call only where no other level has
//!   one, or where Rust cannot pass it by: its trait is declared in the
//!   module the call is written in, or every deeper candidate is of its
//!   trait. Otherwise the call names the first level whose trait is in
//!   scope, which the lookup cannot see, and it refuses.

use trust_wp_core::logic::identity::LogicFnFamilyMember;

use super::{impl_self_covers_all, impl_self_may_apply, peel_transparent_boxes, TypedOutcome};
use crate::logic::{
    identity::member_def_id,
    identity_test_support::{def_id_of, families_for, first_param_ty, member, probe},
};

/// `resolve_family_on_type` for a receiver-style call of the given arity,
/// written where no trait is known to be in scope.
fn resolve<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    family: &[LogicFnFamilyMember],
    ty: rustc_middle::ty::Ty<'tcx>,
) -> TypedOutcome {
    super::resolve_family_on_type(tcx, family, 1, ty, true, None)
}

/// [`resolve`] for a call written in the item `scope`.
fn resolve_in<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    family: &[LogicFnFamilyMember],
    ty: rustc_middle::ty::Ty<'tcx>,
    scope: rustc_hir::def_id::DefId,
) -> TypedOutcome {
    super::resolve_family_on_type(tcx, family, 1, ty, true, Some(scope))
}

// ---------------------------------------------------------------------------
// impl_self_may_apply — over-approximate, and a second candidate must refuse
// ---------------------------------------------------------------------------

/// Two definitions of `count`, on two DIFFERENT ADTs. On the open receiver
/// `List<T>` exactly one impl can apply, and the call resolves to it.
#[test]
fn may_apply_rejects_a_different_adt_so_the_open_receiver_resolves() {
    const SOURCE: &str = r#"
pub struct List<T>(pub T);
pub struct Other<T>(pub T);

impl<T> List<T> {
    #[doc = "trust-wp:logic:"]
    pub fn count(&self) -> i64 { 0 }
}

impl<T> Other<T> {
    #[doc = "trust-wp:logic:"]
    pub fn count(&self) -> i64 { 1 }
}

pub fn open_list<T>(l: &List<T>) -> i64 { l.count() }
"#;

    probe("tw_may_apply_distinct_adt", SOURCE, |tcx| {
        let family = families_for(tcx, "tw_may_apply_distinct_adt", "count");
        let list_count = member(&family, "List::<T>::count");
        let other_count = member(&family, "Other::<T>::count");
        let list_ty = first_param_ty(tcx, "open_list");

        assert!(
            impl_self_may_apply(tcx, member_def_id(&list_count.id).expect("def id"), list_ty),
            "the impl on `List<T>` must be admitted for the receiver `List<T>`"
        );
        assert!(
            !impl_self_may_apply(
                tcx,
                member_def_id(&other_count.id).expect("def id"),
                list_ty
            ),
            "`Other<T>` and `List<T>` are different ADTs and never unify: the \
             `Other` impl must be rejected, or the receiver would refuse"
        );

        assert_eq!(
            resolve(tcx, &family, list_ty),
            TypedOutcome::Id(list_count.id.clone()),
            "one surviving candidate covering every instantiation must resolve"
        );
    });
}

/// The SAME source shape with the rival moved onto the same ADT: an inherent
/// `List<T>::count` and a trait impl `Count for List<i32>`. Both may apply to
/// SOME instantiation of `List<T>`, so the receiver is uncertain and the call
/// must refuse — not pick the inherent one because it is "more likely".
#[test]
fn may_apply_admits_a_same_adt_rival_and_the_open_receiver_refuses() {
    const SOURCE: &str = r#"
pub struct List<T>(pub T);

pub trait Count {
    #[doc = "trust-wp:logic:"]
    fn count(&self) -> i64;
}

impl<T> List<T> {
    #[doc = "trust-wp:logic:"]
    pub fn count(&self) -> i64 { 0 }
}

impl Count for List<i32> {
    #[doc = "trust-wp:logic:"]
    fn count(&self) -> i64 { 1 }
}

pub fn open_list<T>(l: &List<T>) -> i64 { 0 }
"#;

    probe("tw_may_apply_same_adt", SOURCE, |tcx| {
        let family = families_for(tcx, "tw_may_apply_same_adt", "count");
        let inherent = member(&family, "List::<T>::count");
        let trait_impl = member(&family, "<List<i32> as Count>::count");
        let list_ty = first_param_ty(tcx, "open_list");

        assert!(
            impl_self_may_apply(tcx, member_def_id(&inherent.id).expect("def id"), list_ty),
            "the inherent impl may apply"
        );
        assert!(
            impl_self_may_apply(tcx, member_def_id(&trait_impl.id).expect("def id"), list_ty),
            "`List<i32>` is an instantiation of `List<T>`: the decision must \
             ADMIT it (that is the over-approximation), so that two candidates \
             refuse rather than one being silently preferred"
        );

        assert_eq!(
            resolve(tcx, &family, list_ty),
            TypedOutcome::Refused,
            "two candidates for one open receiver is an uncertain receiver, \
             and an uncertain receiver is refused, never guessed"
        );
    });
}

/// The boundary, in one crate: the rival's SELF TYPE is the only thing that
/// moves. On `List<T>` the same-ADT rival refuses the call; on `Only<T>`,
/// whose rival lives on a different ADT, the very same family resolves.
#[test]
fn may_apply_boundary_is_the_rival_self_type_not_the_receiver() {
    const SOURCE: &str = r#"
pub struct List<T>(pub T);
pub struct Only<T>(pub T);

pub trait Count {
    #[doc = "trust-wp:logic:"]
    fn count(&self) -> i64;
}

impl<T> List<T> {
    #[doc = "trust-wp:logic:"]
    pub fn count(&self) -> i64 { 0 }
}

impl Count for List<i32> {
    #[doc = "trust-wp:logic:"]
    fn count(&self) -> i64 { 1 }
}

impl<T> Only<T> {
    #[doc = "trust-wp:logic:"]
    pub fn count(&self) -> i64 { 2 }
}

pub fn open_list<T>(l: &List<T>) -> i64 { 0 }
pub fn open_only<T>(o: &Only<T>) -> i64 { 0 }
"#;

    probe("tw_may_apply_boundary", SOURCE, |tcx| {
        let family = families_for(tcx, "tw_may_apply_boundary", "count");
        let only_count = member(&family, "Only::<T>::count");

        assert_eq!(
            resolve(tcx, &family, first_param_ty(tcx, "open_list")),
            TypedOutcome::Refused,
            "`List<T>` has two candidates (inherent + `List<i32>` trait impl)"
        );
        assert_eq!(
            resolve(tcx, &family, first_param_ty(tcx, "open_only")),
            TypedOutcome::Id(only_count.id.clone()),
            "`Only<T>` has one, in the same family and the same crate: the \
             refusal above is the rival's self type, not a blanket refusal of \
             open receivers"
        );
    });
}

/// A non-ADT impl self type (here `i64`) against an ADT receiver cannot unify
/// either, and neither of them is a parameter: the candidate is rejected.
#[test]
fn may_apply_rejects_a_primitive_impl_against_an_adt_receiver() {
    const SOURCE: &str = r#"
pub struct List<T>(pub T);

pub trait Count {
    #[doc = "trust-wp:logic:"]
    fn count(&self) -> i64;
}

impl<T> List<T> {
    #[doc = "trust-wp:logic:"]
    pub fn count(&self) -> i64 { 0 }
}

impl Count for i64 {
    #[doc = "trust-wp:logic:"]
    fn count(&self) -> i64 { 1 }
}

pub fn open_list<T>(l: &List<T>) -> i64 { 0 }
"#;

    probe("tw_may_apply_primitive", SOURCE, |tcx| {
        let family = families_for(tcx, "tw_may_apply_primitive", "count");
        let on_i64 = member(&family, "<i64 as Count>::count");
        let list_count = member(&family, "List::<T>::count");
        let list_ty = first_param_ty(tcx, "open_list");

        assert!(
            !impl_self_may_apply(tcx, member_def_id(&on_i64.id).expect("def id"), list_ty),
            "`i64` is not an ADT and not a parameter: nothing instantiates \
             `List<T>` into it"
        );
        assert_eq!(
            resolve(tcx, &family, list_ty),
            TypedOutcome::Id(list_count.id.clone())
        );
    });
}

// ---------------------------------------------------------------------------
// impl_self_covers_all — under-approximate: a repeated parameter is not cover
// ---------------------------------------------------------------------------

/// `impl<A, B> Q<A, B>` covers every instantiation of `Q<X, Y>`; `impl<A>
/// P<A, A>` does NOT cover `P<X, Y>` — it only covers the diagonal. The
/// `seen.insert(p.index)` in `impl_self_covers_all` is what tells them apart,
/// and the receiver `P<X, Y>` must refuse even though `P`'s impl is the ONLY
/// candidate.
#[test]
fn covers_all_rejects_a_repeated_type_parameter() {
    const SOURCE: &str = r#"
pub struct P<A, B>(pub A, pub B);
pub struct Q<A, B>(pub A, pub B);

impl<A> P<A, A> {
    #[doc = "trust-wp:logic:"]
    pub fn tag(&self) -> i64 { 0 }
}

impl<A, B> Q<A, B> {
    #[doc = "trust-wp:logic:"]
    pub fn tag(&self) -> i64 { 1 }
}

pub fn open_p<X, Y>(p: &P<X, Y>) -> i64 { 0 }
pub fn open_q<X, Y>(q: &Q<X, Y>) -> i64 { 0 }
"#;

    probe("tw_covers_all_repeated", SOURCE, |tcx| {
        let family = families_for(tcx, "tw_covers_all_repeated", "tag");
        let p_tag = member(&family, "P::<A, A>::tag");
        let q_tag = member(&family, "Q::<A, B>::tag");
        let p_ty = first_param_ty(tcx, "open_p");
        let q_ty = first_param_ty(tcx, "open_q");

        assert!(
            impl_self_may_apply(tcx, member_def_id(&p_tag.id).expect("def id"), p_ty),
            "`impl<A> P<A, A>` is the same ADT, so it survives may_apply and \
             covers_all is the only thing left to refuse it"
        );
        assert!(
            !impl_self_covers_all(tcx, member_def_id(&p_tag.id).expect("def id"), p_ty),
            "`impl<A> P<A, A>` covers only `P<X, X>`, not every `P<X, Y>`"
        );
        assert!(
            impl_self_covers_all(tcx, member_def_id(&q_tag.id).expect("def id"), q_ty),
            "`impl<A, B> Q<A, B>` has a distinct parameter in every slot"
        );

        assert_eq!(
            resolve(tcx, &family, p_ty),
            TypedOutcome::Refused,
            "the ONLY candidate still refuses: it does not answer for every \
             instantiation of the receiver"
        );
        assert_eq!(
            resolve(tcx, &family, q_ty),
            TypedOutcome::Id(q_tag.id.clone()),
            "the boundary is the repeated parameter and nothing else: same \
             family, same crate, same arity, two type parameters each"
        );
    });
}

/// An impl carrying a CONST argument is refused too. `R<A, N>` genuinely does
/// cover every instantiation, and the decision still says no: const arguments
/// are outside what this check can reason about, and under-approximating costs
/// a refusal, never a wrong definition.
#[test]
fn covers_all_rejects_a_const_argument_impl() {
    const SOURCE: &str = r#"
pub struct R<A, const N: usize>(pub A);
pub struct S<A>(pub A);

impl<A, const N: usize> R<A, N> {
    #[doc = "trust-wp:logic:"]
    pub fn tag(&self) -> i64 { 0 }
}

impl<A> S<A> {
    #[doc = "trust-wp:logic:"]
    pub fn tag(&self) -> i64 { 1 }
}

pub fn open_r<X, const M: usize>(r: &R<X, M>) -> i64 { 0 }
pub fn open_s<X>(s: &S<X>) -> i64 { 0 }
"#;

    probe("tw_covers_all_const", SOURCE, |tcx| {
        let family = families_for(tcx, "tw_covers_all_const", "tag");
        let r_tag = member(&family, "R::<A, N>::tag");
        let s_tag = member(&family, "S::<A>::tag");
        let r_ty = first_param_ty(tcx, "open_r");
        let s_ty = first_param_ty(tcx, "open_s");

        assert!(
            !impl_self_covers_all(tcx, member_def_id(&r_tag.id).expect("def id"), r_ty),
            "a const argument in the impl self type is not covered"
        );
        assert_eq!(resolve(tcx, &family, r_ty), TypedOutcome::Refused);

        assert!(
            impl_self_covers_all(tcx, member_def_id(&s_tag.id).expect("def id"), s_ty),
            "the same shape without the const argument is covered"
        );
        assert_eq!(
            resolve(tcx, &family, s_ty),
            TypedOutcome::Id(s_tag.id.clone())
        );
    });
}

/// A CLOSED receiver never reaches `covers_all` at all (the `!open`
/// short-circuit hands the decision to `impl_self_matches`, which accepts an
/// exactly-equal self type). The same concrete `impl P<i32, i32>` therefore
/// ANSWERS `P<i32, i32>` and REFUSES the open `P<X, Y>` — the boundary is the
/// receiver's openness, not the impl.
#[test]
fn covers_all_is_not_consulted_for_a_closed_receiver() {
    const SOURCE: &str = r#"
pub struct P<A, B>(pub A, pub B);

impl P<i32, i32> {
    #[doc = "trust-wp:logic:"]
    pub fn tag(&self) -> i64 { 0 }
}

pub fn closed_p(p: &P<i32, i32>) -> i64 { 0 }
pub fn open_p<X, Y>(p: &P<X, Y>) -> i64 { 0 }
"#;

    probe("tw_covers_all_closed", SOURCE, |tcx| {
        let family = families_for(tcx, "tw_covers_all_closed", "tag");
        let p_tag = member(&family, "P::<i32, i32>::tag");
        let open_ty = first_param_ty(tcx, "open_p");

        assert_eq!(
            resolve(tcx, &family, first_param_ty(tcx, "closed_p")),
            TypedOutcome::Id(p_tag.id.clone()),
            "a concrete receiver matching the impl self type exactly resolves"
        );

        assert!(
            impl_self_may_apply(tcx, member_def_id(&p_tag.id).expect("def id"), open_ty),
            "`P<i32, i32>` is an instantiation of `P<X, Y>`: admitted"
        );
        assert!(
            !impl_self_covers_all(tcx, member_def_id(&p_tag.id).expect("def id"), open_ty),
            "but it answers only ONE instantiation, so it covers nothing open"
        );
        assert_eq!(
            resolve(tcx, &family, open_ty),
            TypedOutcome::Refused,
            "the only candidate still refuses an open receiver"
        );
    });
}

// ---------------------------------------------------------------------------
// peel_transparent_boxes — every autoderef level, and which one decides
// ---------------------------------------------------------------------------

/// With no candidate defined on a box, a `Box<W<i32>>` receiver resolves to
/// the inner type's definition: auto-deref selects it in Rust, and the
/// encoder gives `Box<T>` exactly `T`'s sort. The levels are the box and its
/// pointee, innermost last.
#[test]
fn boxes_peel_to_the_inner_receiver() {
    const SOURCE: &str = r#"
pub struct W<T>(pub T);
pub struct V<T>(pub T);

impl<T> W<T> {
    #[doc = "trust-wp:logic:"]
    pub fn peek(&self) -> i64 { 0 }
}

impl<T> V<T> {
    #[doc = "trust-wp:logic:"]
    pub fn peek(&self) -> i64 { 1 }
}

pub fn one_box(b: &Box<W<i32>>) -> i64 { 0 }
pub fn two_boxes(b: &Box<Box<W<i32>>>) -> i64 { 0 }
"#;

    probe("tw_box_peel", SOURCE, |tcx| {
        let family = families_for(tcx, "tw_box_peel", "peek");
        let w_peek = member(&family, "W::<T>::peek");

        let boxed_ty = first_param_ty(tcx, "one_box");
        assert!(
            boxed_ty.is_box(),
            "fixture should hand over a boxed receiver"
        );
        let levels = peel_transparent_boxes(tcx, boxed_ty);
        assert_eq!(levels.len(), 2, "the box and its pointee, got {levels:?}");
        assert!(
            !levels[1].is_box(),
            "the innermost level is the pointee, got {levels:?}"
        );
        assert_eq!(
            resolve(tcx, &family, boxed_ty),
            TypedOutcome::Id(w_peek.id.clone())
        );

        let twice = first_param_ty(tcx, "two_boxes");
        assert_eq!(
            peel_transparent_boxes(tcx, twice).len(),
            3,
            "nested boxes peel all the way down"
        );
        assert_eq!(
            resolve(tcx, &family, twice),
            TypedOutcome::Id(w_peek.id.clone())
        );
    });
}

const BOX_IMPL_SOURCE: &str = r#"
pub struct W<T>(pub T);

pub trait Peek {
    #[doc = "trust-wp:logic:"]
    fn peek(&self) -> i64;
}

impl<T> W<T> {
    #[doc = "trust-wp:logic:"]
    pub fn peek(&self) -> i64 { 0 }
}

impl Peek for Box<W<i32>> {
    #[doc = "trust-wp:logic:"]
    fn peek(&self) -> i64 { 1 }
}

pub fn one_box(b: &Box<W<i32>>) -> i64 { 0 }
pub fn plain(w: &W<i32>) -> i64 { 0 }

pub mod elsewhere {
    pub fn written_here(b: &Box<super::W<i32>>) -> i64 { 0 }
}
"#;

/// A member defined ON the box stops the peel -- Rust's probe selects it
/// before it derefs -- only where `Peek` is in scope; elsewhere the probe
/// passes it by and derefs to `W::peek`. Written in the module that declares
/// `Peek`, the call is the box's own definition; written where that is not
/// known, the box and its pointee both have a candidate and the call
/// refuses. Before, the box member was bound wherever the call was written.
#[test]
fn a_box_impl_in_the_family_stops_the_peel() {
    probe("tw_box_impl_scope", BOX_IMPL_SOURCE, |tcx| {
        let family = families_for(tcx, "tw_box_impl_scope", "peek");
        let box_peek = member(&family, "Box<W<i32>> as Peek>::peek");
        let boxed_ty = first_param_ty(tcx, "one_box");

        assert_eq!(
            resolve_in(tcx, &family, boxed_ty, def_id_of(tcx, "one_box")),
            TypedOutcome::Id(box_peek.id.clone()),
            "`Peek` is declared in the module `one_box` is written in"
        );
        assert_eq!(
            resolve_in(
                tcx,
                &family,
                first_param_ty(tcx, "written_here"),
                def_id_of(tcx, "written_here")
            ),
            TypedOutcome::Refused,
            "in `elsewhere` `Peek` is not known to be in scope"
        );
        assert_eq!(
            resolve(tcx, &family, boxed_ty),
            TypedOutcome::Refused,
            "with no scope, the box level and its pointee both have a candidate"
        );
    });
}

/// The box member is a candidate of the BOX level only: with it present, an
/// unboxed `W<i32>` receiver still resolves to the inner definition wherever
/// the call is written. (`def_id_of` keeps the fixture honest about which
/// impl is which.)
#[test]
fn the_box_bailout_does_not_disturb_an_unboxed_receiver() {
    probe("tw_box_impl_unboxed", BOX_IMPL_SOURCE, |tcx| {
        let family = families_for(tcx, "tw_box_impl_unboxed", "peek");
        let w_peek = member(&family, "W::<T>::peek");
        let box_peek = member(&family, "Box<W<i32>> as Peek>::peek");
        assert_ne!(
            member_def_id(&w_peek.id),
            member_def_id(&box_peek.id),
            "fixture should carry two distinct definitions"
        );
        assert_eq!(
            def_id_of(tcx, "W::<T>::peek"),
            member_def_id(&w_peek.id).expect("def id"),
            "the inherent `peek` is the member the registry recorded"
        );
        assert_eq!(
            resolve(tcx, &family, first_param_ty(tcx, "plain")),
            TypedOutcome::Id(w_peek.id.clone()),
            "an unboxed receiver has one level and one candidate"
        );
    });
}

/// method_call_box_receiver_other_trait_out_of_scope's shape: `Other` is
/// implemented for `Box<S>` in another module, `AssocTrait` for `S`. Where
/// `f` is written `Other` need not be in scope, and then Rust derefs the box
/// and selects `<S as AssocTrait>::holds`; the call refuses. Before, the box
/// member stopped the peel and `<Box<S> as other::Other>::holds` was bound.
#[test]
fn a_box_impl_of_a_trait_declared_elsewhere_does_not_decide_the_call() {
    const SOURCE: &str = r#"
pub trait AssocTrait {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool;
}

pub struct S;
impl AssocTrait for S {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool { false }
}

pub mod other {
    pub trait Other {
        #[doc = "trust-wp:logic:"]
        fn holds(self) -> bool;
    }
    impl Other for Box<super::S> {
        #[doc = "trust-wp:logic:"]
        fn holds(self) -> bool { true }
    }
}

pub fn boxed_call(b: Box<S>) {}
pub fn plain_call(s: S) {}
"#;

    probe("tw_box_other_trait", SOURCE, |tcx| {
        let family = families_for(tcx, "tw_box_other_trait", "holds");
        let at_s = member(&family, "<S as AssocTrait>::holds").id.clone();
        assert_eq!(
            resolve_in(
                tcx,
                &family,
                first_param_ty(tcx, "boxed_call"),
                def_id_of(tcx, "boxed_call")
            ),
            TypedOutcome::Refused,
            "the box level's `Other` may be out of scope where the call is written"
        );
        assert_eq!(
            resolve_in(
                tcx,
                &family,
                first_param_ty(tcx, "plain_call"),
                def_id_of(tcx, "plain_call")
            ),
            TypedOutcome::Id(at_s),
            "an unboxed `S` has one candidate"
        );
    });
}

/// Two levels whose candidates are all of ONE trait: `Peek` is in scope for
/// both or for neither, so the box's own impl is what Rust selects and the
/// call binds it even where the scope is not known.
#[test]
fn candidates_of_one_trait_at_two_levels_bind_the_outer_one() {
    const SOURCE: &str = r#"
pub struct W(pub i32);

pub trait Peek {
    #[doc = "trust-wp:logic:"]
    fn peek(&self) -> i64;
}

impl Peek for W {
    #[doc = "trust-wp:logic:"]
    fn peek(&self) -> i64 { 0 }
}

impl Peek for Box<W> {
    #[doc = "trust-wp:logic:"]
    fn peek(&self) -> i64 { 1 }
}

pub fn one_box(b: &Box<W>) -> i64 { 0 }
"#;

    probe("tw_box_one_trait", SOURCE, |tcx| {
        let family = families_for(tcx, "tw_box_one_trait", "peek");
        let box_peek = member(&family, "Box<W> as Peek>::peek");
        assert_eq!(
            resolve(tcx, &family, first_param_ty(tcx, "one_box")),
            TypedOutcome::Id(box_peek.id.clone())
        );
    });
}

// ---------------------------------------------------------------------------
// applies_at_closed — an impl whose self type is not the receiver's type
// ---------------------------------------------------------------------------

/// `holds` has a BLANKET impl for every `T: Marker` and a direct `Other` impl
/// for `S` and for `N`; only `S` and `B` are `Marker`. At `S` both impls apply
/// (Rust picks the one whose trait is in scope), at `N` only `Other`'s, at `B`
/// only the blanket one.
const BLANKET_SOURCE: &str = r#"
pub trait Marker {}

pub trait AssocTrait {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool;
}

impl<T: Marker> AssocTrait for T {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool { false }
}

pub trait Other {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool;
}

pub struct S;
pub struct N;
pub struct B;
impl Marker for S {}
impl Marker for B {}

impl Other for S {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool { true }
}

impl Other for N {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool { true }
}

pub fn at_s(s: S) {}
pub fn at_n(n: N) {}
pub fn at_b(b: B) {}
"#;

/// A blanket impl is a candidate wherever rustc's selection picks it: beside
/// another trait's impl it makes the call refuse (the lookup cannot tell which
/// trait is in scope), alone it is the answer, and where its bound fails it is
/// no candidate at all. Before, it was invisible, and `s.holds()` at `S` bound
/// `<S as Other>::holds` although `Other` need not be in scope.
#[test]
fn a_blanket_impl_is_a_candidate_where_selection_picks_it() {
    probe("tw_blanket_candidate", BLANKET_SOURCE, |tcx| {
        let family = families_for(tcx, "tw_blanket_candidate", "holds");
        let blanket = member(&family, "<T as AssocTrait>::holds").id.clone();
        let other_n = member(&family, "<N as Other>::holds").id.clone();
        assert_eq!(
            resolve(tcx, &family, first_param_ty(tcx, "at_s")),
            TypedOutcome::Refused,
            "at `S` the blanket impl and `Other`'s both apply"
        );
        assert_eq!(
            resolve(tcx, &family, first_param_ty(tcx, "at_n")),
            TypedOutcome::Id(other_n),
            "`N` is not `Marker`, so the blanket impl does not apply there"
        );
        assert_eq!(
            resolve(tcx, &family, first_param_ty(tcx, "at_b")),
            TypedOutcome::Id(blanket),
            "at `B` the blanket impl is the one definition that applies"
        );
    });
}

/// A trait DEFAULT that runs at the receiver -- through a concrete impl that
/// does not define the method, a blanket one, or an impl covering an open
/// ADT -- is a candidate: beside another trait's impl the call refuses, where
/// it is the one definition that runs it is the answer, and where the impl
/// selected at the receiver defines the method it is no candidate at all.
/// Before, the default was invisible beside an impl member, and `s.holds()`
/// at `S` bound `<S as Other>::holds` although `Other` need not be in scope.
#[test]
fn a_trait_default_that_runs_at_the_receiver_is_a_candidate() {
    const SOURCE: &str = r#"
pub trait Marker {}

pub trait AssocTrait {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool where Self: Sized { false }
}

pub trait Other {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool;
}

pub struct S;
pub struct B;
pub struct N;
pub struct V;
pub struct D;
pub struct L<T>(pub T);

impl AssocTrait for S {}
impl<T: Marker> AssocTrait for T {}
impl Marker for B {}
impl AssocTrait for D {}
impl<T> AssocTrait for L<T> {}

impl AssocTrait for V {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool { true }
}

impl Other for S {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool { true }
}

impl Other for B {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool { true }
}

impl Other for N {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool { true }
}

impl<T> Other for L<T> {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool { true }
}

pub fn at_s(s: S) {}
pub fn at_b(b: B) {}
pub fn at_n(n: N) {}
pub fn at_v(v: V) {}
pub fn at_d(d: D) {}
pub fn open_l<T>(l: L<T>) {}
"#;

    probe("tw_default_candidate", SOURCE, |tcx| {
        let family = families_for(tcx, "tw_default_candidate", "holds");
        let decl = member(&family, "::AssocTrait::holds").id.clone();
        let other_n = member(&family, "<N as Other>::holds").id.clone();
        let override_v = member(&family, "<V as AssocTrait>::holds").id.clone();
        assert_eq!(
            resolve(tcx, &family, first_param_ty(tcx, "at_s")),
            TypedOutcome::Refused,
            "at `S` the default and `Other`'s impl both apply"
        );
        assert_eq!(
            resolve(tcx, &family, first_param_ty(tcx, "at_b")),
            TypedOutcome::Refused,
            "at `B` the default runs through the blanket impl, beside `Other`'s impl"
        );
        assert_eq!(
            resolve(tcx, &family, first_param_ty(tcx, "open_l")),
            TypedOutcome::Refused,
            "at the open `L<T>` the default may run beside `Other`'s impl"
        );
        assert_eq!(
            resolve(tcx, &family, first_param_ty(tcx, "at_n")),
            TypedOutcome::Id(other_n),
            "`N` implements no `AssocTrait`, so no default runs there"
        );
        assert_eq!(
            resolve(tcx, &family, first_param_ty(tcx, "at_v")),
            TypedOutcome::Id(override_v),
            "`V`'s impl defines `holds`, so the default is no candidate"
        );
        assert_eq!(
            resolve(tcx, &family, first_param_ty(tcx, "at_d")),
            TypedOutcome::Id(decl),
            "at `D` the default is the one definition that runs"
        );
    });
}

/// An impl on `&S` is the one Rust selects for a receiver of type `&S`, which
/// reaches the lookup peeled to `S`: it is a candidate that refuses, beside
/// another impl and alone.
#[test]
fn an_impl_on_a_reference_is_a_candidate_that_refuses() {
    const SOURCE: &str = r#"
pub trait AssocTrait {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool;
}

pub trait Other {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool;
}

pub struct S;
pub struct R;

impl AssocTrait for &S {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool { false }
}

impl Other for S {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool { true }
}

impl AssocTrait for &R {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool { false }
}

pub fn at_s(s: &S) {}
pub fn at_r(r: &R) {}
"#;

    probe("tw_ref_impl_candidate", SOURCE, |tcx| {
        let family = families_for(tcx, "tw_ref_impl_candidate", "holds");
        assert_eq!(
            resolve(tcx, &family, first_param_ty(tcx, "at_s")),
            TypedOutcome::Refused,
            "`<&S as AssocTrait>::holds` is a candidate beside `<S as Other>::holds`"
        );
        assert_eq!(
            resolve(tcx, &family, first_param_ty(tcx, "at_r")),
            TypedOutcome::Refused,
            "whether the receiver had the reference is not known here"
        );
    });
}

/// A trait with a parameter besides `Self` is read by self type: its impl
/// covering every `W<T>` is the answer at `W<i32>` when it is alone, and a
/// blanket impl of another such trait beside it is a candidate that refuses
/// (`W<i32>` is `Marker` in the second crate, so Rust could select either).
#[test]
fn a_parameterized_trait_s_impl_is_read_by_self_type_and_a_blanket_one_refuses() {
    const ALONE: &str = r#"
pub trait P<X> {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool;
}

pub struct W<T>(pub T);

impl<T> P<u8> for W<T> {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool { true }
}

pub struct V;
impl V {
    #[doc = "trust-wp:logic:"]
    pub fn holds(self) -> bool { false }
}

pub fn at_w(w: W<i32>) {}
"#;
    const WITH_BLANKET: &str = r#"
pub trait Marker {}

pub trait P<X> {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool;
}

pub trait Q<X> {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool;
}

pub struct W<T>(pub T);
impl<T> Marker for W<T> {}

impl<T> P<u8> for W<T> {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool { true }
}

impl<T: Marker> Q<u16> for T {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool { false }
}

pub fn at_w(w: W<i32>) {}
"#;

    probe("tw_param_trait_alone", ALONE, |tcx| {
        let family = families_for(tcx, "tw_param_trait_alone", "holds");
        let covering = member(&family, "<W<T> as P<u8>>::holds").id.clone();
        assert_eq!(
            resolve(tcx, &family, first_param_ty(tcx, "at_w")),
            TypedOutcome::Id(covering)
        );
    });
    probe("tw_param_trait_blanket", WITH_BLANKET, |tcx| {
        let family = families_for(tcx, "tw_param_trait_blanket", "holds");
        assert_eq!(
            resolve(tcx, &family, first_param_ty(tcx, "at_w")),
            TypedOutcome::Refused,
            "the blanket `Q<u16>` impl may be the one Rust selects at `W<i32>`"
        );
    });
}
