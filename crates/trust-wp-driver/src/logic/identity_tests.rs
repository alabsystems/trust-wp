// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for the two scope-side decisions that give a receiver its Rust
//! type — the match-arm / `let` type carry, and `body_local_type`.
//!
//! Both answer the same question for `x.m(..)` in a clause: what is `x`? A
//! wrong answer is not a refusal, it is the WRONG DEFINITION — `A::tag` where
//! the program means `B::tag` — so each is pinned where it must answer, where
//! it must refuse, and at the boundary between the two.

use std::sync::Arc;

use trust_wp_core::formula::{BinOp, MatchArm, Pattern, PureExpr};

use super::{resolve_logic_fn_paths_in_scope, ClausePosition, ResolveMode, Resolver};
use crate::logic::{
    identity_test_support::{def_id_of, families_for, member, probe},
    spec_calls::ClauseRef,
};

/// Two types with a colliding `tag`, an enum carrying one of each, and owners
/// whose clauses the tests build by hand.
const SOURCE: &str = r#"
pub struct A(pub i64);
pub struct B(pub i64);

pub enum E {
    One(A),
    Two(B),
}

impl A {
    #[doc = "trust-wp:logic:"]
    pub fn tag(&self) -> i64 { 0 }
}

impl B {
    #[doc = "trust-wp:logic:"]
    pub fn tag(&self) -> i64 { 1 }
}

pub fn on_enum(e: &E) -> i64 { 0 }
pub fn on_pair(a: &A, b: &B) -> i64 { 0 }

pub fn one_local() -> i64 {
    let s = A(1);
    s.0
}

pub fn two_locals(flag: bool) -> i64 {
    if flag {
        let s = A(1);
        s.0
    } else {
        let s = B(2);
        s.0
    }
}
"#;

/// Every clause here stands where a loop invariant or assertion does: the
/// receivers they type are the body's locals. The hand lookup is tested
/// alone, without rustc's confirmation.
fn resolve_in_body(
    tcx: rustc_middle::ty::TyCtxt<'_>,
    owner: rustc_hir::def_id::DefId,
    expr: &PureExpr,
) -> PureExpr {
    resolve_logic_fn_paths_in_scope(
        tcx,
        owner,
        expr,
        ClausePosition::Body,
        &ClauseRef::HandLookupUnderTest,
    )
}

fn var(name: &str) -> PureExpr {
    PureExpr::Var(name.to_string(), None)
}

fn tag_call(receiver: &str) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(var(receiver)),
        method: "tag".to_string(),
        args: Vec::new(),
    }
}

fn constructor(name: &str, bindings: &[&str]) -> Pattern {
    Pattern::Constructor {
        name: name.to_string(),
        inner: Some(Box::new(Pattern::Tuple(
            bindings
                .iter()
                .map(|binding| Pattern::Binding((*binding).to_string()))
                .collect(),
        ))),
    }
}

/// Every logic-function call name the expression carries, in traversal order.
/// A `MethodCall` that stayed a `MethodCall` is spelled `<unresolved>`: that
/// is what a refusal looks like here — the encoder later refuses the clause.
fn call_names(expr: &PureExpr) -> Vec<String> {
    let mut out = Vec::new();
    fn walk(expr: &PureExpr, out: &mut Vec<String>) {
        match expr {
            PureExpr::LogicFnCall { name, args } => {
                out.push(name.clone());
                for arg in args {
                    walk(arg, out);
                }
            }
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } => {
                out.push(format!("<unresolved>::{method}"));
                walk(receiver, out);
                for arg in args {
                    walk(arg, out);
                }
            }
            PureExpr::Match { scrutinee, arms } => {
                walk(scrutinee, out);
                for arm in arms {
                    walk(&arm.body, out);
                }
            }
            PureExpr::Let { value, body, .. } => {
                walk(value, out);
                walk(body, out);
            }
            PureExpr::Forall { body, .. } | PureExpr::Exists { body, .. } => walk(body, out),
            PureExpr::BinOp(left, _, right) => {
                walk(left, out);
                walk(right, out);
            }
            PureExpr::Old(inner)
            | PureExpr::Deref(inner)
            | PureExpr::Final(inner)
            | PureExpr::View(inner) => walk(inner, out),
            _ => {}
        }
    }
    walk(expr, &mut out);
    out
}

// ---------------------------------------------------------------------------
// The match-arm / let-binding type carry
// ---------------------------------------------------------------------------

/// One `match` over `E`, two arms, the SAME spelling `_.tag()` in each. The
/// arm's own field type is what decides, so the two arms must resolve to two
/// DIFFERENT definitions. That difference is the whole point of the carry:
/// without it both arms spell one name and one of them is wrong.
#[test]
fn match_arm_bindings_carry_the_variant_field_type() {
    probe("tw_match_arm_carry", SOURCE, |tcx| {
        let family = families_for(tcx, "tw_match_arm_carry", "tag");
        let a_tag = member(&family, "A::tag").id.clone();
        let b_tag = member(&family, "B::tag").id.clone();
        assert_ne!(a_tag, b_tag);

        let clause = PureExpr::Match {
            scrutinee: Arc::new(var("e")),
            arms: vec![
                MatchArm {
                    pattern: constructor("One", &["x"]),
                    body: tag_call("x"),
                },
                MatchArm {
                    pattern: constructor("Two", &["y"]),
                    body: tag_call("y"),
                },
            ],
        };

        let resolved = resolve_in_body(tcx, def_id_of(tcx, "on_enum"), &clause);
        assert_eq!(
            call_names(&resolved),
            vec![a_tag, b_tag],
            "`One(x) => x.tag()` is `A::tag` and `Two(y) => y.tag()` is \
             `B::tag`: the arm's field type decides, not the spelling"
        );
    });
}

/// A pattern whose arity does not match the variant's fields types NOTHING —
/// the binding gets `None` and the call is refused. The boundary is one item
/// in the tuple pattern: `One(x)` resolves, `One(x, extra)` refuses.
#[test]
fn a_misaligned_pattern_refuses_instead_of_guessing() {
    probe("tw_match_arm_misaligned", SOURCE, |tcx| {
        let family = families_for(tcx, "tw_match_arm_misaligned", "tag");
        let a_tag = member(&family, "A::tag").id.clone();
        let owner = def_id_of(tcx, "on_enum");

        let aligned = PureExpr::Match {
            scrutinee: Arc::new(var("e")),
            arms: vec![MatchArm {
                pattern: constructor("One", &["x"]),
                body: tag_call("x"),
            }],
        };
        assert_eq!(
            call_names(&resolve_in_body(tcx, owner, &aligned)),
            vec![a_tag],
            "`One` has exactly one field, so `x` is typed"
        );

        let misaligned = PureExpr::Match {
            scrutinee: Arc::new(var("e")),
            arms: vec![MatchArm {
                pattern: constructor("One", &["x", "extra"]),
                body: tag_call("x"),
            }],
        };
        assert_eq!(
            call_names(&resolve_in_body(tcx, owner, &misaligned)),
            vec!["<unresolved>::tag".to_string()],
            "two items against a one-field variant: the field types do not \
             line up with the pattern, and an untyped receiver is refused"
        );
    });
}

/// An untyped SCRUTINEE types no binding either: the carry propagates a type
/// it has, and refuses where it has none.
#[test]
fn an_untyped_scrutinee_types_no_arm_binding() {
    probe("tw_match_arm_untyped_scrutinee", SOURCE, |tcx| {
        let _family = families_for(tcx, "tw_match_arm_untyped_scrutinee", "tag");
        let clause = PureExpr::Match {
            scrutinee: Arc::new(var("nothing_named_this")),
            arms: vec![MatchArm {
                pattern: constructor("One", &["x"]),
                body: tag_call("x"),
            }],
        };
        assert_eq!(
            call_names(&resolve_in_body(tcx, def_id_of(tcx, "on_enum"), &clause)),
            vec!["<unresolved>::tag".to_string()],
        );
    });
}

/// `let v = <owner parameter> in v.tag()` carries the parameter's type onto
/// `v`. Both directions in one owner: `let v = a` is `A::tag`, `let v = b` is
/// `B::tag`, same clause shape, same variable name.
#[test]
fn let_bindings_carry_the_value_type() {
    probe("tw_let_carry", SOURCE, |tcx| {
        let family = families_for(tcx, "tw_let_carry", "tag");
        let a_tag = member(&family, "A::tag").id.clone();
        let b_tag = member(&family, "B::tag").id.clone();
        let owner = def_id_of(tcx, "on_pair");

        let bound_to = |param: &str| PureExpr::Let {
            var: "v".to_string(),
            value: Arc::new(var(param)),
            body: Arc::new(tag_call("v")),
        };

        assert_eq!(
            call_names(&resolve_in_body(tcx, owner, &bound_to("a"))),
            vec![a_tag]
        );
        assert_eq!(
            call_names(&resolve_in_body(tcx, owner, &bound_to("b"))),
            vec![b_tag],
            "the same `let v = _ in v.tag()` follows the value, not the name"
        );
    });
}

/// A `let` value that is not a name (here `a + 1`) has no type the carry can
/// read, so the binding is untyped and the call refuses.
#[test]
fn a_let_value_with_no_readable_type_refuses() {
    probe("tw_let_untyped", SOURCE, |tcx| {
        let _family = families_for(tcx, "tw_let_untyped", "tag");
        let clause = PureExpr::Let {
            var: "v".to_string(),
            value: Arc::new(PureExpr::BinOp(
                Arc::new(var("a")),
                BinOp::Add,
                Arc::new(PureExpr::Int(1)),
            )),
            body: Arc::new(tag_call("v")),
        };
        assert_eq!(
            call_names(&resolve_in_body(tcx, def_id_of(tcx, "on_pair"), &clause)),
            vec!["<unresolved>::tag".to_string()],
        );
    });
}

// ---------------------------------------------------------------------------
// body_local_type
// ---------------------------------------------------------------------------

/// A loop invariant or assertion may name a `let` local of the owner's own
/// body. One binding of `s`, at one type, resolves.
#[test]
fn a_body_local_bound_once_types_its_receiver() {
    probe("tw_body_local_once", SOURCE, |tcx| {
        let family = families_for(tcx, "tw_body_local_once", "tag");
        let a_tag = member(&family, "A::tag").id.clone();
        assert_eq!(
            call_names(&resolve_in_body(
                tcx,
                def_id_of(tcx, "one_local"),
                &tag_call("s"),
            )),
            vec![a_tag],
            "`one_local` binds `s` exactly once, at `A`"
        );
    });
}

/// The boundary: the SAME clause in an owner that binds `s` twice, at two
/// types. The spelling no longer says which one, and an ambiguous receiver is
/// refused rather than resolved to whichever binding was visited first.
#[test]
fn a_body_local_bound_twice_at_two_types_refuses() {
    probe("tw_body_local_twice", SOURCE, |tcx| {
        let _family = families_for(tcx, "tw_body_local_twice", "tag");
        assert_eq!(
            call_names(&resolve_in_body(
                tcx,
                def_id_of(tcx, "two_locals"),
                &tag_call("s"),
            )),
            vec!["<unresolved>::tag".to_string()],
            "`two_locals` binds `s` at `A` in one branch and `B` in the other"
        );
    });
}

/// The invariant `body_local_type` rests on, asserted: a name the CLAUSE
/// binds is never typed from the body. `one_local` binds `s` at `A`, and a
/// clause that quantifies over `s` must NOT pick that type up — the quantified
/// `s` is a fresh solver variable with no Rust type at all.
///
/// Both halves are checked: end to end through the quantifier, and directly
/// against `body_local_type`, which is the guard a future edit would have to
/// delete on purpose.
#[test]
fn body_local_type_refuses_a_clause_binder() {
    probe("tw_body_local_binder", SOURCE, |tcx| {
        let family = families_for(tcx, "tw_body_local_binder", "tag");
        let a_tag = member(&family, "A::tag").id.clone();
        let owner = def_id_of(tcx, "one_local");

        let quantified = PureExpr::Forall {
            var: "s".to_string(),
            var_sort: None,
            body: Arc::new(tag_call("s")),
            triggers: Vec::new(),
        };
        assert_eq!(
            call_names(&resolve_in_body(tcx, owner, &quantified)),
            vec!["<unresolved>::tag".to_string()],
            "a quantified `s` shadows the body's `s` and has no Rust type"
        );
        assert_eq!(
            call_names(&resolve_in_body(tcx, owner, &tag_call("s"))),
            vec![a_tag],
            "the same call OUTSIDE the quantifier still reads the body local: \
             the refusal above is the binder, not a blanket refusal"
        );

        let registry = trust_wp_core::logic::identity::logic_fn_identity_registry()
            .expect("identity assignment installs a registry");
        let resolver = |bound: Vec<String>| Resolver {
            tcx,
            owner,
            registry: Arc::clone(&registry),
            bound_tys: vec![None; bound.len()],
            bound,
            signature: None,
            mode: ResolveMode::OwnerVc,
            position: ClausePosition::Body,
            body_locals: std::cell::OnceCell::new(),
            outcomes: std::collections::HashMap::new(),
            clause: ClauseRef::HandLookupUnderTest,
            spec_calls: std::cell::OnceCell::new(),
        };
        assert!(
            resolver(Vec::new()).body_local_type("s").is_some(),
            "unbound `s` is the body's local"
        );
        assert!(
            resolver(vec!["s".to_string()])
                .body_local_type("s")
                .is_none(),
            "bound `s` is the clause's own binder, and this is the guard that \
             says so — deleting it re-arms a wrong-definition pick, not a \
             refusal"
        );
    });
}

// ---------------------------------------------------------------------------
// A trait's grant instantiated at an impl (`ResolveMode::DeclAtImpl`, D-156)
// ---------------------------------------------------------------------------

/// `Outer::holds`'s grant names `Inner::ok` on `inner: Self::In`. `I` has an
/// inherent `ok` beside its `Inner` impl, and `Wrap<T>` implements `Outer`
/// with `In = T`, a type still generic at the impl.
const GRANT_SOURCE: &str = r#"
pub trait Inner {
    #[doc = "trust-wp:logic:"]
    fn ok(self) -> bool;
}

pub trait Outer {
    type In: Inner;
    #[doc = "trust-wp:logic:"]
    fn holds(self, inner: Self::In) -> bool;
}

pub struct I;
pub struct O;
pub struct Wrap<T>(pub T);

impl I {
    #[doc = "trust-wp:logic:"]
    pub fn ok(self) -> bool { true }
}

impl Inner for I {
    #[doc = "trust-wp:logic:"]
    fn ok(self) -> bool { false }
}

impl Outer for O {
    type In = I;
    #[doc = "trust-wp:logic:"]
    fn holds(self, _inner: I) -> bool { true }
}

impl<T: Inner> Outer for Wrap<T> {
    type In = T;
    #[doc = "trust-wp:logic:"]
    fn holds(self, _inner: T) -> bool { true }
}
"#;

fn ok_call(name: &str, receiver: &str) -> PureExpr {
    PureExpr::LogicFnCall {
        name: name.to_string(),
        args: vec![var(receiver)],
    }
}

/// The declaration `Inner::ok` on `inner` reads, at `O`, as the item rustc's
/// instance resolution selects for `<I as Inner>::ok` -- NOT the inherent
/// `I::ok` a method call written at `I` would pick. The grant never named the
/// inherent method: at `Self::In` only the trait's `ok` is visible.
#[test]
fn a_declaration_call_is_the_impl_rustc_selects_at_the_impl() {
    probe("tw_decl_at_impl", GRANT_SOURCE, |tcx| {
        let family = families_for(tcx, "tw_decl_at_impl", "ok");
        let decl = member(&family, "tw_decl_at_impl::Inner::ok").id.clone();
        let trait_impl = member(&family, "<I as Inner>::ok").id.clone();
        let inherent = member(&family, "tw_decl_at_impl::I::ok").id.clone();
        let params = ["self".to_string(), "inner".to_string()];
        let trait_method = def_id_of(tcx, "Outer::holds");
        let at = |impl_method| {
            call_names(&super::instantiate_trait_decl_calls_at_impl(
                tcx,
                trait_method,
                impl_method,
                &params,
                &ok_call(&decl, "inner"),
            ))
        };
        assert_eq!(
            at(def_id_of(tcx, "<O as Outer>::holds")),
            vec![trait_impl.clone()]
        );
        assert_ne!(trait_impl, inherent);
        assert_eq!(
            at(def_id_of(tcx, "<Wrap<T> as Outer>::holds")),
            vec![decl.clone()],
            "at `Wrap<T>` the receiver's type is the parameter `T`: no one \
             implementation answers for it, so the declaration stays and the \
             discharge refuses it"
        );
    });
}

/// A binder that shadows the parameter is the clause's own variable, with no
/// type from the signature: the call under it is left as the declaration.
#[test]
fn a_declaration_call_on_a_binder_is_not_instantiated() {
    probe("tw_decl_at_impl_binder", GRANT_SOURCE, |tcx| {
        let family = families_for(tcx, "tw_decl_at_impl_binder", "ok");
        let decl = member(&family, "tw_decl_at_impl_binder::Inner::ok")
            .id
            .clone();
        let trait_impl = member(&family, "<I as Inner>::ok").id.clone();
        let params = ["self".to_string(), "inner".to_string()];
        let quantified = PureExpr::Forall {
            var: "inner".to_string(),
            var_sort: None,
            body: Arc::new(ok_call(&decl, "inner")),
            triggers: Vec::new(),
        };
        let clause = PureExpr::BinOp(
            Arc::new(quantified),
            BinOp::And,
            Arc::new(ok_call(&decl, "inner")),
        );
        let resolved = super::instantiate_trait_decl_calls_at_impl(
            tcx,
            def_id_of(tcx, "Outer::holds"),
            def_id_of(tcx, "<O as Outer>::holds"),
            &params,
            &clause,
        );
        assert_eq!(
            call_names(&resolved),
            vec![decl, trait_impl],
            "the bound `inner` keeps the declaration; the parameter `inner` \
             beside it is instantiated"
        );
    });
}

// ---------------------------------------------------------------------------
// A trait clause read at an impl, and a call through a named trait
// ---------------------------------------------------------------------------

/// `Trait::check`'s clause names `assoc.holds()` on `assoc: Self::Assoc`,
/// whose bound is `AssocTrait`. At `Struct`, `Assoc = AssocStruct`, whose
/// `AssocTrait` impl is the BLANKET one; `AssocStruct` also has an inherent
/// `holds` and implements `Other`, which declares `holds` too.
const BLANKET_CLAUSE_SOURCE: &str = r#"
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

pub trait Trait {
    type Assoc: AssocTrait;
    fn check(&self, assoc: Self::Assoc) -> bool;
}

pub struct AssocStruct;
impl Marker for AssocStruct {}

impl AssocStruct {
    #[doc = "trust-wp:logic:"]
    pub fn holds(self) -> bool { true }
}

impl Other for AssocStruct {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool { true }
}

pub struct Struct;

impl Trait for Struct {
    type Assoc = AssocStruct;
    fn check(&self, assoc: AssocStruct) -> bool { true }
}

pub fn named(s: AssocStruct) {}
"#;

fn holds_call(receiver: &str) -> PureExpr {
    PureExpr::MethodCall {
        receiver: Arc::new(var(receiver)),
        method: "holds".to_string(),
        args: Vec::new(),
    }
}

/// The trait's clause at the impl is the declaration its bound names, read in
/// the trait's scope and instantiated by rustc's instance resolution: the
/// blanket impl. A lookup on `AssocStruct` sees the inherent method and
/// `Other`'s, and neither is what the trait promised.
#[test]
fn a_trait_clause_at_an_impl_is_the_instance_its_declaration_selects() {
    probe("tw_trait_clause_blanket", BLANKET_CLAUSE_SOURCE, |tcx| {
        let family = families_for(tcx, "tw_trait_clause_blanket", "holds");
        let blanket = member(&family, "<T as AssocTrait>::holds").id.clone();
        let resolved = super::resolve_trait_clause_at_impl(
            tcx,
            def_id_of(tcx, "Trait::check"),
            def_id_of(tcx, "<Struct as Trait>::check"),
            &holds_call("assoc"),
            &ClauseRef::HandLookupUnderTest,
        );
        assert_eq!(call_names(&resolved), vec![blanket]);
    });
}

/// `AssocTrait::holds(s)` names the trait: the one `AssocTrait` impl that
/// applies at `AssocStruct` (the blanket one), never the inherent `holds` or
/// `Other`'s, which a receiver-style lookup over the whole family would see.
#[test]
fn a_call_through_a_named_trait_is_that_trait_s_impl() {
    probe("tw_named_trait_call", BLANKET_CLAUSE_SOURCE, |tcx| {
        let family = families_for(tcx, "tw_named_trait_call", "holds");
        let blanket = member(&family, "<T as AssocTrait>::holds").id.clone();
        let other = member(&family, "<AssocStruct as Other>::holds").id.clone();
        let call = |name: &str| PureExpr::LogicFnCall {
            name: name.to_string(),
            args: vec![var("s")],
        };
        let owner = def_id_of(tcx, "named");
        assert_eq!(
            call_names(&resolve_logic_fn_paths_in_scope(
                tcx,
                owner,
                &call("AssocTrait::holds"),
                ClausePosition::Signature,
                &ClauseRef::HandLookupUnderTest,
            )),
            vec![blanket]
        );
        assert_eq!(
            call_names(&resolve_logic_fn_paths_in_scope(
                tcx,
                owner,
                &call("Other::holds"),
                ClausePosition::Signature,
                &ClauseRef::HandLookupUnderTest,
            )),
            vec![other]
        );
        assert_eq!(
            call_names(&resolve_logic_fn_paths_in_scope(
                tcx,
                owner,
                &holds_call("s"),
                ClausePosition::Signature,
                &ClauseRef::HandLookupUnderTest,
            )),
            vec!["<unresolved>::holds".to_string()],
            "a method call at `AssocStruct` has three candidates and refuses"
        );
    });
}

/// Two modules each declare a logic `k`; a trait's clause names `a::k(x)`
/// and calls `x.holds()` on a receiver whose `holds` has one definition.
const TRAIT_CLAUSE_PATH_SOURCE: &str = r#"
pub mod a {
    #[doc = "trust-wp:logic:"]
    pub fn k(x: i64) -> bool { true }
}

pub mod b {
    #[doc = "trust-wp:logic:"]
    pub fn k(x: i64) -> bool { false }
}

pub struct V;
impl V {
    #[doc = "trust-wp:logic:"]
    pub fn holds(self) -> bool { true }
}

pub struct U;
impl U {
    #[doc = "trust-wp:logic:"]
    pub fn holds(self) -> bool { false }
}

pub trait Tr {
    fn m(&self, x: i64, v: V) -> bool;
}

pub struct S;
impl Tr for S {
    fn m(&self, x: i64, v: V) -> bool { true }
}
"#;

/// A trait clause read at an impl resolves its method calls in the trait's
/// scope and leaves a path call as written, for the refinement's scope
/// closure to refuse: the module lookup a path would be read by cannot see a
/// block's own items, while the trait's own verification does read the path.
#[test]
fn a_path_call_in_a_trait_clause_at_an_impl_is_left_as_written() {
    probe("tw_trait_clause_path", TRAIT_CLAUSE_PATH_SOURCE, |tcx| {
        let holds = families_for(tcx, "tw_trait_clause_path", "holds");
        let v_holds = member(&holds, "V::holds").id.clone();
        let ks = families_for(tcx, "tw_trait_clause_path", "k");
        let a_k = member(&ks, "a::k").id.clone();
        let clause = PureExpr::BinOp(
            Arc::new(PureExpr::LogicFnCall {
                name: "a::k".to_string(),
                args: vec![var("x")],
            }),
            BinOp::And,
            Arc::new(holds_call("v")),
        );
        let trait_method = def_id_of(tcx, "Tr::m");
        let at_impl = super::resolve_trait_clause_at_impl(
            tcx,
            trait_method,
            def_id_of(tcx, "<S as Tr>::m"),
            &clause,
            &ClauseRef::HandLookupUnderTest,
        );
        assert_eq!(
            call_names(&at_impl),
            vec!["a::k".to_string(), v_holds.clone()]
        );
        assert_eq!(
            call_names(&resolve_logic_fn_paths_in_scope(
                tcx,
                trait_method,
                &clause,
                ClausePosition::Signature,
                &ClauseRef::HandLookupUnderTest,
            )),
            vec![a_k, v_holds],
            "the trait's own reading resolves the path"
        );
    });
}

/// `Other::holds(s)` written in a function declared inside a body is read
/// through the block scopes around it first (D-208): with no trait of that
/// name in a block, it is the module's `Other`, as at module level; where the
/// body around it declares its own `Other`, D-174 withholds the name before
/// the block lookup runs (D-213) and the call is refused (D-214), never the
/// module's.
#[test]
fn a_call_through_a_named_trait_inside_a_body_reads_the_block_scopes() {
    const SOURCE: &str = r#"
pub trait Other {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool;
}

pub struct S;
impl Other for S {
    #[doc = "trust-wp:logic:"]
    fn holds(self) -> bool { true }
}

pub struct U;
impl U {
    #[doc = "trust-wp:logic:"]
    pub fn holds(self) -> bool { false }
}

pub fn outer(s: S) {}

pub fn host() {
    pub fn inner(s: S) {}
}

pub fn shadow() {
    pub trait Other {
        #[doc = "trust-wp:logic:"]
        fn holds(self) -> bool;
    }
    impl Other for S {
        #[doc = "trust-wp:logic:"]
        fn holds(self) -> bool { false }
    }
    pub fn inner(s: S) {}
}
"#;
    probe("tw_named_trait_in_body", SOURCE, |tcx| {
        let family = families_for(tcx, "tw_named_trait_in_body", "holds");
        let other = member(&family, "<S as Other>::holds").id.clone();
        member(&family, "<S as shadow::Other>::holds");
        let call = PureExpr::LogicFnCall {
            name: "Other::holds".to_string(),
            args: vec![var("s")],
        };
        let at = |owner: &str| {
            call_names(&resolve_logic_fn_paths_in_scope(
                tcx,
                def_id_of(tcx, owner),
                &call,
                ClausePosition::Signature,
                &ClauseRef::HandLookupUnderTest,
            ))
        };
        assert_eq!(at("outer"), vec![other.clone()]);
        assert_eq!(at("host::inner"), vec![other]);
        // `shadow`'s body declares `Other`, and D-174's withholding answers
        // before the block lookup would find it (D-213); the method-style
        // call it withholds is refused (D-214).
        let refused = trust_wp_core::logic::identity::logic_fn_unresolved_marker("holds");
        let in_shadow = at("shadow::inner");
        assert!(
            matches!(in_shadow.as_slice(), [name] if name.starts_with(&refused)),
            "{in_shadow:?}"
        );
    });
}

// ---------------------------------------------------------------------------
// unit_struct_value_type
// ---------------------------------------------------------------------------

/// Unit structs with a colliding `tag`, next to every other kind of value a
/// bare path can name, and a nested module that imports a DIFFERENT `U`.
const UNIT_SOURCE: &str = r#"
pub struct U;
pub struct V;
pub struct P(pub i64);
pub struct G<const N: usize>;

impl U {
    #[doc = "trust-wp:logic:"]
    pub fn tag(self) -> i64 { 0 }
}

impl V {
    #[doc = "trust-wp:logic:"]
    pub fn tag(self) -> i64 { 1 }
}

impl P {
    #[doc = "trust-wp:logic:"]
    pub fn tag(self) -> i64 { 2 }
}

impl<const N: usize> G<N> {
    #[doc = "trust-wp:logic:"]
    pub fn tag(self) -> i64 { 3 }
}

pub const C: U = U;

pub fn root_owner() -> i64 { 0 }

pub fn shadowing_const_owner<const U: i64>() -> i64 { 0 }

pub fn renamed_const_owner<const N: i64>() -> i64 { 0 }

pub mod m {
    pub struct U;

    impl U {
        #[doc = "trust-wp:logic:"]
        pub fn tag(self) -> i64 { 4 }
    }

    pub mod inner {
        use super::U;

        pub fn inner_owner() -> i64 { 0 }
    }
}
"#;

/// Each unit struct value selects its OWN impl: the two calls spell the same
/// method on two receivers and must land on two definitions.
#[test]
fn a_unit_struct_value_types_its_receiver() {
    probe("tw_unit_value", UNIT_SOURCE, |tcx| {
        let family = families_for(tcx, "tw_unit_value", "tag");
        let u_tag = member(&family, "tw_unit_value::U::tag").id.clone();
        let v_tag = member(&family, "tw_unit_value::V::tag").id.clone();
        let owner = def_id_of(tcx, "root_owner");
        assert_eq!(
            call_names(&resolve_logic_fn_paths_in_scope(
                tcx,
                owner,
                &tag_call("U"),
                ClausePosition::Signature,
                &ClauseRef::HandLookupUnderTest
            )),
            vec![u_tag],
            "`U` is the unit struct `U`'s only value"
        );
        assert_eq!(
            call_names(&resolve_logic_fn_paths_in_scope(
                tcx,
                owner,
                &tag_call("V"),
                ClausePosition::Signature,
                &ClauseRef::HandLookupUnderTest
            )),
            vec![v_tag],
            "`V` is the unit struct `V`'s only value"
        );
    });
}

/// A bare path that names a value of a unit struct's type but is NOT its
/// constructor — a `const`, a tuple struct's constructor function, a struct
/// whose const argument the clause leaves to inference — is refused, not
/// typed from whatever the name happens to share.
#[test]
fn a_path_that_is_not_a_unit_struct_constructor_refuses() {
    probe("tw_unit_other_values", UNIT_SOURCE, |tcx| {
        let _family = families_for(tcx, "tw_unit_other_values", "tag");
        let owner = def_id_of(tcx, "root_owner");
        for name in ["C", "P", "G", "Nowhere"] {
            assert_eq!(
                call_names(&resolve_logic_fn_paths_in_scope(
                    tcx,
                    owner,
                    &tag_call(name),
                    ClausePosition::Signature,
                    &ClauseRef::HandLookupUnderTest
                )),
                vec!["<unresolved>::tag".to_string()],
                "`{name}` is not a unit struct constructor in scope"
            );
        }
    });
}

/// The name is resolved in the OWNER's module, `use` imports included: in
/// `m::inner`, `U` is the imported `m::U`, whose `tag` is not the root `U`'s.
#[test]
fn a_unit_struct_value_resolves_in_the_owners_module() {
    probe("tw_unit_scope", UNIT_SOURCE, |tcx| {
        let family = families_for(tcx, "tw_unit_scope", "tag");
        let root_u_tag = member(&family, "tw_unit_scope::U::tag").id.clone();
        let m_u_tag = member(&family, "m::U::tag").id.clone();
        assert_eq!(
            call_names(&resolve_logic_fn_paths_in_scope(
                tcx,
                def_id_of(tcx, "inner_owner"),
                &tag_call("U"),
                ClausePosition::Signature,
                &ClauseRef::HandLookupUnderTest
            )),
            vec![m_u_tag],
            "`m::inner` imports `m::U`"
        );
        assert_eq!(
            call_names(&resolve_logic_fn_paths_in_scope(
                tcx,
                def_id_of(tcx, "root_owner"),
                &tag_call("U"),
                ClausePosition::Signature,
                &ClauseRef::HandLookupUnderTest
            )),
            vec![root_u_tag],
            "the crate root's own `U`"
        );
    });
}

/// A clause binder spelled like a unit struct is the binder, with no Rust
/// type: the module's `U` must not type it.
#[test]
fn a_clause_binder_shadows_a_unit_struct() {
    probe("tw_unit_binder", UNIT_SOURCE, |tcx| {
        let _family = families_for(tcx, "tw_unit_binder", "tag");
        let quantified = PureExpr::Forall {
            var: "U".to_string(),
            var_sort: None,
            body: Arc::new(tag_call("U")),
            triggers: Vec::new(),
        };
        assert_eq!(
            call_names(&resolve_logic_fn_paths_in_scope(
                tcx,
                def_id_of(tcx, "root_owner"),
                &quantified,
                ClausePosition::Signature,
                &ClauseRef::HandLookupUnderTest
            )),
            vec!["<unresolved>::tag".to_string()],
            "the quantified `U` is not the unit struct"
        );
    });
}

/// A const generic parameter is a value in scope for the owner's clauses and
/// shadows the module's unit struct of that name; a const parameter under
/// another name does not.
#[test]
fn a_const_parameter_shadows_a_unit_struct() {
    probe("tw_unit_const_param", UNIT_SOURCE, |tcx| {
        let family = families_for(tcx, "tw_unit_const_param", "tag");
        let u_tag = member(&family, "tw_unit_const_param::U::tag").id.clone();
        assert_eq!(
            call_names(&resolve_logic_fn_paths_in_scope(
                tcx,
                def_id_of(tcx, "shadowing_const_owner"),
                &tag_call("U"),
                ClausePosition::Signature,
                &ClauseRef::HandLookupUnderTest
            )),
            vec!["<unresolved>::tag".to_string()],
            "`U` is the const parameter, not the unit struct"
        );
        assert_eq!(
            call_names(&resolve_logic_fn_paths_in_scope(
                tcx,
                def_id_of(tcx, "renamed_const_owner"),
                &tag_call("U"),
                ClausePosition::Signature,
                &ClauseRef::HandLookupUnderTest
            )),
            vec![u_tag],
            "the const parameter is `N`, so `U` is the unit struct"
        );
    });
}

// ---------------------------------------------------------------------------
// shadowed_by_body_item
// ---------------------------------------------------------------------------

/// Owners whose bodies redeclare a module-level name, and owners that do not.
/// A clause is type-checked at the head of its owner's body, so an item there
/// is what the clause's name means; the module's item of that name is not.
const SHADOW_SOURCE: &str = r#"
pub struct U;
pub struct V;

impl U {
    #[doc = "trust-wp:logic:"]
    pub fn tag(self) -> i64 { 0 }
}

impl V {
    #[doc = "trust-wp:logic:"]
    pub fn tag(self) -> i64 { 1 }
}

pub mod a {
    #[doc = "trust-wp:logic:"]
    pub fn k(p: i64) -> i64 { p }
}

pub mod b {
    #[doc = "trust-wp:logic:"]
    pub fn k(p: i64) -> i64 { p + 1 }
}

use a::k;

pub fn plain_owner(x: i64) -> i64 { x }

pub fn shadowing_owner(x: i64) -> i64 {
    struct U;
    fn k(p: i64) -> i64 { p + 2 }
    x
}

pub fn other_name_owner(x: i64) -> i64 {
    struct W;
    x
}

pub mod globbed {
    pub struct U;
    pub fn k(p: i64) -> i64 { p + 3 }
}

pub fn glob_owner(x: i64) -> i64 {
    use crate::globbed::*;
    x
}

pub fn cmp_star_import_owner(x: i64) -> i64 {
    use std::cmp::*;
    x
}

pub fn outer() -> i64 {
    struct U;
    fn nested_owner() -> i64 { 0 }
    nested_owner()
}
"#;

fn k_call(arg: &str) -> PureExpr {
    PureExpr::LogicFnCall {
        name: "k".to_string(),
        args: vec![var(arg)],
    }
}

/// The same two clauses in owners that differ only in what their bodies
/// declare: the module's answer stands where nothing redeclares the name (an
/// item of another name, a glob of a module without it), and is withheld where
/// something does — the owner's own body, a glob import of a module that has
/// the name, or the body of a function the owner is nested in.
#[test]
fn a_body_item_withholds_the_modules_answer_for_its_name() {
    probe("tw_body_shadow", SHADOW_SOURCE, |tcx| {
        let tags = families_for(tcx, "tw_body_shadow", "tag");
        let u_tag = member(&tags, "tw_body_shadow::U::tag").id.clone();
        let ks = families_for(tcx, "tw_body_shadow", "k");
        let a_k = member(&ks, "a::k").id.clone();
        let resolve = |owner: &str, expr: &PureExpr| {
            call_names(&resolve_logic_fn_paths_in_scope(
                tcx,
                def_id_of(tcx, owner),
                expr,
                ClausePosition::Signature,
                &ClauseRef::HandLookupUnderTest,
            ))
        };

        for owner in ["plain_owner", "other_name_owner", "cmp_star_import_owner"] {
            assert_eq!(
                resolve(owner, &tag_call("U")),
                vec![u_tag.clone()],
                "`{owner}` redeclares nothing named `U`"
            );
            assert_eq!(
                resolve(owner, &k_call("x")),
                vec![a_k.clone()],
                "`{owner}` redeclares nothing named `k`"
            );
        }
        for owner in ["shadowing_owner", "glob_owner"] {
            assert_eq!(
                resolve(owner, &tag_call("U")),
                vec!["<unresolved>::tag".to_string()],
                "`{owner}`'s body can declare its own `U`"
            );
            assert_eq!(
                resolve(owner, &k_call("x")),
                vec!["k".to_string()],
                "`{owner}`'s body can declare its own `k`"
            );
        }
        assert_eq!(
            resolve("nested_owner", &tag_call("U")),
            vec!["<unresolved>::tag".to_string()],
            "`outer`'s body declares the `U` its nested function's clauses see"
        );
    });
}
