// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Builder-output pins for the structural (subterm-descent) IH scheme.
//! The M0 encoder-level kill-gate lives in trust-wp-ay
//! (`verify/tests/structural_induction_m0.rs`); these tests pin WHAT the
//! builder emits and, more importantly, WHEN it must emit nothing.

use std::collections::HashMap;

use trust_wp_core::{
    formula::intern_sort_name,
    logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind, LogicMode},
};

use super::*;

fn var(n: &str) -> PureExpr {
    PureExpr::Var(n.to_string(), None)
}

fn list_sort_id() -> u32 {
    intern_sort_name("test::List")
}

fn list_sort() -> ExprSort {
    ExprSort::Datatype(list_sort_id())
}

fn list_adt_decls() -> AdtDecls {
    HashMap::from([(
        "List".to_string(),
        AdtDecl::new(
            "test::List".to_string(),
            "List".to_string(),
            AdtKind::Enum,
            vec![
                AdtConstructorDecl::new(
                    "Cons".to_string(),
                    "Cons".to_string(),
                    vec![
                        AdtFieldDecl::new("0".to_string(), ExprSort::Int),
                        AdtFieldDecl::new("1".to_string(), list_sort()),
                    ],
                ),
                AdtConstructorDecl::new("Nil".to_string(), "Nil".to_string(), vec![]),
            ],
        ),
    )])
}

fn cons_pattern(head: Pattern, tail: Pattern) -> Pattern {
    Pattern::Constructor {
        name: "Cons".to_string(),
        inner: Some(Box::new(Pattern::Tuple(vec![head, tail]))),
    }
}

fn nil_pattern() -> Pattern {
    Pattern::Constructor {
        name: "Nil".to_string(),
        inner: None,
    }
}

/// `fn len_logic(self: List) -> Int { match self { Cons(_, ls) => 1 + len_logic(ls), Nil => 0 } }`
/// with `#[ensures(result >= 0)]` and NO variant — the binary_search_list shape.
fn len_logic_def(call_args: Vec<PureExpr>) -> LogicFnDef {
    let body = PureExpr::Match {
        scrutinee: std::sync::Arc::new(PureExpr::Var("self".to_string(), Some(list_sort()))),
        arms: vec![
            trust_wp_core::formula::MatchArm {
                pattern: cons_pattern(Pattern::Wildcard, Pattern::Binding("ls".to_string())),
                body: super::super::binop(
                    PureExpr::Int(1),
                    BinOp::Add,
                    PureExpr::LogicFnCall {
                        name: "len_logic".to_string(),
                        args: call_args,
                    },
                ),
            },
            trust_wp_core::formula::MatchArm {
                pattern: nil_pattern(),
                body: PureExpr::Int(0),
            },
        ],
    };
    let mut def = LogicFnDef::new_with_requires(
        "len_logic".to_string(),
        "test::List::len_logic".to_string(),
        vec!["self".to_string()],
        vec![],
        body,
    )
    .with_param_sorts(vec![Some(list_sort())])
    .with_return_sort(Some(ExprSort::Int))
    .with_mode(LogicMode::Open)
    .detect_recursion();
    def.set_ensures(vec![super::super::binop(
        var("result"),
        BinOp::Ge,
        PureExpr::Int(0),
    )]);
    def
}

#[test]
fn len_logic_shape_emits_the_match_wrapped_ih() {
    let def = len_logic_def(vec![var("ls")]);
    let hyps = build_structural_induction_hypotheses(&def, Some(&list_adt_decls()));
    assert_eq!(
        hyps.len(),
        1,
        "exactly one self-call => one IH, got {hyps:?}"
    );
    let PureExpr::Match { scrutinee, arms } = &hyps[0] else {
        panic!("IH must be the match wrapper, got {:?}", hyps[0]);
    };
    assert_eq!(
        **scrutinee,
        PureExpr::Var("self".to_string(), Some(list_sort())),
        "wrapper must re-destructure the body's scrutinee (the parameter)"
    );
    assert_eq!(arms.len(), 2);
    assert_eq!(
        arms[0].pattern,
        cons_pattern(Pattern::Wildcard, Pattern::Binding("ls".to_string())),
        "wrapper arm must reuse the body arm's own pattern"
    );
    // Conclusion: ensures with self |-> ls, result |-> len_logic(ls):
    // `len_logic(ls) >= 0`.
    let expected = super::super::binop(
        PureExpr::LogicFnCall {
            name: "len_logic".to_string(),
            args: vec![var("ls")],
        },
        BinOp::Ge,
        PureExpr::Int(0),
    );
    assert_eq!(arms[0].body, expected, "IH conclusion mismatch");
    assert_eq!(arms[1].pattern, Pattern::Wildcard);
    assert_eq!(arms[1].body, PureExpr::Bool(true));
}

/// Deref-wrapped self-call argument (`len_logic(*ls)`, the Box deref form)
/// still descends: Deref layers are transparent.
#[test]
fn deref_wrapped_binder_argument_still_descends() {
    let def = len_logic_def(vec![PureExpr::Deref(std::sync::Arc::new(var("ls")))]);
    let hyps = build_structural_induction_hypotheses(&def, Some(&list_adt_decls()));
    assert_eq!(hyps.len(), 1, "Deref(ls) must still be the descent binder");
}

/// Recursion on the parameter ITSELF is circular — no IH, ever.
#[test]
fn self_argument_recursion_emits_nothing() {
    let def = len_logic_def(vec![PureExpr::Var("self".to_string(), Some(list_sort()))]);
    assert!(
        build_structural_induction_hypotheses(&def, Some(&list_adt_decls())).is_empty(),
        "f(self) is not a subterm call — the IH would be pure circularity"
    );
}

/// A rebuilt same-size term (`len_logic(Cons(h, ls))`-style constructor
/// application) is not a bare descent binder — no IH.
#[test]
fn rebuilt_constructor_argument_emits_nothing() {
    let def = len_logic_def(vec![PureExpr::LogicFnCall {
        name: "Cons".to_string(),
        args: vec![PureExpr::Int(7), var("ls")],
    }]);
    assert!(
        build_structural_induction_hypotheses(&def, Some(&list_adt_decls())).is_empty(),
        "a constructor application is not a strict subterm"
    );
}

/// Without ADT declarations there is no field-sort evidence — no IH.
#[test]
fn missing_adt_decls_emits_nothing() {
    let def = len_logic_def(vec![var("ls")]);
    assert!(build_structural_induction_hypotheses(&def, None).is_empty());
}

/// A binder at a NON-recursive field position (the Int head) must not grant
/// descent: substituting it into the ADT position would be ill-sorted and
/// unjustified.
#[test]
fn non_recursive_field_binder_emits_nothing() {
    // match self { Cons(h, _) => 1 + len_logic(h), Nil => 0 }
    let body = PureExpr::Match {
        scrutinee: std::sync::Arc::new(PureExpr::Var("self".to_string(), Some(list_sort()))),
        arms: vec![
            trust_wp_core::formula::MatchArm {
                pattern: cons_pattern(Pattern::Binding("h".to_string()), Pattern::Wildcard),
                body: super::super::binop(
                    PureExpr::Int(1),
                    BinOp::Add,
                    PureExpr::LogicFnCall {
                        name: "len_logic".to_string(),
                        args: vec![var("h")],
                    },
                ),
            },
            trust_wp_core::formula::MatchArm {
                pattern: nil_pattern(),
                body: PureExpr::Int(0),
            },
        ],
    };
    let mut def = LogicFnDef::new_with_requires(
        "len_logic".to_string(),
        "test::List::len_logic".to_string(),
        vec!["self".to_string()],
        vec![],
        body,
    )
    .with_param_sorts(vec![Some(list_sort())])
    .with_return_sort(Some(ExprSort::Int))
    .with_mode(LogicMode::Open)
    .detect_recursion();
    def.set_ensures(vec![super::super::binop(
        var("result"),
        BinOp::Ge,
        PureExpr::Int(0),
    )]);
    assert!(
        build_structural_induction_hypotheses(&def, Some(&list_adt_decls())).is_empty(),
        "the Int head field must not grant an ADT descent fact"
    );
}

/// An alias binder (`whole @ Cons(..)`) denotes the WHOLE scrutinee — no
/// descent fact, no IH.
#[test]
fn alias_binder_emits_nothing() {
    let body = PureExpr::Match {
        scrutinee: std::sync::Arc::new(PureExpr::Var("self".to_string(), Some(list_sort()))),
        arms: vec![
            trust_wp_core::formula::MatchArm {
                pattern: Pattern::Alias {
                    alias: "whole".to_string(),
                    pattern: Box::new(cons_pattern(Pattern::Wildcard, Pattern::Wildcard)),
                },
                body: PureExpr::LogicFnCall {
                    name: "len_logic".to_string(),
                    args: vec![var("whole")],
                },
            },
            trust_wp_core::formula::MatchArm {
                pattern: Pattern::Wildcard,
                body: PureExpr::Int(0),
            },
        ],
    };
    let mut def = LogicFnDef::new_with_requires(
        "len_logic".to_string(),
        "test::List::len_logic".to_string(),
        vec!["self".to_string()],
        vec![],
        body,
    )
    .with_param_sorts(vec![Some(list_sort())])
    .with_mode(LogicMode::Open)
    .detect_recursion();
    def.set_ensures(vec![super::super::binop(
        var("result"),
        BinOp::Ge,
        PureExpr::Int(0),
    )]);
    assert!(
        build_structural_induction_hypotheses(&def, Some(&list_adt_decls())).is_empty(),
        "an alias binder is the whole value, not a subterm"
    );
}

/// A match on a BINDER that shadows a parameter name must not be misread as a
/// match on the parameter (the shadowed-scrutinee guard).
#[test]
fn match_on_binder_shadowing_param_name_emits_nothing() {
    // fn f(self: List, aux: List)
    //   match self { Cons(_, aux) =>            // binder shadows param `aux`
    //     match aux { Cons(_, ls) => f(self, ls), .. } // NOT a match on param aux
    //   .. }
    // The inner match destructures the BINDER aux (a List-sorted field), so a
    // descent fact for `ls` rooted at PARAM position 1 would be unsound-ish
    // bookkeeping (the fact would claim descent from the parameter `aux`).
    let inner = PureExpr::Match {
        scrutinee: std::sync::Arc::new(var("aux")),
        arms: vec![
            trust_wp_core::formula::MatchArm {
                pattern: cons_pattern(Pattern::Wildcard, Pattern::Binding("ls".to_string())),
                body: PureExpr::LogicFnCall {
                    name: "f".to_string(),
                    args: vec![
                        PureExpr::Var("self".to_string(), Some(list_sort())),
                        var("ls"),
                    ],
                },
            },
            trust_wp_core::formula::MatchArm {
                pattern: Pattern::Wildcard,
                body: PureExpr::Int(0),
            },
        ],
    };
    let body = PureExpr::Match {
        scrutinee: std::sync::Arc::new(PureExpr::Var("self".to_string(), Some(list_sort()))),
        arms: vec![
            trust_wp_core::formula::MatchArm {
                // Cons(_, aux): binder `aux` shadows the parameter `aux`, and
                // is itself a List field — but the INNER match is on the
                // binder, not the parameter.
                pattern: cons_pattern(Pattern::Wildcard, Pattern::Binding("aux".to_string())),
                body: inner,
            },
            trust_wp_core::formula::MatchArm {
                pattern: Pattern::Wildcard,
                body: PureExpr::Int(0),
            },
        ],
    };
    let mut def = LogicFnDef::new_with_requires(
        "f".to_string(),
        "test::f".to_string(),
        vec!["self".to_string(), "aux".to_string()],
        vec![],
        body,
    )
    .with_param_sorts(vec![Some(list_sort()), Some(list_sort())])
    .with_return_sort(Some(ExprSort::Int))
    .with_mode(LogicMode::Open)
    .detect_recursion();
    def.set_ensures(vec![super::super::binop(
        var("result"),
        BinOp::Ge,
        PureExpr::Int(0),
    )]);
    // The outer arm DOES grant a descent fact for the binder `aux` (it is a
    // genuine subterm of param `self` at position 0). But the self-call's
    // args are (self, ls): position 0 arg `self` is no descent binder;
    // position 1 arg `ls` carries a fact ONLY if the inner match were
    // (wrongly) treated as destructuring param aux. With the shadowed guard
    // the inner match grants nothing, so no site is collected.
    assert!(
        build_structural_induction_hypotheses(&def, Some(&list_adt_decls())).is_empty(),
        "a shadowed scrutinee name must not be treated as the parameter"
    );
}

/// `&mut` induction parameters are rejected (prophecy-carrying).
#[test]
fn mut_ref_param_emits_nothing() {
    let mut def = len_logic_def(vec![var("ls")]);
    def = def.with_param_sorts(vec![Some(ExprSort::MutRef(Box::new(list_sort())))]);
    assert!(
        build_structural_induction_hypotheses(&def, Some(&list_adt_decls())).is_empty(),
        "a &mut parameter must not drive structural induction"
    );
}

/// Shared-reference parameters are transparent (the lemma_sum_nonneg shape):
/// `fn lemma(self: &List) #[ensures(sum(self) >= 0)]`
/// `{ match self { Cons(_, l) => lemma(l), Nil => () } }`.
#[test]
fn shared_ref_param_unit_lemma_emits_the_ih() {
    let body = PureExpr::Match {
        scrutinee: std::sync::Arc::new(PureExpr::Var(
            "self".to_string(),
            Some(ExprSort::Ref(Box::new(list_sort()))),
        )),
        arms: vec![
            trust_wp_core::formula::MatchArm {
                pattern: cons_pattern(Pattern::Wildcard, Pattern::Binding("l".to_string())),
                body: PureExpr::LogicFnCall {
                    name: "lemma_sum_nonneg".to_string(),
                    args: vec![var("l")],
                },
            },
            trust_wp_core::formula::MatchArm {
                pattern: nil_pattern(),
                body: PureExpr::Bool(true),
            },
        ],
    };
    let mut def = LogicFnDef::new_with_requires(
        "lemma_sum_nonneg".to_string(),
        "test::List::lemma_sum_nonneg".to_string(),
        vec!["self".to_string()],
        vec![],
        body,
    )
    .with_param_sorts(vec![Some(ExprSort::Ref(Box::new(list_sort())))])
    .with_return_sort(Some(ExprSort::Unit))
    .with_mode(LogicMode::Open)
    .detect_recursion();
    def.set_ensures(vec![super::super::binop(
        PureExpr::LogicFnCall {
            name: "sum".to_string(),
            args: vec![PureExpr::Var("self".to_string(), None)],
        },
        BinOp::Ge,
        PureExpr::Int(0),
    )]);
    let hyps = build_structural_induction_hypotheses(&def, Some(&list_adt_decls()));
    assert_eq!(hyps.len(), 1, "the lemma shape must produce one IH");
    // Conclusion: sum(l) >= 0 (self |-> l; unit lemma, result substitution inert).
    let PureExpr::Match { arms, .. } = &hyps[0] else {
        panic!("expected match wrapper");
    };
    let expected = super::super::binop(
        PureExpr::LogicFnCall {
            name: "sum".to_string(),
            args: vec![var("l")],
        },
        BinOp::Ge,
        PureExpr::Int(0),
    );
    assert_eq!(arms[0].body, expected);
}

/// A struct-kind ADT (no native enum constructors to guard on) is rejected.
#[test]
fn struct_kind_adt_emits_nothing() {
    let mut decls = list_adt_decls();
    decls.get_mut("List").unwrap().kind = AdtKind::Struct;
    let def = len_logic_def(vec![var("ls")]);
    assert!(build_structural_induction_hypotheses(&def, Some(&decls)).is_empty());
}

/// The variant-declared path is untouched: a declared `#[variant]` routes to
/// the integer-measure scheme and never to the structural one (pinned at the
/// dispatcher level by the parent module's tests; re-checked here through the
/// public entry).
#[test]
fn declared_variant_routes_to_integer_scheme_not_structural() {
    let mut def = len_logic_def(vec![var("ls")]);
    def = def.with_variants(vec![var("self")]); // a non-integer variant measure
    let hyps = super::super::build_recursive_induction_hypotheses(&def, Some(&list_adt_decls()));
    assert!(
        hyps.is_empty(),
        "a declared non-integer variant must fail the integer gate WITHOUT \
         falling back to the structural scheme (the user's measure is their \
         termination claim); got {hyps:?}"
    );
}
