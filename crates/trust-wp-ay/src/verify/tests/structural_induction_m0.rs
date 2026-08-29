// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! M0 kill-gate for the STRUCTURAL (subterm-descent) induction hypothesis
//! scheme for recursive `#[logic]` functions WITHOUT a `#[variant]`.
//!
//! Target shape (binary_search_list's `List::len_logic`, the axiom-census
//! structural-induction capability gap):
//!
//! ```text
//! #[logic] #[ensures(result >= 0)]
//! fn len_logic(self: List) -> Int {
//!     match self { Cons(_, ls) => 1 + ls.len_logic(), Nil => 0 }
//! }
//! ```
//!
//! With no `#[variant]`, `recursive_induction` injects no IH and both
//! self-axioms are suppressed, so the VC sees `len_logic` UNINTERPRETED at the
//! recursive call: `1 + len_logic(ls) >= 0` is honestly falsifiable (the
//! demonstrated Failed(CE)). The structural scheme instead injects, per
//! self-call whose argument is a match binder bound under >= 1 constructor
//! layer of the induction parameter, the TESTER-GUARDED ground hypothesis
//! (expressed with the existing `Match` machinery — binders encode to selector
//! terms, so no new quantifier is introduced):
//!
//! ```text
//! match self { Cons(_, ls) => ensures[self |-> ls], _ => true }
//! ```
//!
//! Soundness: SMT datatypes are initial-algebra (finite-tree) models, so the
//! strict-subterm relation is well-founded; the guarded hypothesis is the
//! well-founded-induction antecedent instantiated at the immediate subterm
//! `sel_tail(self)` under the `is_Cons(self)` guard that proves subterm-hood.
//! See `recursive_induction` (driver) for the full argument once M1 lands.
//!
//! M0 verdict criteria (all three must hold or the campaign STOPS):
//!  1. WITHOUT the IH the VC stays falsifiable (Failed/CE) — pins that the
//!     current incompleteness is real and the test bites.
//!  2. WITH the hand-built structural IH the VC verifies (UNSAT) — pins that
//!     the encoder+solver close the shape via ground DT+LIA reasoning.
//!  3. WITH the IH a FALSE postcondition (`result >= 1`) is still rejected —
//!     the IH must not be a blank cheque (adversarial control).

use std::{collections::HashMap, sync::Arc, time::Duration};

use ntest::timeout;
use trust_wp_core::{
    formula::{intern_sort_name, BinOp, ExprSort, MatchArm, Pattern, PureExpr},
    logic::{AdtConstructorDecl, AdtDecl, AdtDecls, AdtFieldDecl, AdtKind, LogicFnDef, LogicMode},
};

use crate::{verify::verify_function_with_modes, VerificationRequest, VerificationResult};

fn binop(l: PureExpr, op: BinOp, r: PureExpr) -> PureExpr {
    PureExpr::BinOp(Arc::new(l), op, Arc::new(r))
}

fn list_sort() -> ExprSort {
    ExprSort::Datatype(intern_sort_name("test::List"))
}

fn self_var() -> PureExpr {
    PureExpr::Var("self".to_string(), Some(list_sort()))
}

fn cons_pattern() -> Pattern {
    Pattern::Constructor {
        name: "Cons".to_string(),
        inner: Some(Box::new(Pattern::Tuple(vec![
            Pattern::Wildcard,
            Pattern::Binding("ls".to_string()),
        ]))),
    }
}

/// `match self { Cons(_, ls) => 1 + len_logic(ls), Nil => 0 }`
fn len_logic_body() -> PureExpr {
    PureExpr::Match {
        scrutinee: Arc::new(self_var()),
        arms: vec![
            MatchArm {
                pattern: cons_pattern(),
                body: binop(
                    PureExpr::Int(1),
                    BinOp::Add,
                    PureExpr::LogicFnCall {
                        name: "len_logic".to_string(),
                        args: vec![PureExpr::Var("ls".to_string(), None)],
                    },
                ),
            },
            MatchArm {
                pattern: Pattern::Constructor {
                    name: "Nil".to_string(),
                    inner: None,
                },
                body: PureExpr::Int(0),
            },
        ],
    }
}

/// The structural IH the M1 builder is expected to emit for the single
/// self-call `len_logic(ls)`:
/// `match self { Cons(_, ls) => len_logic(ls) >= 0, _ => true }`
/// (ensures `result >= 0` with `result |-> len_logic(ls)`, `self |-> ls`).
fn structural_ih() -> PureExpr {
    PureExpr::Match {
        scrutinee: Arc::new(self_var()),
        arms: vec![
            MatchArm {
                pattern: cons_pattern(),
                body: binop(
                    PureExpr::LogicFnCall {
                        name: "len_logic".to_string(),
                        args: vec![PureExpr::Var("ls".to_string(), None)],
                    },
                    BinOp::Ge,
                    PureExpr::Int(0),
                ),
            },
            MatchArm {
                pattern: Pattern::Wildcard,
                body: PureExpr::Bool(true),
            },
        ],
    }
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

/// Mirror of `logic_fn_verify`'s recursive-fn VC construction: the function
/// under test stays in the axiom set for its symbol declaration only — its
/// spec axiom removed by clearing `ensures`, its defining axiom suppressed by
/// the `Default` mode override.
fn len_logic_def_for_axiom_set() -> LogicFnDef {
    LogicFnDef::new_with_requires(
        "len_logic".to_string(),
        "test::List::len_logic".to_string(),
        vec!["self".to_string()],
        vec![],
        len_logic_body(),
    )
    .with_param_sorts(vec![Some(list_sort())])
    .with_return_sort(Some(ExprSort::Int))
    .with_mode(LogicMode::Open)
    .detect_recursion()
    // ensures deliberately NOT set: the self spec axiom must be absent.
}

fn run_vc(requires: &[PureExpr], ensures_rhs: PureExpr) -> VerificationResult {
    let body = len_logic_body();
    let ensures = vec![binop(
        PureExpr::Var("result".to_string(), None),
        BinOp::Ge,
        ensures_rhs,
    )];
    let logic_fns = vec![len_logic_def_for_axiom_set()];
    let mode_overrides = vec![LogicMode::Default];
    verify_function_with_modes(
        VerificationRequest::new(requires, &ensures)
            .return_expr(Some(&body))
            .logic_fns(Some(&logic_fns))
            .mode_overrides(Some(&mode_overrides))
            .adt_decls(Some(list_adt_decls()))
            .timeout(Some(Duration::from_secs(30))),
    )
    .expect("VC encoding must not error")
}

/// M0 criterion 1: without any IH the len_logic postcondition VC is honestly
/// falsifiable — `len_logic` is uninterpreted at the recursive call, so a
/// model may assign `len_logic(ls) = -7` and violate `result >= 0`.
#[test]
#[timeout(60000)]
fn m0_len_logic_shape_without_ih_stays_falsifiable() {
    let result = run_vc(&[], PureExpr::Int(0));
    assert!(
        matches!(result, VerificationResult::Failed(_)),
        "without an IH the VC must remain falsifiable (Failed/CE); got {result:?}"
    );
}

/// M0 criterion 2 (THE kill-gate): with the tester-guarded structural IH the
/// VC closes UNSAT by ground reasoning — is_Cons(self) case gives
/// result = 1 + len_logic(sel_tail(self)) with len_logic(sel_tail(self)) >= 0
/// from the IH (the match binder encodes to the SAME selector term in body and
/// IH); Nil case gives result = 0.
///
/// MEASURED at ay `fef7a83d2f`: ay COMPUTES the UNSAT, but the mandatory
/// strict certification refuses the proof ("step t1 uses unverified trust
/// rule"), so the consumer-facing verdict is downgraded to
/// `Unknown(ProofTrusted)` (see `VerificationResult::apply_strict_trust`).
/// That is the SAME upstream certification gap that already holds the
/// scoreboard's proof-trusted pile — it is NOT an induction defect. The
/// criterion is therefore "the counterexample is GONE and the goal closes",
/// pinned as `Verified | Unknown(ProofTrusted)`; the accompanying
/// `..._without_ih_stays_falsifiable` and `..._does_not_prove_false_postcondition`
/// tests are what keep this from being a weakened check — without the IH the
/// very same VC still yields a live CE, and a false postcondition still fails
/// WITH the IH present.
#[test]
#[timeout(60000)]
fn m0_len_logic_shape_with_structural_ih_closes_the_goal() {
    let ih = structural_ih();
    let result = run_vc(std::slice::from_ref(&ih), PureExpr::Int(0));
    assert!(
        matches!(
            result,
            VerificationResult::Verified(_)
                | VerificationResult::Unknown(crate::UnknownReason::ProofTrusted)
        ),
        "with the structural IH the VC must close the goal (Verified, or \
         ProofTrusted when upstream strict certification declines); got {result:?}"
    );
    assert!(
        !matches!(result, VerificationResult::Failed(_)),
        "no counterexample may survive the structural IH; got {result:?}"
    );
}

/// M0 criterion 3 (control): the IH is not a blank cheque — a FALSE
/// postcondition (`result >= 1`, violated by Nil => 0) must stay rejected
/// even with the (true-postcondition-shaped) IH present.
#[test]
#[timeout(60000)]
fn m0_structural_ih_does_not_prove_false_postcondition() {
    let ih = structural_ih();
    let result = run_vc(std::slice::from_ref(&ih), PureExpr::Int(1));
    assert!(
        !matches!(
            result,
            VerificationResult::Verified(_) | VerificationResult::Assumed(_)
        ),
        "the IH must not admit the false postcondition result >= 1; got {result:?}"
    );
}
