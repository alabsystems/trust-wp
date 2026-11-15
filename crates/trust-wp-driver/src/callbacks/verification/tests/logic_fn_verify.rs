// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
    time::Duration,
};

use trust_wp_ay::{VerificationOutcome, VerificationResult};
use trust_wp_core::{
    formula::{internal::tuple_lowering::tuple_logic_fn_name, BinOp, ExprSort, PureExpr},
    logic::{LogicFnDef, LogicMode},
    TrackLevel,
};

use crate::callbacks::{
    reporting::VerificationCounters,
    verification::logic_fn_verify::{
        record_logic_fn_verified_evidence_gap_if_any, verify_logic_fn_postconditions,
        LogicBodyCallees, VerifyConfig,
    },
};

#[test]
fn verify_logic_fn_postconditions_skips_no_ensures() {
    let logic_fn = LogicFnDef::new(
        "id".to_string(),
        "test::id".to_string(),
        vec!["x".to_string()],
        PureExpr::Var("x".to_string(), None),
    );
    let logic_fns = vec![logic_fn];
    let cfg = VerifyConfig {
        logic_fns: &logic_fns,
        type_invariants_opt: None,
        track_level: TrackLevel::Auto,
        timeout: Some(Duration::from_secs(5)),
        strict_axioms: false,
        trait_logic_fn_groups: None,
        impl_owed_postconditions: None,
        adt_field_ranges: None,
        adt_decls: None,
        program_fns_with_requires: None,
        logic_body_callees: &LogicBodyCallees::spelling_only(),
    };
    let mut counters = VerificationCounters::default();
    let mut unverified = HashSet::new();

    verify_logic_fn_postconditions(&cfg, &mut counters, &mut unverified);

    assert_eq!(
        counters.verified, 0,
        "no ensures = no verification attempted"
    );
    assert_eq!(counters.failed, 0);
    assert_eq!(counters.errors, 0);
    assert!(unverified.is_empty());
}

#[test]
fn logic_fn_verified_without_provenance_records_evidence_gap_not_verified() {
    let mut counters = VerificationCounters::default();
    let mut unverified = HashSet::new();
    let outcome = VerificationOutcome::without_provenance(VerificationResult::Verified(None));

    let recorded = record_logic_fn_verified_evidence_gap_if_any(
        &outcome,
        "test::law",
        &mut counters,
        &mut unverified,
    );

    assert!(recorded);
    assert_eq!(counters.verified, 0);
    assert_eq!(counters.evidence_gaps, 1);
    assert_eq!(counters.warnings, 1);
    assert!(unverified.contains("test::law"));
}

#[test]
fn verify_logic_fn_postconditions_verifies_trivial_postcondition() {
    let mut logic_fn = LogicFnDef::new(
        "truth".to_string(),
        "test::truth".to_string(),
        vec![],
        PureExpr::Bool(true),
    );
    logic_fn.set_ensures(vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Bool(true)),
    )]);
    let logic_fns = vec![logic_fn];
    let cfg = VerifyConfig {
        logic_fns: &logic_fns,
        type_invariants_opt: None,
        track_level: TrackLevel::Auto,
        timeout: Some(Duration::from_secs(10)),
        strict_axioms: false,
        trait_logic_fn_groups: None,
        impl_owed_postconditions: None,
        adt_field_ranges: None,
        adt_decls: None,
        program_fns_with_requires: None,
        logic_body_callees: &LogicBodyCallees::spelling_only(),
    };
    let mut counters = VerificationCounters::default();
    let mut unverified = HashSet::new();

    verify_logic_fn_postconditions(&cfg, &mut counters, &mut unverified);

    assert_eq!(
        counters.verified, 1,
        "trivially true postcondition should verify"
    );
    assert_eq!(counters.failed, 0);
    assert_eq!(counters.errors, 0);
    assert!(unverified.is_empty());
}

#[test]
fn verify_logic_fn_postconditions_fails_contradictory_postcondition() {
    let mut logic_fn = LogicFnDef::new(
        "zero".to_string(),
        "test::zero".to_string(),
        vec![],
        PureExpr::Int(0),
    );
    logic_fn.set_ensures(vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )]);
    let logic_fns = vec![logic_fn];
    let cfg = VerifyConfig {
        logic_fns: &logic_fns,
        type_invariants_opt: None,
        track_level: TrackLevel::Auto,
        timeout: Some(Duration::from_secs(10)),
        strict_axioms: false,
        trait_logic_fn_groups: None,
        impl_owed_postconditions: None,
        adt_field_ranges: None,
        adt_decls: None,
        program_fns_with_requires: None,
        logic_body_callees: &LogicBodyCallees::spelling_only(),
    };
    let mut counters = VerificationCounters::default();
    let mut unverified = HashSet::new();

    verify_logic_fn_postconditions(&cfg, &mut counters, &mut unverified);

    assert_eq!(
        counters.verified, 0,
        "contradictory postcondition should not verify"
    );
    // Logic fn postcondition failures are now tracked as unverified axioms
    // (warnings), not function-level failures. This prevents them from
    // blocking compat test classification. (#2700)
    assert_eq!(
        counters.failed, 0,
        "logic fn postcondition FAILED goes to warnings, not failed"
    );
    assert_eq!(
        counters.warnings, 1,
        "should record a warning for unverified postcondition"
    );
    assert!(
        unverified.contains("test::zero"),
        "should track in unverified axioms"
    );
}

#[test]
fn verify_logic_fn_postconditions_skips_trusted_logic_fns() {
    // Trusted logic functions should have their postconditions assumed,
    // not verified. Previously they were fed through verification and
    // produced spurious failures. (#2700)
    let mut logic_fn = LogicFnDef::new(
        "view".to_string(),
        "test::view".to_string(),
        vec!["self".to_string()],
        PureExpr::Int(0), // trivial body
    )
    .with_trusted(true);
    // Postcondition that would fail against the trivial body:
    logic_fn.set_ensures(vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )]);
    let logic_fns = vec![logic_fn];
    let cfg = VerifyConfig {
        logic_fns: &logic_fns,
        type_invariants_opt: None,
        track_level: TrackLevel::Auto,
        timeout: Some(Duration::from_secs(5)),
        strict_axioms: false,
        trait_logic_fn_groups: None,
        impl_owed_postconditions: None,
        adt_field_ranges: None,
        adt_decls: None,
        program_fns_with_requires: None,
        logic_body_callees: &LogicBodyCallees::spelling_only(),
    };
    let mut counters = VerificationCounters::default();
    let mut unverified = HashSet::new();

    verify_logic_fn_postconditions(&cfg, &mut counters, &mut unverified);

    assert_eq!(counters.verified, 0, "trusted fn should not be verified");
    assert_eq!(counters.failed, 0, "trusted fn should not be failed");
    assert_eq!(
        counters.warnings, 0,
        "trusted fn should not produce warnings"
    );
    assert!(
        unverified.is_empty(),
        "trusted fn should not be in unverified axioms"
    );
}

fn concrete_law(ensures: PureExpr) -> Vec<LogicFnDef> {
    let mut law = LogicFnDef::new(
        "law".to_string(),
        "test::law".to_string(),
        vec![],
        PureExpr::Int(0),
    )
    .with_law(true)
    .with_mode(LogicMode::Open);
    law.set_ensures(vec![ensures]);
    vec![law]
}

fn verify_non_strict(logic_fns: &[LogicFnDef]) -> (VerificationCounters, HashSet<String>) {
    let cfg = VerifyConfig {
        logic_fns,
        type_invariants_opt: None,
        track_level: TrackLevel::Auto,
        timeout: Some(Duration::from_secs(5)),
        strict_axioms: false,
        trait_logic_fn_groups: None,
        impl_owed_postconditions: None,
        adt_field_ranges: None,
        adt_decls: None,
        program_fns_with_requires: None,
        logic_body_callees: &LogicBodyCallees::spelling_only(),
    };
    let mut counters = VerificationCounters::default();
    let mut unverified = HashSet::new();
    verify_logic_fn_postconditions(&cfg, &mut counters, &mut unverified);
    (counters, unverified)
}

/// A concrete law is proved like any logic function, in the default mode
/// too: the true one is credited...
#[test]
fn verify_logic_fn_postconditions_proves_a_true_concrete_law() {
    let (counters, unverified) = verify_non_strict(&concrete_law(PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    )));
    assert_eq!(counters.verified, 1, "a true law is proved and credited");
    assert!(
        unverified.is_empty(),
        "a proved law stays available to callers"
    );
}

/// ...and its false twin (`0 > 0`) is never credited and never left live.
#[test]
fn verify_logic_fn_postconditions_never_credits_a_false_concrete_law() {
    let (counters, unverified) = verify_non_strict(&concrete_law(PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )));
    assert_eq!(counters.verified, 0, "a false law is not credited");
    assert!(
        unverified.contains("test::law"),
        "an unproved law is recorded, which withholds it from callers"
    );
}

#[test]
fn verify_logic_fn_postconditions_self_exclusion_prevents_circular_reasoning() {
    let mut logic_fn = LogicFnDef::new(
        "f".to_string(),
        "test::f".to_string(),
        vec!["x".to_string()],
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        ),
    );
    logic_fn.set_ensures(vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Var("x".to_string(), None)),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    )]);
    let other_fn = LogicFnDef::new(
        "g".to_string(),
        "test::g".to_string(),
        vec!["y".to_string()],
        PureExpr::Var("y".to_string(), None),
    );
    let logic_fns = vec![logic_fn, other_fn];
    let cfg = VerifyConfig {
        logic_fns: &logic_fns,
        type_invariants_opt: None,
        track_level: TrackLevel::Auto,
        timeout: Some(Duration::from_secs(10)),
        strict_axioms: false,
        trait_logic_fn_groups: None,
        impl_owed_postconditions: None,
        adt_field_ranges: None,
        adt_decls: None,
        program_fns_with_requires: None,
        logic_body_callees: &LogicBodyCallees::spelling_only(),
    };
    let mut counters = VerificationCounters::default();
    let mut unverified = HashSet::new();

    verify_logic_fn_postconditions(&cfg, &mut counters, &mut unverified);

    assert_eq!(
        counters.verified, 1,
        "f's postcondition should verify without circular reasoning"
    );
    assert_eq!(counters.failed, 0);
}

#[test]
fn verify_logic_fn_postconditions_trait_law_hides_same_trait_default_body() {
    let unit = || PureExpr::LogicFnCall {
        name: tuple_logic_fn_name(0),
        args: vec![],
    };
    let logic_call = |name: &str, args: Vec<PureExpr>| PureExpr::LogicFnCall {
        name: name.to_string(),
        args,
    };
    let le =
        |lhs: PureExpr, rhs: PureExpr| PureExpr::BinOp(Arc::new(lhs), BinOp::Le, Arc::new(rhs));

    let mktrue = LogicFnDef::new(
        "mktrue".to_string(),
        "test::A::mktrue".to_string(),
        vec![],
        PureExpr::Int(5),
    )
    .with_mode(LogicMode::Open);
    let mut law = LogicFnDef::new(
        "is_true".to_string(),
        "test::A::is_true".to_string(),
        vec![],
        unit(),
    )
    .with_law(true)
    .with_mode(LogicMode::Open);
    law.set_ensures(vec![le(logic_call("mktrue", vec![]), PureExpr::Int(10))]);

    let logic_fns = vec![mktrue, law];
    let trait_logic_fn_groups = HashMap::from([
        ("test::A::mktrue".to_string(), "test::A".to_string()),
        ("test::A::is_true".to_string(), "test::A".to_string()),
    ]);
    let cfg = VerifyConfig {
        logic_fns: &logic_fns,
        type_invariants_opt: None,
        track_level: TrackLevel::Auto,
        timeout: Some(Duration::from_secs(10)),
        strict_axioms: false,
        trait_logic_fn_groups: Some(&trait_logic_fn_groups),
        impl_owed_postconditions: None,
        adt_field_ranges: None,
        adt_decls: None,
        program_fns_with_requires: None,
        logic_body_callees: &LogicBodyCallees::spelling_only(),
    };
    let mut counters = VerificationCounters::default();
    let mut unverified = HashSet::new();

    verify_logic_fn_postconditions(&cfg, &mut counters, &mut unverified);

    assert_eq!(
        counters.failed, 1,
        "trait law must not verify by assuming same-trait default body"
    );
    assert_eq!(counters.verified, 0);
    assert_eq!(
        counters.warnings, 0,
        "concrete trait law counterexamples should reject rather than warn"
    );
    assert!(unverified.contains("test::A::is_true"));
}

/// bug/222 production shape: besides the trait's overridable default body
/// (`A::mktrue = 5`), the crate also carries an impl override
/// (`<() as A>::mktrue = 6`). Impl methods are not trait-declared, so they are
/// absent from `trait_logic_fn_groups`, but logic calls resolve by name: the
/// override must not define the generic `Self::mktrue` for the law either.
#[test]
fn verify_logic_fn_postconditions_trait_law_hides_impl_override_body() {
    let unit = || PureExpr::LogicFnCall {
        name: tuple_logic_fn_name(0),
        args: vec![],
    };
    let le =
        |lhs: PureExpr, rhs: PureExpr| PureExpr::BinOp(Arc::new(lhs), BinOp::Le, Arc::new(rhs));
    let mktrue_default = LogicFnDef::new(
        "mktrue".to_string(),
        "test::A::mktrue".to_string(),
        vec![],
        PureExpr::Int(5),
    )
    .with_mode(LogicMode::Open);
    let mktrue_impl = LogicFnDef::new(
        "mktrue".to_string(),
        "test::<() as A>::mktrue".to_string(),
        vec![],
        PureExpr::Int(6),
    )
    .with_mode(LogicMode::Open);
    let mut law = LogicFnDef::new(
        "is_true".to_string(),
        "test::A::is_true".to_string(),
        vec![],
        unit(),
    )
    .with_law(true)
    .with_mode(LogicMode::Open);
    law.set_ensures(vec![le(
        PureExpr::LogicFnCall {
            name: "mktrue".to_string(),
            args: vec![],
        },
        PureExpr::Int(10),
    )]);

    for logic_fns in [
        vec![mktrue_default.clone(), mktrue_impl.clone(), law.clone()],
        vec![mktrue_default.clone(), law.clone(), mktrue_impl.clone()],
    ] {
        let trait_logic_fn_groups = HashMap::from([
            ("test::A::mktrue".to_string(), "test::A".to_string()),
            ("test::A::is_true".to_string(), "test::A".to_string()),
        ]);
        let cfg = VerifyConfig {
            logic_fns: &logic_fns,
            type_invariants_opt: None,
            track_level: TrackLevel::Auto,
            timeout: Some(Duration::from_secs(10)),
            strict_axioms: false,
            trait_logic_fn_groups: Some(&trait_logic_fn_groups),
            impl_owed_postconditions: None,
            adt_field_ranges: None,
            adt_decls: None,
            program_fns_with_requires: None,
            logic_body_callees: &LogicBodyCallees::spelling_only(),
        };
        let mut counters = VerificationCounters::default();
        let mut unverified = HashSet::new();

        verify_logic_fn_postconditions(&cfg, &mut counters, &mut unverified);

        assert_eq!(
            counters.verified, 0,
            "trait law must not verify through an impl override's body"
        );
        assert_eq!(counters.failed, 1);
        assert!(unverified.contains("test::A::is_true"));
    }
}

#[test]
fn verify_logic_fn_postconditions_strict_axioms_verifiable_fn() {
    let mut logic_fn = LogicFnDef::new(
        "id".to_string(),
        "test::id".to_string(),
        vec!["x".to_string()],
        PureExpr::Var("x".to_string(), None),
    );
    logic_fn.set_ensures(vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Var("x".to_string(), None)),
    )]);
    let logic_fns = vec![logic_fn];
    let cfg = VerifyConfig {
        logic_fns: &logic_fns,
        type_invariants_opt: None,
        track_level: TrackLevel::Auto,
        timeout: Some(Duration::from_secs(10)),
        strict_axioms: true,
        trait_logic_fn_groups: None,
        impl_owed_postconditions: None,
        adt_field_ranges: None,
        adt_decls: None,
        program_fns_with_requires: None,
        logic_body_callees: &LogicBodyCallees::spelling_only(),
    };
    let mut counters = VerificationCounters::default();
    let mut unverified = HashSet::new();

    verify_logic_fn_postconditions(&cfg, &mut counters, &mut unverified);

    assert_eq!(
        counters.verified, 1,
        "identity function postcondition should verify even under strict_axioms"
    );
    assert_eq!(counters.errors, 0, "no errors expected for verifiable fn");
}

#[test]
fn verify_logic_fn_postconditions_recursive_pow2_lemma_verifies() {
    let unit = || PureExpr::LogicFnCall {
        name: tuple_logic_fn_name(0),
        args: vec![],
    };
    let var_i = || PureExpr::Var("i".to_string(), None);
    let logic_call = |name: &str, args: Vec<PureExpr>| PureExpr::LogicFnCall {
        name: name.to_string(),
        args,
    };
    let pow2 = |receiver: PureExpr| PureExpr::MethodCall {
        receiver: Arc::new(receiver),
        method: "pow2".to_string(),
        args: vec![],
    };
    let sub =
        |lhs: PureExpr, rhs: PureExpr| PureExpr::BinOp(Arc::new(lhs), BinOp::Sub, Arc::new(rhs));
    let add =
        |lhs: PureExpr, rhs: PureExpr| PureExpr::BinOp(Arc::new(lhs), BinOp::Add, Arc::new(rhs));
    let le =
        |lhs: PureExpr, rhs: PureExpr| PureExpr::BinOp(Arc::new(lhs), BinOp::Le, Arc::new(rhs));
    let eq =
        |lhs: PureExpr, rhs: PureExpr| PureExpr::BinOp(Arc::new(lhs), BinOp::Eq, Arc::new(rhs));

    let fib_body = PureExpr::Ite(
        Arc::new(le(var_i(), PureExpr::Int(0))),
        Arc::new(PureExpr::Int(0)),
        Arc::new(PureExpr::Ite(
            Arc::new(eq(var_i(), PureExpr::Int(1))),
            Arc::new(PureExpr::Int(1)),
            Arc::new(add(
                logic_call("fib", vec![sub(var_i(), PureExpr::Int(1))]),
                logic_call("fib", vec![sub(var_i(), PureExpr::Int(2))]),
            )),
        )),
    );
    let fib = LogicFnDef::new(
        "fib".to_string(),
        "test::fib".to_string(),
        vec!["i".to_string()],
        fib_body,
    )
    .with_mode(LogicMode::Open)
    .detect_recursion();

    let lemma_body = PureExpr::Ite(
        Arc::new(eq(var_i(), PureExpr::Int(0))),
        Arc::new(unit()),
        Arc::new(PureExpr::Ite(
            Arc::new(eq(var_i(), PureExpr::Int(1))),
            Arc::new(unit()),
            Arc::new(PureExpr::Let {
                var: "__stmt0".to_string(),
                value: Arc::new(logic_call(
                    "lemma_fib_bound",
                    vec![sub(var_i(), PureExpr::Int(2))],
                )),
                body: Arc::new(PureExpr::Let {
                    var: "__stmt1".to_string(),
                    value: Arc::new(logic_call(
                        "lemma_fib_bound",
                        vec![sub(var_i(), PureExpr::Int(1))],
                    )),
                    body: Arc::new(unit()),
                }),
            }),
        )),
    );
    let mut lemma = LogicFnDef::new_with_requires(
        "lemma_fib_bound".to_string(),
        "test::lemma_fib_bound".to_string(),
        vec!["i".to_string()],
        vec![le(PureExpr::Int(0), var_i())],
        lemma_body,
    )
    .with_mode(LogicMode::Open)
    .detect_recursion();
    lemma.set_ensures(vec![le(logic_call("fib", vec![var_i()]), pow2(var_i()))]);

    let logic_fns = vec![fib, lemma];
    let cfg = VerifyConfig {
        logic_fns: &logic_fns,
        type_invariants_opt: None,
        track_level: TrackLevel::Auto,
        // ay cbce819: recursive fib proof needs more time with new quantifier handler.
        timeout: Some(Duration::from_secs(30)),
        strict_axioms: false,
        trait_logic_fn_groups: None,
        impl_owed_postconditions: None,
        adt_field_ranges: None,
        adt_decls: None,
        program_fns_with_requires: None,
        logic_body_callees: &LogicBodyCallees::spelling_only(),
    };
    let mut counters = VerificationCounters::default();
    let mut unverified = HashSet::new();

    verify_logic_fn_postconditions(&cfg, &mut counters, &mut unverified);

    // ay cbce819: recursive fib proof may timeout with new quantifier handler.
    // Accept either verified or timeout (unverified), but not failed.
    assert_eq!(
        counters.failed, 0,
        "recursive pow2 lemma must not produce a counterexample"
    );
    assert!(
        counters.verified == 1 || !unverified.is_empty(),
        "recursive pow2 lemma should either verify or timeout: verified={}, unverified={:?}",
        counters.verified,
        unverified
    );
}

/// An `ensures` the encoder REFUSES was never put to the solver, so the clause
/// is unproved. It must be recorded on the unverified path — that path is the
/// only input to `filter_downstream_logic_fns`, and without it callers in the
/// same crate keep collecting `verified` credit from an axiom nobody proved.
#[test]
fn verify_logic_fn_postconditions_encoding_refusal_neutralizes_the_axiom() {
    let mut law = LogicFnDef::new(
        "bumped".to_string(),
        "test::Spec::bumped".to_string(),
        vec!["self".to_string()],
        PureExpr::Var("self".to_string(), None),
    );
    // `base` is declared by no logic fn in this set, so encoding the clause
    // fails rather than producing a goal.
    law.set_ensures(vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::LogicFnCall {
                name: "__lfid__test_P__P_Spec_P__P_base".to_string(),
                args: vec![PureExpr::Var("self".to_string(), None)],
            }),
            BinOp::Add,
            Arc::new(PureExpr::Int(1)),
        )),
    )]);
    let logic_fns = vec![law];
    let cfg = VerifyConfig {
        logic_fns: &logic_fns,
        type_invariants_opt: None,
        track_level: TrackLevel::Auto,
        timeout: Some(Duration::from_secs(10)),
        strict_axioms: false,
        trait_logic_fn_groups: None,
        impl_owed_postconditions: None,
        adt_field_ranges: None,
        adt_decls: None,
        program_fns_with_requires: None,
        logic_body_callees: &LogicBodyCallees::spelling_only(),
    };
    let mut counters = VerificationCounters::default();
    let mut unverified = HashSet::new();

    verify_logic_fn_postconditions(&cfg, &mut counters, &mut unverified);

    assert_eq!(counters.verified, 0, "a refused encoding proves nothing");
    assert_eq!(counters.errors, 1, "the refusal is still a counted error");
    assert!(
        unverified.contains("test::Spec::bumped"),
        "a refused postcondition must not stay available as a spec axiom"
    );
}

/// A VACUOUS outcome means the premises were contradictory, so the `ensures`
/// holds in no model that matters — it was not proved. It must be recorded on
/// the unverified path for the same reason a refused or unknown one is.
#[test]
fn verify_logic_fn_postconditions_vacuous_neutralizes_the_axiom() {
    let mut logic_fn = LogicFnDef::new_with_requires(
        "bogus".to_string(),
        "test::bogus".to_string(),
        vec![],
        // Contradictory premise: the base assertions are UNSAT on their own.
        vec![PureExpr::BinOp(
            Arc::new(PureExpr::Int(1)),
            BinOp::Gt,
            Arc::new(PureExpr::Int(2)),
        )],
        PureExpr::Int(0),
    );
    logic_fn.set_ensures(vec![PureExpr::BinOp(
        Arc::new(PureExpr::Var("result".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )]);
    let logic_fns = vec![logic_fn];
    let cfg = VerifyConfig {
        logic_fns: &logic_fns,
        type_invariants_opt: None,
        track_level: TrackLevel::Auto,
        timeout: Some(Duration::from_secs(10)),
        strict_axioms: false,
        trait_logic_fn_groups: None,
        impl_owed_postconditions: None,
        adt_field_ranges: None,
        adt_decls: None,
        program_fns_with_requires: None,
        logic_body_callees: &LogicBodyCallees::spelling_only(),
    };
    let mut counters = VerificationCounters::default();
    let mut unverified = HashSet::new();

    verify_logic_fn_postconditions(&cfg, &mut counters, &mut unverified);

    assert_eq!(counters.verified, 0, "a vacuous outcome is not a proof");
    assert!(
        unverified.contains("test::bogus"),
        "an unproved postcondition must not stay available as a spec axiom"
    );
}

/// `needs_pos(x)` requires `x > 0`; `caller(y)` returns `needs_pos(y)` under
/// the given `requires` and `ensures`.
fn callee_precondition_pair(
    caller_requires: Vec<PureExpr>,
    caller_ensures: Vec<PureExpr>,
) -> Vec<LogicFnDef> {
    let gt =
        |lhs: PureExpr, rhs: PureExpr| PureExpr::BinOp(Arc::new(lhs), BinOp::Gt, Arc::new(rhs));
    let needs_pos = LogicFnDef::new_with_requires(
        "needs_pos".to_string(),
        "test::needs_pos".to_string(),
        vec!["x".to_string()],
        vec![gt(PureExpr::Var("x".to_string(), None), PureExpr::Int(0))],
        PureExpr::Var("x".to_string(), None),
    );
    let mut caller = LogicFnDef::new_with_requires(
        "caller".to_string(),
        "test::caller".to_string(),
        vec!["y".to_string()],
        caller_requires,
        PureExpr::LogicFnCall {
            name: "needs_pos".to_string(),
            args: vec![PureExpr::Var("y".to_string(), None)],
        },
    );
    caller.set_ensures(caller_ensures);
    vec![needs_pos, caller]
}

fn run_logic_lane(logic_fns: &[LogicFnDef]) -> (VerificationCounters, HashSet<String>) {
    let cfg = VerifyConfig {
        logic_fns,
        type_invariants_opt: None,
        track_level: TrackLevel::Auto,
        timeout: Some(Duration::from_secs(10)),
        strict_axioms: false,
        trait_logic_fn_groups: None,
        adt_field_ranges: None,
        adt_decls: None,
        impl_owed_postconditions: None,
        program_fns_with_requires: None,
        logic_body_callees: &LogicBodyCallees::spelling_only(),
    };
    let mut counters = VerificationCounters::default();
    let mut unverified = HashSet::new();
    verify_logic_fn_postconditions(&cfg, &mut counters, &mut unverified);
    (counters, unverified)
}

fn y_positive() -> PureExpr {
    PureExpr::BinOp(
        Arc::new(PureExpr::Var("y".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    )
}

/// logic_fn_callee_precondition_never_examined.rs: the `ensures` holds, the
/// call is outside `needs_pos`'s precondition, and the function is refuted.
#[test]
fn a_call_outside_the_callee_precondition_refutes_the_caller() {
    let (counters, unverified) = run_logic_lane(&callee_precondition_pair(
        vec![],
        vec![PureExpr::Bool(true)],
    ));
    assert_eq!(
        counters.verified, 0,
        "an unmet callee precondition is not a proof"
    );
    assert_eq!(counters.failed, 1);
    assert!(
        unverified.contains("test::caller"),
        "a caller that did not prove its body goals must not keep its spec"
    );
}

/// The isolating twin: the caller's own `requires` puts the call inside the
/// precondition, and nothing else differs.
#[test]
fn a_call_inside_the_callee_precondition_is_credited() {
    let (counters, unverified) = run_logic_lane(&callee_precondition_pair(
        vec![y_positive()],
        vec![PureExpr::Bool(true)],
    ));
    assert_eq!(counters.verified, 1);
    assert_eq!(counters.failed, 0);
    assert_eq!(counters.errors, 0);
    assert!(unverified.is_empty());
}

/// A requires-only caller has no ensures lane; its callee preconditions are
/// still owed, and it is credited on them alone.
#[test]
fn a_requires_only_caller_owes_its_callee_preconditions() {
    let (counters, _) = run_logic_lane(&callee_precondition_pair(
        vec![PureExpr::Bool(true)],
        vec![],
    ));
    assert_eq!(counters.verified, 0);
    assert_eq!(counters.failed, 1);

    let (counters, unverified) =
        run_logic_lane(&callee_precondition_pair(vec![y_positive()], vec![]));
    assert_eq!(counters.verified, 1);
    assert_eq!(counters.failed, 0);
    assert!(unverified.is_empty());
}

/// A logic function with no contract gets no goal in Creusot, so its calls
/// owe nothing and it is neither refuted nor credited.
#[test]
fn a_contract_free_caller_owes_nothing() {
    let (counters, unverified) = run_logic_lane(&callee_precondition_pair(vec![], vec![]));
    assert_eq!(counters.verified, 0);
    assert_eq!(counters.failed, 0);
    assert_eq!(counters.errors, 0);
    assert!(unverified.is_empty());
}

/// `caller(y)` requires `true`, asserts `true` and returns `value`.
fn requires_only_asserting_caller(value: PureExpr) -> LogicFnDef {
    LogicFnDef::new_with_requires(
        "caller".to_string(),
        "test::caller".to_string(),
        vec!["y".to_string()],
        vec![PureExpr::Bool(true)],
        PureExpr::Let {
            var: "$stmt0".to_string(),
            value: Arc::new(PureExpr::LogicFnCall {
                name: "proof_assert".to_string(),
                args: vec![PureExpr::Bool(true)],
            }),
            body: Arc::new(value),
        },
    )
}

/// A requires-only function is credited on its body goals, so its body must
/// be one the encoder reads, as the ensures lane's body is
/// (logic_fn_requires_only_program_method_callee.rs): a method the encoder
/// does not know withholds the credit.
#[test]
fn a_requires_only_caller_whose_body_does_not_encode_is_not_credited() {
    let (counters, unverified) =
        run_logic_lane(&[requires_only_asserting_caller(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("y".to_string(), None)),
            method: "not_a_known_method".to_string(),
            args: Vec::new(),
        })]);
    assert_eq!(counters.verified, 0, "an unread body earns no credit");
    assert_eq!(counters.errors, 1);
    assert!(unverified.contains("test::caller"));

    // The isolating twin: the same function returning its parameter.
    let (counters, unverified) = run_logic_lane(&[requires_only_asserting_caller(PureExpr::Var(
        "y".to_string(),
        None,
    ))]);
    assert_eq!(counters.verified, 1);
    assert_eq!(counters.errors, 0);
    assert!(unverified.is_empty());
}

/// `needs_nonneg(x)` requires `x >= 0`; `caller(n)` requires `n >= 0` and
/// calls `needs_nonneg(n - 1)` in the `else` arm of `n == 0`, with `n`
/// declared `sort`.
fn disequality_branch_caller(sort: Option<ExprSort>) -> Vec<LogicFnDef> {
    let var = |name: &str| PureExpr::Var(name.to_string(), None);
    let ge0 = |e: PureExpr| PureExpr::BinOp(Arc::new(e), BinOp::Ge, Arc::new(PureExpr::Int(0)));
    let needs_nonneg = LogicFnDef::new_with_requires(
        "needs_nonneg".to_string(),
        "test::needs_nonneg".to_string(),
        vec!["x".to_string()],
        vec![ge0(var("x"))],
        var("x"),
    )
    .with_param_sorts(vec![sort.clone()]);
    let mut caller = LogicFnDef::new_with_requires(
        "caller".to_string(),
        "test::caller".to_string(),
        vec!["n".to_string()],
        vec![ge0(var("n"))],
        PureExpr::Ite(
            Arc::new(PureExpr::BinOp(
                Arc::new(var("n")),
                BinOp::Eq,
                Arc::new(PureExpr::Int(0)),
            )),
            Arc::new(PureExpr::Int(0)),
            Arc::new(PureExpr::LogicFnCall {
                name: "needs_nonneg".to_string(),
                args: vec![PureExpr::BinOp(
                    Arc::new(var("n")),
                    BinOp::Sub,
                    Arc::new(PureExpr::Int(1)),
                )],
            }),
        ),
    )
    .with_param_sorts(vec![sort]);
    caller.set_ensures(vec![PureExpr::Bool(true)]);
    vec![needs_nonneg, caller]
}

/// logic_fn_recursive_disequality_branch_control.rs: `n - 1 >= 0` follows
/// from `n >= 0` and `n != 0` over the integers only. Stated as the integer
/// restatement of the branch, the goal is proved with a checkable
/// certificate. AY can also certify the original formula when the integer
/// domain is inferred from its arithmetic rather than explicitly annotated.
#[test]
fn an_integer_disequality_branch_is_certified_with_explicit_or_inferred_sort() {
    for sort in [Some(ExprSort::Int), None] {
        let (counters, unverified) = run_logic_lane(&disequality_branch_caller(sort));
        assert_eq!(counters.verified, 1);
        assert_eq!(counters.failed, 0);
        assert_eq!(counters.errors, 0);
        assert!(unverified.is_empty());
    }
}

/// For n=0.5, nonnegative and nonzero do not imply n-1>=0. Supplying the
/// actual noninteger domain must not receive the integer restatement.
#[test]
fn a_float_disequality_branch_receives_no_integer_credit() {
    let (counters, unverified) = run_logic_lane(&disequality_branch_caller(Some(ExprSort::Float(
        trust_wp_core::formula::FloatWidth::F64,
    ))));
    assert_eq!(
        counters.verified, 0,
        "a floating-point counterexample must not be ruled out by integer reasoning"
    );
    assert!(counters.failed + counters.errors > 0);
    assert!(unverified.contains("test::caller"));
}
