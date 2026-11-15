// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use trust_wp_core::verify_bundle::{
    replay_native_pure_evidence, BundleClaim, BundleClaimFormat, BundleObligation,
    BundleObligationKind, BundleObligationStatus, BundleProducer, BundleTarget,
    EvidenceArtifactKind, NativeTrustWpBundleVerifier, ProofEvidence, VerifyBundleEngine,
    VerifyBundleRequest, VerifyBundleStatus,
};

fn request(predicate: &str) -> VerifyBundleRequest {
    VerifyBundleRequest::new(
        "mixed-scalar-goal",
        BundleProducer::new("trust-ir"),
        BundleTarget::new("native-select"),
    )
    .with_obligation(BundleObligation::new(
        "original-postcondition",
        BundleObligationKind::Postcondition,
        "native_select",
        BundleClaim::new(BundleClaimFormat::TrustWpPureExprV1, predicate),
    ))
}

fn verified(request: &VerifyBundleRequest) -> ProofEvidence {
    let original = request.clone();
    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());
    assert_eq!(
        result.status,
        VerifyBundleStatus::Verified,
        "request={request:#?}\nresult={result:#?}"
    );
    let BundleObligationStatus::Verified { evidence } = &result.obligation_results[0].status else {
        panic!("a verified native scalar goal must retain proof evidence");
    };
    assert!(evidence.is_proof_grade());
    replay_native_pure_evidence(request, &request.obligations[0], evidence).unwrap();
    assert_eq!(*request, original);
    evidence.clone()
}

fn replay_text(evidence: &ProofEvidence) -> &str {
    &evidence
        .artifacts
        .iter()
        .find(|artifact| artifact.kind == EvidenceArtifactKind::ReplayLog)
        .unwrap()
        .inline_bytes
        .as_ref()
        .unwrap()
        .data
}

#[test]
fn symbolic_unsigned_select_continuations_prove_and_replay_the_whole_goal() {
    for maximum in [
        "255",
        "4294967295",
        "(9223372036854775807 + 9223372036854775807 + 1)",
    ] {
        // Both guarded substitutions come from the same original contract:
        // c -> r=x and !c -> r=y. No integer is selected as a test valuation.
        let goal = format!(
            "((x : Int) >= 0 && x <= {maximum} && (y : Int) >= 0 && y <= {maximum}) ==> \
             (((c : bool) ==> ((c ==> x == x) && (!c ==> x == y))) && \
              (!c ==> ((c ==> y == x) && (!c ==> y == y))))"
        );
        let evidence = verified(&request(&goal));
        assert!(replay_text(&evidence).contains("replay-rule:boolean-integer-case-split\n"));
    }
}

#[test]
fn boolean_cases_retain_the_enclosing_symbolic_integer_constraints() {
    for goal in [
        "((x : Int) >= 8 && (y : Int) >= x) ==> \
         (((p : bool) ==> y >= 8) && (!p ==> x + 1 >= 9))",
        "((p : bool) ==> ((q : bool) ==> (x : Int) == x)) && \
         (!p ==> (!q ==> (y : Int) + 1 > y))",
        "(if (p : bool) { (x : Int) + 1 } else { x + 2 }) > x",
    ] {
        verified(&request(goal));
    }
}

#[test]
fn scalar_constraint_combinations_keep_direction_and_integer_strictness() {
    for goal in [
        "((x : Int) >= 8 && (y : Int) >= x) ==> y >= 8",
        "((y : Int) >= (x : Int) && x >= 8) ==> y >= 8",
        "((x : Int) > 8 && (y : Int) >= x) ==> y > 8",
        "((x : Int) > 8 && (y : Int) >= x) ==> y >= 9",
        "((x : Int) >= 8 && (y : Int) > x) ==> y > 8",
        "(-(x : Int) >= 8 && (y : Int) >= -x) ==> y >= 8",
        "((x : Int) >= 8 && (y : Int) >= x && (z : Int) >= y) ==> z >= 8",
        "((x : Int) >= 8 && (y : Int) >= 2 * x) ==> y >= 16",
    ] {
        verified(&request(goal));
    }
    for goal in [
        "((x : Int) >= 8 && (y : Int) >= x) ==> y > 8",
        "((x : Int) >= 8 && (y : Int) <= x) ==> y >= 8",
        "((x : Int) >= (y : Int) && y >= x) ==> x >= 0",
        "((x : Int) >= 8 && 2 * (y : Int) >= x) ==> y >= 5",
        "((x : Int) >= 0 && (y : Int) >= \
         (9223372036854775807 * 9223372036854775807 * 3) * x) ==> y >= 0",
    ] {
        let result = NativeTrustWpBundleVerifier.verify_bundle(request(goal));
        assert_eq!(
            result.status,
            VerifyBundleStatus::Unsupported,
            "{goal}: {result:#?}"
        );
    }
}

#[test]
fn boolean_results_of_exact_unsigned_constant_comparisons_keep_the_original_question() {
    let wide = "(9223372036854775807 + 9223372036854775807 + 1)";
    for maximum in ["255", "4294967295", wide] {
        // The native body selects zero/MAX, compares the selected value with
        // zero and returns that Boolean. Its unchanged original claim is r=c.
        let goal = format!("((c : bool) ==> ((0 == 0) == c)) && (!c ==> (({maximum} == 0) == c))");
        let original = request(&goal);
        let evidence = verified(&original);
        let changed = request(&format!(
            "((c : bool) ==> (({maximum} == 0) == c)) && (!c ==> ((0 == 0) == c))"
        ));
        let result = NativeTrustWpBundleVerifier.verify_bundle(changed.clone());
        assert_eq!(result.status, VerifyBundleStatus::Failed, "{result:#?}");
        assert!(replay_native_pure_evidence(&changed, &changed.obligations[0], &evidence).is_err());
    }
    for goal in [
        format!("({wide} == 0) == false"),
        format!("false == ({wide} == 0)"),
        format!("({wide} == 0) != true"),
        format!("true != ({wide} == 0)"),
        format!("({wide} > 9223372036854775807) == true"),
        format!("!(({wide} <= 9223372036854775807) == true)"),
        format!("(({wide} != 0) == true) == true"),
    ] {
        verified(&request(&goal));
    }
    for goal in [
        format!("({wide} == 0) != false"),
        format!("true == ({wide} == 0)"),
    ] {
        let result = NativeTrustWpBundleVerifier.verify_bundle(request(&goal));
        assert_eq!(
            result.status,
            VerifyBundleStatus::Failed,
            "{goal}: {result:#?}"
        );
    }
    for (goal, expected) in [
        (
            "((x : Int) == (y : Int)) == false",
            VerifyBundleStatus::Failed,
        ),
        (
            "((x : Int) == (y : Int)) == true",
            VerifyBundleStatus::Failed,
        ),
        (
            "((9223372036854775807 + 9223372036854775807 + 1) == 0) == ((x : Int) > 0)",
            VerifyBundleStatus::Failed,
        ),
        (
            "((9223372036854775807 * 9223372036854775807 * 3) > 0) == true",
            VerifyBundleStatus::Unsupported,
        ),
    ] {
        let result = NativeTrustWpBundleVerifier.verify_bundle(request(goal));
        assert_eq!(result.status, expected, "{goal}: {result:#?}");
    }
    let prior_boolean = verified(&request("!((p : bool) && false) == true"));
    assert!(replay_text(&prior_boolean).contains("replay-rule:boolean-case-split\n"));
}

#[test]
fn symbolic_integer_failure_requires_a_checked_whole_goal_counterexample() {
    for goal in [
        "(p : bool) || ((x : Int) == (y : Int))",
        "(p : bool) || ((x : Int) > 0)",
        "(x : Int) >= 0 ==> \
         (((p : bool) ==> x >= 1) && (!p ==> x >= 0))",
        "((p : bool) ==> (x : Int) == (y : Int)) && (!p ==> y == y)",
    ] {
        let result = NativeTrustWpBundleVerifier.verify_bundle(request(goal));
        assert_eq!(
            result.status,
            VerifyBundleStatus::Failed,
            "{goal}: {result:#?}"
        );
    }
    let result =
        NativeTrustWpBundleVerifier.verify_bundle(request("(p : bool) || ((x : Int) < x)"));
    assert_eq!(result.status, VerifyBundleStatus::Failed, "{result:#?}");
}

#[test]
fn scalar_candidates_preserve_guards_and_do_not_guess_validity() {
    for maximum in [
        "255",
        "4294967295",
        "(9223372036854775807 + 9223372036854775807 + 1)",
    ] {
        let goal = format!(
            "((x : Int) >= 0 && x <= {maximum} && (y : Int) >= 0 && y <= {maximum}) ==> \
             (((c : bool) ==> y == x) && (!c ==> x == y))"
        );
        let original = request(&goal);
        let result = NativeTrustWpBundleVerifier.verify_bundle(original.clone());
        assert_eq!(result.status, VerifyBundleStatus::Failed, "{result:#?}");
        assert_eq!(result.obligation_results.len(), 1);
        assert!(matches!(&result.obligation_results[0].status,
            BundleObligationStatus::Failed { reason } if reason.contains("checked whole-predicate counterexample")));
    }
    // Every generated zero/one candidate violates the antecedent. That is not
    // evidence that this universally quantified, actually false goal is true.
    let result = NativeTrustWpBundleVerifier.verify_bundle(request("(x : Int) >= 8 ==> x >= 9"));
    assert_eq!(
        result.status,
        VerifyBundleStatus::Unsupported,
        "{result:#?}"
    );
    verified(&request("((x : Int) == 0 && (y : Int) == 0) ==> x == y"));
}

#[test]
fn changed_scalar_goals_and_replay_bytes_cannot_inherit_a_proof() {
    let original = request(
        "((p : bool) ==> ((p ==> (x : Int) == x) && (!p ==> x == (y : Int)))) && \
         (!p ==> ((p ==> y == x) && (!p ==> y == y)))",
    );
    let evidence = verified(&original);
    assert!(replay_text(&evidence).contains("replay-rule:boolean-integer-case-split\n"));
    for goal in [
        "((p : bool) ==> (x : Int) == (y : Int)) && (!p ==> y == y)",
        "((p : bool) ==> (x : Int) != x) && (!p ==> (y : Int) == y)",
        "((p : bool) ==> (x : Int) + 1 > x) && (!p ==> (y : Int) == y)",
    ] {
        let changed = request(goal);
        assert!(replay_native_pure_evidence(&changed, &changed.obligations[0], &evidence).is_err());
    }
    let mut changed = evidence;
    let replay = changed
        .artifacts
        .iter_mut()
        .find(|artifact| artifact.kind == EvidenceArtifactKind::ReplayLog)
        .unwrap();
    let bytes = replay.inline_bytes.as_mut().unwrap();
    bytes.data = bytes
        .data
        .replace("boolean-integer-case-split", "bool-literal");
    assert!(replay_native_pure_evidence(&original, &original.obligations[0], &changed).is_err());
}

#[test]
fn temporal_bound_and_conflicting_names_do_not_become_boolean_cases() {
    for goal in [
        "(p : bool) == old(p)",
        "((p : bool) || (x : Int) == x) && (p == old(p))",
        "!(p : bool) || forall<p: bool> p",
        "((p : bool) || (x : Int) == x) && (p == (x > 0))",
        "((p : bool) || (x : Int) == x) && (p == (*r : bool))",
        "((p : bool) || (x : Int) == x) && (p == (^r : bool))",
        "((p : bool) || (x : Int) == x) && (p == r@)",
        "((p : bool) || (x : Int) == x) && (p == f(x))",
        "((p : bool) || (x : Int) == x) && (p == (p + 1 > p))",
    ] {
        let parsed = trust_wp_core::contract_parser::parse_contract(goal)
            .expect("well-formed refusal input");
        if goal.contains("^r") {
            assert!(parsed
                .any_recursive(|expr| matches!(expr, trust_wp_core::formula::PureExpr::Final(_))));
        }
        let result = NativeTrustWpBundleVerifier.verify_bundle(request(goal));
        assert_ne!(
            result.status,
            VerifyBundleStatus::Verified,
            "{goal}: {result:#?}"
        );
    }
}

#[test]
fn mixed_case_name_depth_and_node_budgets_refuse_without_reducing_the_goal() {
    let names = (0..9)
        .map(|index| format!("((p{index} : bool) || !(p{index} : bool))"))
        .collect::<Vec<_>>()
        .join(" && ");
    let depth = format!("{}((p : bool) || !p)", "!".repeat(66));
    let mut nodes = "((p : bool) || !p)".to_string();
    for _ in 0..11 {
        nodes = format!("({nodes}) && ({nodes})");
    }
    for boolean in [names, depth, nodes] {
        let result = NativeTrustWpBundleVerifier
            .verify_bundle(request(&format!("({boolean}) && ((x : Int) == x)")));
        assert_ne!(result.status, VerifyBundleStatus::Verified, "{result:#?}");
    }
}

#[test]
fn existing_pure_boolean_replay_rule_is_unchanged() {
    let evidence = verified(&request("(p : bool) || !(p : bool)"));
    assert!(replay_text(&evidence).contains("replay-rule:boolean-case-split\n"));
    assert!(!replay_text(&evidence).contains("boolean-integer-case-split"));
}
