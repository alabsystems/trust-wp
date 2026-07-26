// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use serde::{Deserialize, Serialize};
use trust_wp_core::verify_bundle::{
    replay_native_pure_evidence, replay_verify_bundle_result_evidence,
    trust_tmir_to_verify_bundle_with_budget, BundleDiagnosticSeverity, BundleObligationKind,
    BundleObligationStatus, BundleProducer, BundleSourceSpan, BundleSummaryFact,
    BundleSummaryFactKind, BundleTarget, EvidenceArtifactKind, NativeTrustWpBundleVerifier,
    TrustTmirAdapterBudget, TrustTmirAdapterMetrics, TrustTmirBinOp, TrustTmirBundle,
    TrustTmirExpr, TrustTmirFormula, TrustTmirObligation, TrustTmirSort, VerifyBundleEngine,
    VerifyBundleOptions, VerifyBundleStatus,
};

const SNAPSHOT: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../../reports/2026-04-29-trust-tmir-verify-bundle-performance-gate.json"
));
const SCHEMA: &str = "trust-wp.trust-tmir.verify-bundle-perf-gate.v1";
const FIXTURE_NAME: &str = "compiler-adjacent-linear-vc-bundle";
const ISSUE: u64 = 2749;
const OBLIGATIONS: usize = 18;

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct GateMetrics {
    schema: String,
    issue: u64,
    fixture: FixtureMetrics,
    adapter_budget: AdapterBudgetSnapshot,
    adapter_metrics: AdapterMetricsSnapshot,
    verify_bundle_metrics: VerifyBundleMetrics,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct FixtureMetrics {
    name: String,
    obligations: usize,
    preconditions: usize,
    postconditions: usize,
    loop_invariants: usize,
    source_locations: usize,
    summary_facts: usize,
}

#[allow(clippy::struct_field_names)]
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct AdapterBudgetSnapshot {
    max_obligations: usize,
    max_bindings: usize,
    max_expr_nodes: usize,
    max_expr_depth: usize,
    max_payload_bytes: usize,
    max_summary_facts: usize,
    max_source_locations: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct AdapterMetricsSnapshot {
    obligations: usize,
    bindings: usize,
    expr_nodes: usize,
    max_expr_depth: usize,
    payload_bytes: usize,
    summary_facts: usize,
    source_locations: usize,
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
struct VerifyBundleMetrics {
    verification_on: bool,
    request_json_bytes: usize,
    result_json_bytes: usize,
    obligation_results: usize,
    verified_obligations: usize,
    replayed_obligations: usize,
    proof_evidence_artifacts: usize,
    summary_evidence_artifacts: usize,
    aggregate_evidence_artifacts: usize,
    stable_evidence_wire_bytes: usize,
    aggregate_evidence_wire_bytes: usize,
    max_stable_evidence_wire_bytes: usize,
}

#[test]
fn trust_tmir_verify_bundle_ci_metrics_match_snapshot() {
    let actual = collect_gate_metrics();
    let expected: GateMetrics = serde_json::from_str(SNAPSHOT).expect("metrics snapshot parses");

    assert_eq!(
        actual,
        expected,
        "Trust/tMIR verify_bundle performance metrics changed:\n{}",
        serde_json::to_string_pretty(&actual).expect("actual metrics serialize")
    );
}

#[test]
fn trust_tmir_verify_bundle_ci_budget_rejects_growth_before_verification() {
    let bundle = compiler_adjacent_bundle();
    let metrics = bundle.adapter_metrics().expect("adapter metrics");
    let mut budget = ci_budget();
    budget.max_expr_nodes = metrics.expr_nodes - 1;

    let err = trust_tmir_to_verify_bundle_with_budget(bundle, &budget).unwrap_err();

    assert!(err.diagnostics().iter().any(|diagnostic| {
        diagnostic.severity == BundleDiagnosticSeverity::Unsupported
            && diagnostic.code == "trust_tmir.performance_budget"
            && diagnostic.message.contains("expr_nodes")
    }));
}

fn collect_gate_metrics() -> GateMetrics {
    let budget = ci_budget();
    let bundle = compiler_adjacent_bundle();
    let adapter_metrics = bundle
        .checked_adapter_metrics(&budget)
        .expect("compiler-adjacent fixture stays within adapter budget");
    let request =
        trust_tmir_to_verify_bundle_with_budget(bundle, &budget).expect("adapter conversion");
    let request_json_bytes = serde_json::to_vec(&request)
        .expect("request JSON serializes")
        .len();
    let result = NativeTrustWpBundleVerifier.verify_bundle(request.clone());

    assert_eq!(result.status, VerifyBundleStatus::Verified);
    assert!(result.is_verified());
    assert_eq!(result.obligation_results.len(), OBLIGATIONS);
    replay_verify_bundle_result_evidence(&request, &result).expect("aggregate evidence replays");

    let mut verified_obligations = 0;
    let mut replayed_obligations = 0;
    let mut proof_evidence_artifacts = 0;
    let mut summary_evidence_artifacts = 0;
    let mut stable_evidence_wire_bytes = 0;
    let mut max_stable_evidence_wire_bytes = 0;

    for (obligation, obligation_result) in request
        .obligations
        .iter()
        .zip(result.obligation_results.iter())
    {
        let BundleObligationStatus::Verified { evidence } = &obligation_result.status else {
            panic!("expected verified obligation `{}`", obligation.id);
        };
        verified_obligations += 1;
        proof_evidence_artifacts += evidence.artifacts.len();
        summary_evidence_artifacts += evidence
            .artifacts
            .iter()
            .filter(|artifact| artifact.kind == EvidenceArtifactKind::SummaryEvidence)
            .count();
        let wire_bytes = evidence.to_stable_wire().len();
        stable_evidence_wire_bytes += wire_bytes;
        max_stable_evidence_wire_bytes = max_stable_evidence_wire_bytes.max(wire_bytes);
        replay_native_pure_evidence(&request, obligation, evidence).expect("evidence replays");
        replayed_obligations += 1;
    }
    let aggregate_evidence = result
        .aggregate_evidence
        .as_ref()
        .expect("verified fixture carries aggregate proof evidence");
    let aggregate_evidence_artifacts = aggregate_evidence.artifacts.len();
    assert!(aggregate_evidence.artifacts.iter().any(|artifact| {
        artifact.kind == EvidenceArtifactKind::AggregateProofManifest
            && artifact.has_stable_identity()
    }));
    let aggregate_evidence_wire_bytes = aggregate_evidence.to_stable_wire().len();

    let result_json_bytes = serde_json::to_vec(&result)
        .expect("result JSON serializes")
        .len();

    GateMetrics {
        schema: SCHEMA.to_string(),
        issue: ISSUE,
        fixture: FixtureMetrics {
            name: FIXTURE_NAME.to_string(),
            obligations: OBLIGATIONS,
            preconditions: 6,
            postconditions: 6,
            loop_invariants: 6,
            source_locations: OBLIGATIONS,
            summary_facts: 6,
        },
        adapter_budget: budget_snapshot(&budget),
        adapter_metrics: adapter_metrics_snapshot(adapter_metrics),
        verify_bundle_metrics: VerifyBundleMetrics {
            verification_on: true,
            request_json_bytes,
            result_json_bytes,
            obligation_results: result.obligation_results.len(),
            verified_obligations,
            replayed_obligations,
            proof_evidence_artifacts,
            summary_evidence_artifacts,
            aggregate_evidence_artifacts,
            stable_evidence_wire_bytes,
            aggregate_evidence_wire_bytes,
            max_stable_evidence_wire_bytes,
        },
    }
}

fn compiler_adjacent_bundle() -> TrustTmirBundle {
    let mut bundle =
        TrustTmirBundle::new("trust-tmir-ci-perf-gate", "demo", "demo::compiler_lowered");
    bundle.producer = BundleProducer::new("trust-tmir")
        .with_version("ci-gate")
        .with_revision("tmir-snapshot-2749");
    bundle.target = BundleTarget::new("demo")
        .with_package_name("demo")
        .with_target_triple("x86_64-unknown-linux-gnu");
    let mut options = VerifyBundleOptions::default();
    options.require_proof_evidence = true;
    options.timeout_ms = Some(1_000);
    bundle.options = options;

    for index in 0..OBLIGATIONS {
        let line = 40 + u32::try_from(index).expect("fixture index fits in u32");
        let mut obligation = TrustTmirObligation::new(
            format!("tmir-vc-{index:02}"),
            obligation_kind(index),
            linear_compiler_formula(index),
        )
        .with_location(BundleSourceSpan::new(
            format!("src/compiler_lowered_{index:02}.rs"),
            line,
            17,
        ));

        if index % 3 == 0 {
            obligation = obligation.with_summary_fact(summary_fact(index));
        }

        bundle = bundle.with_obligation(obligation);
    }

    bundle
}

fn obligation_kind(index: usize) -> BundleObligationKind {
    match index % 3 {
        0 => BundleObligationKind::Precondition {
            callee: format!("demo::callee_{index:02}"),
        },
        1 => BundleObligationKind::Postcondition,
        _ => BundleObligationKind::LoopInvariant,
    }
}

fn linear_compiler_formula(index: usize) -> TrustTmirFormula {
    let arg = format!("arg_{index:02}");
    let arg_nonnegative = TrustTmirExpr::binary(
        TrustTmirBinOp::Ge,
        TrustTmirExpr::var(arg.as_str()),
        TrustTmirExpr::int(0),
    );
    let increment_positive = TrustTmirExpr::binary(
        TrustTmirBinOp::Gt,
        TrustTmirExpr::binary(
            TrustTmirBinOp::Add,
            TrustTmirExpr::var(arg.as_str()),
            TrustTmirExpr::int(1),
        ),
        TrustTmirExpr::int(0),
    );

    TrustTmirFormula::new(TrustTmirExpr::binary(
        TrustTmirBinOp::Implies,
        arg_nonnegative,
        increment_positive,
    ))
    .with_variable(arg, TrustTmirSort::Int)
    .with_named_result(format!("ret_{index:02}"), TrustTmirSort::Int)
}

fn summary_fact(index: usize) -> BundleSummaryFact {
    BundleSummaryFact::new(
        format!("summary-linear-range-{index:02}"),
        "trust-tmir",
        "dep_math",
        format!("dep_math::linear_range_summary_{index:02}"),
        BundleSummaryFactKind::Other {
            schema: "trust.summary.linear-int-range.v1".to_string(),
        },
        trust_wp_core::verify_bundle::BundleDigest::new("sha256", format!("{:064x}", index + 1)),
    )
}

fn ci_budget() -> TrustTmirAdapterBudget {
    let mut budget = TrustTmirAdapterBudget::default();
    budget.max_obligations = OBLIGATIONS;
    budget.max_bindings = 36;
    budget.max_expr_nodes = 162;
    budget.max_expr_depth = 4;
    budget.max_payload_bytes = 16_384;
    budget.max_summary_facts = 6;
    budget.max_source_locations = OBLIGATIONS;
    budget
}

fn budget_snapshot(budget: &TrustTmirAdapterBudget) -> AdapterBudgetSnapshot {
    AdapterBudgetSnapshot {
        max_obligations: budget.max_obligations,
        max_bindings: budget.max_bindings,
        max_expr_nodes: budget.max_expr_nodes,
        max_expr_depth: budget.max_expr_depth,
        max_payload_bytes: budget.max_payload_bytes,
        max_summary_facts: budget.max_summary_facts,
        max_source_locations: budget.max_source_locations,
    }
}

fn adapter_metrics_snapshot(metrics: TrustTmirAdapterMetrics) -> AdapterMetricsSnapshot {
    AdapterMetricsSnapshot {
        obligations: metrics.obligations,
        bindings: metrics.bindings,
        expr_nodes: metrics.expr_nodes,
        max_expr_depth: metrics.max_expr_depth,
        payload_bytes: metrics.payload_bytes,
        summary_facts: metrics.summary_facts,
        source_locations: metrics.source_locations,
    }
}
