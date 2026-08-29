// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    collections::{HashMap, HashSet},
    time::Duration,
};

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def_id::DefId;
use rustc_interface::interface::{Compiler, Config};
use rustc_middle::ty::TyCtxt;
use trust_wp_core::{formula::PureExpr, logic::TypeInvariantDef, TrackLevel};
use trust_wp_driver::{builtin_trust_wp_std_specs, StdSpec};

use super::rustc_callback_harness::{
    run_test_compiler_with_args, trust_wp_probe_args, TEST_CRATE_NAME,
};
use crate::{
    callbacks::{
        copy_mir_bodies,
        discovery::{
            discover_proof_assert_functions, find_contract_functions,
            source_parsing::collect_loop_contract_attrs,
        },
        ghost_context::{find_ghost_closure_def_ids_in_mir, ghost_block_contains_cutoff},
        helpers::{
            diagnose_identity_final_value_synthesis_skip,
            diagnose_identity_final_value_synthesis_skip_with_expr,
            IdentityFinalValueSynthesisSkipReason,
        },
        parsing::build_user_spec_table,
        proof_assert_snapshot::build_assertion_snapshots_for_function,
        proof_assert_verify::{build_proof_assert_setup, prepare_proof_assert},
        verification::verify_contracts,
        verification_context::{ProofAssertContext, VerificationRunConfig},
    },
    ghost::find_ghost_blocks,
    mir_analysis::{detect_loops, get_mir_body},
    proof_assert::find_proof_asserts_in_mir,
};

fn complicated_identity_fixture_source() -> &'static str {
    r#"
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

use trust_wp_std::prelude::*;

#[check(ghost)]
#[ensures(result == m)]
pub fn complicated_identity<K: std::cmp::Eq + std::hash::Hash, V>(
    m: Ghost<FMap<K, V>>,
) -> Ghost<FMap<K, V>> {
    ghost! {
        let mut result = FMap::new().into_inner();

        let _m_snap = snapshot!(m);

        #[variant(iter@.len())]
        #[invariant(forall<k, v> (_m_snap.get(k) == Some(v)) == (result.get(k) == Some(v) || iter@.get(k) == Some(v)))]
        for (k, v) in m.into_inner() {
            result.insert_ghost(k, v);
        }

        proof_assert!(result.ext_eq(**_m_snap));

        result
    }
}
"#
}

fn complicated_identity_view_fn_fixture_source() -> &'static str {
    r#"
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

use trust_wp_std::prelude::*;

#[check(ghost)]
#[ensures(result == m)]
pub fn complicated_identity_view_fn<K: std::cmp::Eq + std::hash::Hash, V>(
    m: Ghost<FMap<K, V>>,
) -> Ghost<FMap<K, V>> {
    ghost! {
        let mut result = FMap::new().into_inner();

        let _m_snap = snapshot!(m);

        #[variant(iter@.len())]
        #[invariant(forall<k, v> (_m_snap.get(k) == Some(v)) == (result.get(k) == Some(v) || view(iter).get(k) == Some(v)))]
        for (k, v) in m.into_inner() {
            result.insert_ghost(k, v);
        }

        proof_assert!(result.ext_eq(**_m_snap));

        result
    }
}
"#
}

fn assoc_const_proof_assert_fixture_source() -> &'static str {
    r#"
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

use trust_wp::*;

pub trait Nat {
    const VALUE: usize;
}

pub struct Two;

impl Nat for Two {
    const VALUE: usize = 2;
}

pub struct I3<T: Nat>(T);

impl<T: Nat> Nat for I3<T> {
    const VALUE: usize = const { T::VALUE + T::VALUE };
}

#[ensures(true)]
pub fn nat_i3<T: Nat>() {
    proof_assert! { <I3<T> as Nat>::VALUE@ == T::VALUE@ + T::VALUE@ };
}
"#
}

fn module_qualified_assoc_const_proof_assert_fixture_source() -> &'static str {
    r#"
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

use trust_wp::*;

mod traits {
    pub trait Nat {
        const VALUE: usize;
    }
}

use traits::Nat;

pub struct I3<T: Nat>(T);

impl<T: Nat> traits::Nat for I3<T> {
    const VALUE: usize = const { T::VALUE + T::VALUE };
}

#[ensures(true)]
pub fn nat_i3<T: traits::Nat>() {
    proof_assert! { <I3<T> as traits::Nat>::VALUE@ == T::VALUE@ + T::VALUE@ };
}
"#
}

fn super_qualified_assoc_const_proof_assert_fixture_source() -> &'static str {
    r#"
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]
#![allow(dead_code)]

mod outer {
    pub mod traits {
        pub trait Nat {
            const VALUE: usize;
        }
    }

    use traits::Nat;

    pub struct I3<T: Nat>(T);

    impl<T: Nat> traits::Nat for I3<T> {
        const VALUE: usize = const { T::VALUE + T::VALUE };
    }

    pub mod nested {
        use trust_wp::*;

        #[ensures(true)]
        pub fn nat_i3<T: super::traits::Nat>() {
            proof_assert! { <super::I3<T> as super::traits::Nat>::VALUE@ == T::VALUE@ + T::VALUE@ };
        }
    }
}
"#
}

fn write_inner_borrow_fixture_source() -> &'static str {
    r#"
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

use trust_wp::*;

#[ensures(true)]
pub fn write_inner_borrow<'a>(x: &mut &'a mut i32, b: &'a mut i32, value: i32) {
    let _r = &mut **x;
    let _snap = snapshot!(&mut **x);
    *x = b;
    **x = value;
    proof_assert!(_r == *_snap);
}
"#
}

fn rebor_in_pair_fixture_source() -> &'static str {
    r#"
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

use trust_wp::*;

pub fn rebor_in_pair() {
    let mut x = 12;
    let mut y = 13;
    let mut p = (&mut x, 12);
    let s = snapshot!(p.0);
    let b = &mut *p.0;
    proof_assert!(*s == b);
    p.0 = &mut y;
}
"#
}

fn later_reborrow_not_final_fixture_source() -> &'static str {
    r#"
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

use trust_wp::*;

pub fn not_final_borrow(bor: &mut i32) {
    let b1 = &mut *bor;
    let _b2 = &mut *bor;
    proof_assert!(b1 == bor);
}
"#
}

fn inspect_no_gen_fixture_source() -> &'static str {
    r#"
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

use trust_wp::*;

pub fn inspect_no_gen<T>(x: &mut Option<T>) {
    let r = &mut *x;

    if matches!(x, Some(_)) {
        return;
    }
    proof_assert!(r == x);
}
"#
}

fn shallow_borrow_no_gen_fixture_source() -> &'static str {
    r#"
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

use trust_wp::*;

pub fn shallow_borrow_no_gen(x: &mut Option<i32>) {
    let _r = &mut *x;
    match *x {
        Some(ref inner) if *inner == 2 => {
            proof_assert!(_r == x);
        }
        _ => {}
    }
}
"#
}

fn nested_loop_post_assert_fixture_source() -> &'static str {
    r#"
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

use trust_wp::*;

#[ensures(true)]
pub fn nested_loop_post_assert(n: i32) {
    let mut i = 0;

    #[invariant(i >= 0)]
    while i < n {
        let mut j = 0;

        #[invariant(j >= 0)]
        #[invariant(j <= 1)]
        while j < 1 {
            j += 1;
        }

        proof_assert!(j == 1);
        i += 1;
    }
}
"#
}

fn contracted_and_contractless_proof_assert_fixture_source() -> &'static str {
    r#"
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]

use trust_wp::*;

#[ensures(true)]
pub fn contracted() {
    proof_assert!(1 == 1);
}

pub fn contractless() {
    proof_assert!(1 == 1);
}
"#
}

fn ghost_seq_push_back_proof_assert_fixture_source() -> &'static str {
    r#"
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]
#![allow(unexpected_cfgs)]
#![allow(unused_variables)]

use trust_wp::*;

pub fn ghost_seq_push_back_proof_assert() {
    let _ = ghost! {
        let mut v = Seq::new();
        v.push_back_ghost(30i32);
        proof_assert!(v[0] == 30i32);
    };
}
"#
}

fn ghost_side_channel_obligation_fixture_source() -> &'static str {
    r#"
#![feature(stmt_expr_attributes)]
#![feature(proc_macro_hygiene)]
#![allow(unexpected_cfgs)]
#![allow(unused_variables)]

use trust_wp::*;

#[trusted]
#[requires(false)]
#[ensures(result == 1i32)]
fn impossible_post() -> i32 {
    1
}

pub fn ghost_side_channel_obligation() {
    let _ = ghost! {
        let y = impossible_post();
        proof_assert!(y == 1i32);
    };
}
"#
}

fn closure_caller_capture_verify_fixture_source() -> String {
    let body = std::fs::read_to_string(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/../../tests/fixtures/proof_assert/src/closure_caller_capture_verify.rs"
    ))
    .expect("closure_caller_capture_verify fixture should be readable");
    format!("#![feature(stmt_expr_attributes)]\n\n{body}")
}

fn path_matches_name(tcx: TyCtxt<'_>, def_id: DefId, name: &str) -> bool {
    let path = tcx.def_path_str(def_id);
    path == name || path.ends_with(&format!("::{name}"))
}

fn install_mir_borrowck_cache(config: &mut Config) {
    config.override_queries = Some(|_sess, providers| {
        providers.queries.mir_borrowck = |tcx, local_id| {
            if tcx.hir_node_by_def_id(local_id).body_id().is_none() {
                let guar = tcx.dcx().span_delayed_bug(
                    tcx.def_span(local_id),
                    "mir_borrowck called for item without HIR body",
                );
                return Err(guar);
            }
            copy_mir_bodies(tcx, local_id);
            (rustc_interface::DEFAULT_QUERY_PROVIDERS
                .queries
                .mir_borrowck)(tcx, local_id)
        };
    });
}

#[derive(Debug, Default)]
struct ProofAssertPipelineSnapshot {
    assumed_facts: Vec<PureExpr>,
    call_assumptions: Vec<PureExpr>,
    call_effect_expr: Option<PureExpr>,
    has_mutating_call_effect: bool,
    substitution_facts: Vec<PureExpr>,
    post_loop_assumptions: Vec<PureExpr>,
    prepared_preconditions: Vec<PureExpr>,
    prepared_ensures: Vec<PureExpr>,
    snapshot_return_expr: Option<PureExpr>,
    prepared_return_expr: Option<PureExpr>,
    extractor_diagnostics: Vec<String>,
    ran: bool,
}

struct ProofAssertPipelineCallbacks {
    snapshot: ProofAssertPipelineSnapshot,
    target_fn: &'static str,
}

#[derive(Debug, Default)]
struct ProofAssertDriverSummarySnapshot {
    contracted_paths: Vec<String>,
    contractless_paths: Vec<String>,
    proof_assert_verified: usize,
    proof_assert_failed: usize,
    proof_assert_errors: usize,
    exit_code: i32,
    ran: bool,
}

struct ProofAssertDriverSummaryCallbacks {
    snapshot: ProofAssertDriverSummarySnapshot,
}

impl Callbacks for ProofAssertPipelineCallbacks {
    fn config(&mut self, config: &mut Config) {
        install_mir_borrowck_cache(config);
    }

    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let mut contracts = find_contract_functions(tcx);
        discover_proof_assert_functions(tcx, &mut contracts);
        let contract = contracts
            .iter()
            .find(|contract| path_matches_name(tcx, contract.def_id, self.target_fn))
            .expect("target contract function should be discovered");
        let logic_fn_defs = crate::logic::extract_logic_fn_defs(tcx);
        let user_specs = build_user_spec_table(&contracts);
        let (pa_setup, warnings) =
            build_proof_assert_setup(tcx, &contracts, &logic_fn_defs, &user_specs);
        assert_eq!(warnings, 0, "fixture should parse without setup warnings");

        let trait_specs: HashMap<DefId, StdSpec> = HashMap::new();
        let extern_specs = builtin_trust_wp_std_specs();
        let type_invariant_defs: Vec<TypeInvariantDef> = Vec::new();
        let pa_ctx = ProofAssertContext {
            logic_fn_defs: &logic_fn_defs,
            type_invariant_defs: &type_invariant_defs,
            trait_specs: &trait_specs,
            extern_specs: &extern_specs,
            verbose: false,
        };

        let ghost_blocks = find_ghost_blocks(tcx);
        let body_with_facts = crate::callbacks::try_get_body_with_context(contract.local_def_id)
            .expect("MIR body should be cached by test query override");
        let body = get_mir_body(body_with_facts);
        let assertions = find_proof_asserts_in_mir(tcx, body, contract.local_def_id);
        assert_eq!(
            assertions.len(),
            1,
            "fixture should expose one proof_assert"
        );
        let assertion = &assertions[0];

        let containing_ghost_block = ghost_blocks
            .iter()
            .filter(|block| {
                block.containing_fn == assertion.containing_fn
                    && ghost_block_contains_cutoff(block.span, assertion.span)
            })
            .max_by_key(|block| block.span.source_callsite().lo());
        self.snapshot.extractor_diagnostics.push(format!(
            "assertion_span={}..{}",
            assertion.span.source_callsite().lo().0,
            assertion.span.source_callsite().hi().0
        ));
        if let Some(mut current) = assertion.closure_def_id {
            self.snapshot
                .extractor_diagnostics
                .push(format!("assertion_closure={}", tcx.def_path_str(current)));
            while let Some(parent) = tcx.opt_parent(current) {
                self.snapshot.extractor_diagnostics.push(format!(
                    "ancestor={} kind={:?}",
                    tcx.def_path_str(parent),
                    tcx.def_kind(parent)
                ));
                current = parent;
            }
        }
        self.snapshot.extractor_diagnostics.push(format!(
            "containing_ghost_block={}",
            containing_ghost_block.is_some()
        ));
        if let Some(block) = containing_ghost_block {
            let ghost_closure_def_ids = find_ghost_closure_def_ids_in_mir(body, block.span);
            self.snapshot.extractor_diagnostics.push(format!(
                "ghost_closure_count={}",
                ghost_closure_def_ids.len()
            ));
            for closure_def_id in ghost_closure_def_ids {
                let path = tcx.def_path_str(closure_def_id);
                let Some(local_def_id) = closure_def_id.as_local() else {
                    self.snapshot
                        .extractor_diagnostics
                        .push(format!("closure={path} local=false"));
                    continue;
                };
                let (flat_invariants, _, _, _, all_loop_spans) =
                    collect_loop_contract_attrs(tcx, local_def_id);
                let proof_assert_start = assertion.span.source_callsite().lo().0;
                let after_all_loops = !all_loop_spans.is_empty()
                    && all_loop_spans
                        .iter()
                        .all(|(_, end)| *end <= proof_assert_start);
                let loop_analysis = detect_loops(tcx.optimized_mir(closure_def_id));
                self.snapshot.extractor_diagnostics.push(format!(
                    "closure={path} invariants={} hir_loops={:?} after_all_loops={} mir_loops={}",
                    flat_invariants.len(),
                    all_loop_spans,
                    after_all_loops,
                    loop_analysis.loops.len()
                ));
            }
        }

        let snapshots = build_assertion_snapshots_for_function(
            tcx,
            &assertions,
            &ghost_blocks,
            &pa_setup.user_specs,
            &pa_ctx,
            TEST_CRATE_NAME,
        );
        let snapshot = snapshots
            .into_iter()
            .next()
            .expect("snapshot should be present")
            .expect("snapshot build should succeed");
        let prepared = prepare_proof_assert(tcx, &snapshot, &pa_setup, &pa_ctx, TEST_CRATE_NAME)
            .expect("proof_assert preparation should succeed")
            .expect("fixture proof_assert should not be trusted");
        self.snapshot.assumed_facts = snapshot.assumed_facts;
        self.snapshot.call_assumptions = snapshot.call_assumptions;
        self.snapshot.call_effect_expr = snapshot.call_effect_expr;
        self.snapshot.has_mutating_call_effect = prepared.has_mutating_call_effect;
        self.snapshot.substitution_facts = snapshot.substitution_facts;
        self.snapshot.post_loop_assumptions = snapshot.post_loop_assumptions;
        self.snapshot.snapshot_return_expr = snapshot.return_expr;
        self.snapshot.prepared_preconditions = prepared.preconditions;
        self.snapshot.prepared_ensures = prepared.ensures;
        self.snapshot.prepared_return_expr = prepared.return_expr;
        self.snapshot.ran = true;
        Compilation::Stop
    }
}

impl Callbacks for ProofAssertDriverSummaryCallbacks {
    fn config(&mut self, config: &mut Config) {
        install_mir_borrowck_cache(config);
    }

    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let mut contracts = find_contract_functions(tcx);
        discover_proof_assert_functions(tcx, &mut contracts);

        for contract in &contracts {
            let path = tcx.def_path_str(contract.def_id);
            if contract.requires.is_empty()
                && contract.ensures.is_empty()
                && contract.invariants.is_empty()
                && contract.variants.is_empty()
            {
                self.snapshot.contractless_paths.push(path);
            } else {
                self.snapshot.contracted_paths.push(path);
            }
        }

        let logic_fn_defs = crate::logic::extract_logic_fn_defs(tcx);
        let ghost_blocks = find_ghost_blocks(tcx);
        let type_invariant_defs: Vec<TypeInvariantDef> = Vec::new();
        let trait_specs: HashMap<DefId, StdSpec> = HashMap::new();
        let trait_contracts = Vec::new();
        let trait_refinement_overrides = HashSet::new();
        let recursive_fns = HashSet::new();
        let extern_specs = builtin_trust_wp_std_specs();
        let run_config = VerificationRunConfig {
            all_contracts: &contracts,
            ghost_blocks: &ghost_blocks,
            logic_fns: &logic_fn_defs,
            type_invariant_defs: &type_invariant_defs,
            trait_specs: &trait_specs,
            trait_contracts: &trait_contracts,
            trait_refinement_overrides: &trait_refinement_overrides,
            recursive_fns: &recursive_fns,
            extern_specs: &extern_specs,
            verbose: false,
            track_level: TrackLevel::Auto,
            timeout: Some(Duration::from_secs(5)),
            strict_axioms: false,
            strict_trust: false,
        };

        let summary = verify_contracts(tcx, &contracts, &run_config);
        self.snapshot.proof_assert_verified = summary.proof_assert_verified;
        self.snapshot.proof_assert_failed = summary.proof_assert_failed;
        self.snapshot.proof_assert_errors = summary.proof_assert_errors;
        self.snapshot.exit_code = summary.exit_code();
        self.snapshot.ran = true;
        Compilation::Stop
    }
}

fn collect_proof_assert_pipeline_snapshot(source: &str) -> ProofAssertPipelineSnapshot {
    collect_proof_assert_pipeline_snapshot_for(source, "complicated_identity")
}

fn collect_proof_assert_pipeline_snapshot_for(
    source: &str,
    target_fn: &'static str,
) -> ProofAssertPipelineSnapshot {
    let mut callbacks = ProofAssertPipelineCallbacks {
        snapshot: ProofAssertPipelineSnapshot::default(),
        target_fn,
    };
    run_test_compiler_with_args(
        source,
        "trust_wp_proof_assert_pipeline",
        &trust_wp_probe_args(),
        &mut callbacks,
    );
    assert!(
        callbacks.snapshot.ran,
        "proof_assert pipeline callback should run"
    );
    callbacks.snapshot
}

fn collect_proof_assert_driver_summary(source: &str) -> ProofAssertDriverSummarySnapshot {
    let mut callbacks = ProofAssertDriverSummaryCallbacks {
        snapshot: ProofAssertDriverSummarySnapshot::default(),
    };
    run_test_compiler_with_args(
        source,
        "trust_wp_proof_assert_driver_summary",
        &trust_wp_probe_args(),
        &mut callbacks,
    );
    assert!(
        callbacks.snapshot.ran,
        "proof_assert driver summary callback should run"
    );
    callbacks.snapshot
}

fn assert_complicated_identity_post_loop_specialization(snapshot: &ProofAssertPipelineSnapshot) {
    let post_loop_text: Vec<String> = snapshot
        .post_loop_assumptions
        .iter()
        .map(ToString::to_string)
        .collect();
    let prepared_precondition_text: Vec<String> = snapshot
        .prepared_preconditions
        .iter()
        .map(ToString::to_string)
        .collect();

    assert!(
        !snapshot.post_loop_assumptions.is_empty(),
        "ghost-closure proof_assert snapshot should recover closure-local post-loop assumptions: assumptions={:?} diagnostics={:?}",
        snapshot.post_loop_assumptions,
        snapshot.extractor_diagnostics
    );
    assert!(
        post_loop_text.iter().any(|text| text.contains("fmap_new()")),
        "post-loop assumptions should specialize exhausted iterator views to fmap_new(): {post_loop_text:?}"
    );
    assert!(
        post_loop_text.iter().all(|text| {
            !text.contains("view(iter)")
                && !text.contains("__trust_wp_for_iter_old")
                && !text.contains("produced")
        }),
        "post-loop assumptions should not leak loop-local iterator/continuation state: {post_loop_text:?}"
    );
    assert!(
        prepared_precondition_text.iter().all(|text| {
            !text.contains("view(iter)")
                && !text.contains("__trust_wp_for_iter_old")
                && !text.contains("produced")
        }),
        "prepare_proof_assert should not retain loop-local continuation artifacts before later post-loop injection: {prepared_precondition_text:?}"
    );
}

#[test]
fn complicated_identity_proof_assert_pipeline_snapshot_2116() {
    let snapshot = collect_proof_assert_pipeline_snapshot(complicated_identity_fixture_source());

    assert!(
        snapshot
            .prepared_ensures
            .iter()
            .any(|expr| format!("{expr}").contains("result.ext_eq")),
        "prepared proof_assert should preserve the ext_eq goal shape"
    );
    assert_eq!(
        snapshot.snapshot_return_expr, None,
        "synthetic cutoff marker must not leak into proof_assert snapshots as a real return_expr"
    );
    assert_eq!(
        snapshot.prepared_return_expr, None,
        "prepare_proof_assert must not pass the synthetic cutoff marker to the solver"
    );
    assert!(
        snapshot
            .assumed_facts
            .iter()
            .any(|expr| format!("{expr}").contains("call_5")),
        "normalized assumed facts should still preserve call assumptions when the synthetic return marker is dropped: {:?}",
        snapshot.assumed_facts
    );
    assert!(
        !snapshot.substitution_facts.is_empty(),
        "snapshot should own substitution-derived facts for downstream proof_assert hosts"
    );
    assert_complicated_identity_post_loop_specialization(&snapshot);
}

#[test]
fn complicated_identity_view_fn_proof_assert_pipeline_snapshot_2584() {
    let snapshot = collect_proof_assert_pipeline_snapshot_for(
        complicated_identity_view_fn_fixture_source(),
        "complicated_identity_view_fn",
    );

    assert!(
        snapshot
            .prepared_ensures
            .iter()
            .any(|expr| format!("{expr}").contains("result.ext_eq")),
        "prepared proof_assert should preserve the ext_eq goal shape for the view(iter) syntax fixture"
    );
    assert_complicated_identity_post_loop_specialization(&snapshot);
}

#[test]
fn nested_loop_proof_assert_snapshot_injects_inner_loop_exit_assumptions() {
    let snapshot = collect_proof_assert_pipeline_snapshot_for(
        nested_loop_post_assert_fixture_source(),
        "nested_loop_post_assert",
    );
    let post_loop_text: Vec<String> = snapshot
        .post_loop_assumptions
        .iter()
        .map(ToString::to_string)
        .collect();

    assert!(
        post_loop_text
            .iter()
            .any(|text| text.contains('j') && text.contains(">=") && text.contains('0')),
        "nested proof_assert should receive the completed inner loop invariant: {post_loop_text:?}"
    );
    assert!(
        post_loop_text
            .iter()
            .any(|text| text.contains('j') && text.contains("<=") && text.contains('1')),
        "nested proof_assert should receive all inner loop invariants: {post_loop_text:?}"
    );
    assert!(
        post_loop_text
            .iter()
            .any(|text| text.contains('!') && text.contains('j') && text.contains('<')),
        "nested proof_assert should receive the negated inner loop condition: {post_loop_text:?}"
    );
    assert!(
        post_loop_text
            .iter()
            .all(|text| !(text.contains('i') && text.contains('<') && text.contains('n'))),
        "inner post-loop assumptions must not inject the still-active outer loop condition: {post_loop_text:?}"
    );
}

#[test]
fn assoc_const_proof_assert_pipeline_substitutes_qualified_path_2550() {
    let snapshot = collect_proof_assert_pipeline_snapshot_for(
        assoc_const_proof_assert_fixture_source(),
        "nat_i3",
    );
    let ensures_text: Vec<String> = snapshot
        .prepared_ensures
        .iter()
        .map(ToString::to_string)
        .collect();

    assert!(
        ensures_text
            .iter()
            .all(|text| !text.contains("<I3<T> as Nat>::VALUE")),
        "prepared proof_assert goals should not retain the opaque qualified assoc const path: {ensures_text:?}"
    );
    assert!(
        ensures_text
            .iter()
            .any(|text| text.contains("T::VALUE") && text.contains('+')),
        "prepared proof_assert goals should include the symbolic associated-const body: {ensures_text:?}"
    );
}

#[test]
fn assoc_const_proof_assert_pipeline_substitutes_module_qualified_trait_path_2550() {
    let snapshot = collect_proof_assert_pipeline_snapshot_for(
        module_qualified_assoc_const_proof_assert_fixture_source(),
        "nat_i3",
    );
    let ensures_text: Vec<String> = snapshot
        .prepared_ensures
        .iter()
        .map(ToString::to_string)
        .collect();

    assert!(
        ensures_text
            .iter()
            .all(|text| !text.contains("<I3<T> as traits::Nat>::VALUE")),
        "prepared proof_assert goals should not retain the module-qualified assoc const path: {ensures_text:?}"
    );
    assert!(
        ensures_text
            .iter()
            .any(|text| text.contains("T::VALUE") && text.contains('+')),
        "prepared proof_assert goals should include the symbolic associated-const body for module-qualified trait paths: {ensures_text:?}"
    );
}

#[test]
fn assoc_const_proof_assert_pipeline_substitutes_super_qualified_trait_path_2550() {
    let snapshot = collect_proof_assert_pipeline_snapshot_for(
        super_qualified_assoc_const_proof_assert_fixture_source(),
        "nat_i3",
    );
    let ensures_text: Vec<String> = snapshot
        .prepared_ensures
        .iter()
        .map(ToString::to_string)
        .collect();

    assert!(
        ensures_text
            .iter()
            .all(|text| !text.contains("<I3<T> as super::traits::Nat>::VALUE")),
        "prepared proof_assert goals should not retain the super-qualified assoc const path: {ensures_text:?}"
    );
    assert!(
        ensures_text
            .iter()
            .any(|text| text.contains("T::VALUE") && text.contains('+')),
        "prepared proof_assert goals should include the symbolic associated-const body for super-qualified trait paths: {ensures_text:?}"
    );
}

#[test]
fn write_inner_borrow_pipeline_preserves_snapshot_reborrow_carrier_2590() {
    let snapshot = collect_proof_assert_pipeline_snapshot_for(
        write_inner_borrow_fixture_source(),
        "write_inner_borrow",
    );
    let all_text: Vec<String> = snapshot
        .substitution_facts
        .iter()
        .chain(snapshot.assumed_facts.iter())
        .chain(snapshot.prepared_preconditions.iter())
        .chain(snapshot.prepared_ensures.iter())
        .map(ToString::to_string)
        .collect();

    assert!(
        all_text.iter().any(|text| text.contains("__trust_wp_reborrow_")),
        "proof_assert pipeline should preserve a synthetic reborrow carrier for snapshot!(&mut ...): {all_text:?}"
    );
    assert!(
        all_text.iter().any(|text| {
            text.contains("r == __trust_wp_reborrow_") || text.contains("__trust_wp_reborrow_ == r")
        }),
        "pipeline facts should keep `r` bound to the projected reborrow carrier: {all_text:?}"
    );
    assert!(
        all_text.iter().any(|text| {
            text.contains("snap == __trust_wp_reborrow_")
                || text.contains("__trust_wp_reborrow_ == snap")
        }),
        "pipeline facts should keep `snap` bound to the projected reborrow carrier: {all_text:?}"
    );
    assert!(
        all_text.iter().all(|text| {
            !text.contains("r == value")
                && !text.contains("value == r")
                && !text.contains("snap == value")
                && !text.contains("value == snap")
                && !text.contains("value == *value")
        }),
        "proof_assert pipeline must not collapse write_inner_borrow to scalar aliases: {all_text:?}"
    );
}

#[test]
fn rebor_in_pair_pipeline_preserves_projected_snapshot_ref_identity_2701() {
    let snapshot =
        collect_proof_assert_pipeline_snapshot_for(rebor_in_pair_fixture_source(), "rebor_in_pair");
    let all_text: Vec<String> = snapshot
        .substitution_facts
        .iter()
        .chain(snapshot.assumed_facts.iter())
        .chain(snapshot.prepared_preconditions.iter())
        .chain(snapshot.prepared_ensures.iter())
        .map(ToString::to_string)
        .collect();
    let ensures_text: Vec<String> = snapshot
        .prepared_ensures
        .iter()
        .map(ToString::to_string)
        .collect();

    assert!(
        all_text
            .iter()
            .any(|text| text.contains("*s == __trust_wp_reborrow_")
                && text.contains("field0_deref")),
        "snapshot!(p.0) should retain a deref alias to the projected reborrow carrier: {all_text:?}"
    );
    // The prepared goal `*s == b` must be phrased over the projected reborrow
    // carrier, never a scalarized snapshot. Two sound outcomes are accepted:
    // either the carrier comparison is retained as an ensure, or the exact
    // carrier substitutions normalize it to syntactic `true`. The strict
    // proof-assert lane deliberately retains that `true` slice so the authored
    // obligation still receives a replayable per-slice certificate.
    let precondition_text: Vec<String> = snapshot
        .prepared_preconditions
        .iter()
        .map(ToString::to_string)
        .collect();
    let carrier_ensure_retained = ensures_text.iter().any(|text| {
        text.contains("__trust_wp_reborrow_")
            && text.contains("field0_deref")
            && !text.contains("*12")
    });
    let carrier_goal_normalized_to_certified_truth = !ensures_text.is_empty()
        && ensures_text.iter().all(|text| text == "true")
        && precondition_text.iter().any(|text| {
            text.contains("*s == __trust_wp_reborrow_") && text.contains("field0_deref")
        })
        && precondition_text.iter().any(|text| {
            text.contains("b == __trust_wp_reborrow_") && text.contains("field0_deref")
        });
    assert!(
        carrier_ensure_retained || carrier_goal_normalized_to_certified_truth,
        "prepared proof_assert should compare the projected reborrow carrier, not a scalarized snapshot: ensures={ensures_text:?} preconditions={precondition_text:?}"
    );
    assert!(
        ensures_text.iter().all(|text| !text.contains("*12")),
        "prepared proof_assert must not dereference the scalar snapshot value: {ensures_text:?}"
    );
}

#[test]
fn proof_assert_driver_verifies_rebor_in_pair_2701() {
    let snapshot = collect_proof_assert_driver_summary(rebor_in_pair_fixture_source());

    assert_eq!(
        snapshot.proof_assert_verified, 1,
        "rebor_in_pair proof_assert should verify once snapshot!(p.0) keeps projected ref identity"
    );
    assert_eq!(
        snapshot.proof_assert_failed, 0,
        "rebor_in_pair proof_assert should not fail after the projected snapshot alias fix"
    );
    assert_eq!(
        snapshot.proof_assert_errors, 0,
        "rebor_in_pair proof_assert should not error after the projected snapshot alias fix"
    );
    assert_eq!(
        snapshot.exit_code, 0,
        "rebor_in_pair regression fixture should verify cleanly"
    );
}

#[test]
fn plain_reborrow_pipeline_uses_mut_borrow_child_carrier_2702() {
    let snapshot = collect_proof_assert_pipeline_snapshot_for(
        later_reborrow_not_final_fixture_source(),
        "not_final_borrow",
    );
    let all_text: Vec<String> = snapshot
        .substitution_facts
        .iter()
        .chain(snapshot.assumed_facts.iter())
        .chain(snapshot.prepared_preconditions.iter())
        .chain(snapshot.prepared_ensures.iter())
        .map(ToString::to_string)
        .collect();
    let ensures_text: Vec<String> = snapshot
        .prepared_ensures
        .iter()
        .map(ToString::to_string)
        .collect();

    assert!(
        all_text.iter().any(|text| text.contains("bor_rb")),
        "plain &mut *bor reborrows should use the MIR mut-borrow child carrier: {all_text:?}"
    );
    assert!(
        ensures_text
            .iter()
            .any(|text| text.contains("bor_rb") && text.contains("bor")),
        "prepared proof_assert should compare the child reborrow carrier with the parent, not a tautology: {ensures_text:?}"
    );
    assert!(
        ensures_text.iter().all(|text| !text.contains("bor == bor")),
        "prepared proof_assert must not collapse b1 == bor to bor == bor: {ensures_text:?}"
    );
    assert!(
        snapshot
            .assumed_facts
            .iter()
            .map(ToString::to_string)
            .all(|text| {
                !(text.contains("bor_rb2")
                    && (text.contains("== bor)") || text.ends_with("== bor")))
            }),
        "generated snapshot assumptions must not retain the stale child == parent alias: {:?}",
        snapshot.assumed_facts
    );
}

#[test]
fn proof_assert_driver_rejects_not_final_plain_reborrow_2702() {
    let snapshot = collect_proof_assert_driver_summary(later_reborrow_not_final_fixture_source());

    assert_eq!(
        snapshot.proof_assert_verified, 0,
        "non-final reborrow equality must not verify as a parent identity"
    );
    assert!(
        snapshot.proof_assert_failed + snapshot.proof_assert_errors > 0,
        "non-final reborrow equality should be reported as a proof_assert failure/error, not a false accept: {snapshot:?}"
    );
    assert_ne!(
        snapshot.exit_code, 0,
        "proof_assert rejection should make the driver summary fail"
    );
}

fn is_final_parent_alias_text(text: &str, parent: &str) -> bool {
    (text.contains("_rb") && text.contains(&format!(" == {parent})")))
        || (text.contains(&format!("({parent} == ")) && text.contains("_rb"))
}

#[test]
fn final_plain_reborrow_inspect_keeps_parent_alias_2702() {
    let snapshot = collect_proof_assert_pipeline_snapshot_for(
        inspect_no_gen_fixture_source(),
        "inspect_no_gen",
    );
    let assumed_text: Vec<String> = snapshot
        .assumed_facts
        .iter()
        .map(ToString::to_string)
        .collect();
    let prepared_text: Vec<String> = snapshot
        .prepared_preconditions
        .iter()
        .chain(snapshot.prepared_ensures.iter())
        .map(ToString::to_string)
        .collect();

    assert!(
        assumed_text
            .iter()
            .any(|text| is_final_parent_alias_text(text, "x")),
        "final plain reborrow should retain the child == parent alias across non-mutating inspect uses: {assumed_text:?}"
    );
    assert!(
        prepared_text
            .iter()
            .any(|text| is_final_parent_alias_text(text, "x")),
        "prepared proof_assert context should retain the final child == parent alias: {prepared_text:?}"
    );
}

#[test]
fn proof_assert_driver_verifies_inspect_no_gen_final_reborrow_2702() {
    let snapshot = collect_proof_assert_driver_summary(inspect_no_gen_fixture_source());

    assert_eq!(
        snapshot.proof_assert_verified, 1,
        "inspect_no_gen proof_assert should verify from the final plain-reborrow alias"
    );
    assert_eq!(
        snapshot.proof_assert_failed, 0,
        "inspect_no_gen proof_assert should not fail"
    );
    assert_eq!(
        snapshot.proof_assert_errors, 0,
        "inspect_no_gen proof_assert should not be inconclusive/error"
    );
    assert_eq!(
        snapshot.exit_code, 0,
        "inspect_no_gen regression fixture should verify cleanly"
    );
}

#[test]
fn proof_assert_driver_verifies_shallow_borrow_no_gen_final_reborrow_2702() {
    let snapshot = collect_proof_assert_driver_summary(shallow_borrow_no_gen_fixture_source());

    assert_eq!(
        snapshot.proof_assert_verified, 1,
        "shallow_borrow_no_gen proof_assert should verify from the final plain-reborrow alias"
    );
    assert_eq!(
        snapshot.proof_assert_failed, 0,
        "shallow_borrow_no_gen proof_assert should not fail"
    );
    assert_eq!(
        snapshot.proof_assert_errors, 0,
        "shallow_borrow_no_gen proof_assert should not be inconclusive/error"
    );
    assert_eq!(
        snapshot.exit_code, 0,
        "shallow_borrow_no_gen regression fixture should verify cleanly"
    );
}

#[test]
fn shared_proof_assert_driver_verifies_contracted_and_contractless_hosts_2332() {
    let snapshot = collect_proof_assert_driver_summary(
        contracted_and_contractless_proof_assert_fixture_source(),
    );

    assert!(
        snapshot
            .contracted_paths
            .iter()
            .any(|path| path == "contracted" || path.ends_with("::contracted")),
        "fixture should include a contracted proof_assert host: {:?}",
        snapshot.contracted_paths
    );
    assert!(
        snapshot
            .contractless_paths
            .iter()
            .any(|path| path == "contractless" || path.ends_with("::contractless")),
        "fixture should include a contractless proof_assert host: {:?}",
        snapshot.contractless_paths
    );
    assert_eq!(
        snapshot.proof_assert_verified, 2,
        "shared driver should verify one proof_assert from each host kind"
    );
    assert_eq!(
        snapshot.proof_assert_failed, 0,
        "host-driver regression fixture should not fail proof_assert verification"
    );
    assert_eq!(
        snapshot.proof_assert_errors, 0,
        "host-driver regression fixture should not report proof_assert errors"
    );
    assert_eq!(
        snapshot.exit_code, 0,
        "shared driver regression fixture should verify cleanly"
    );
}

#[test]
fn proof_assert_driver_verifies_ghost_seq_push_back_2616() {
    let snapshot =
        collect_proof_assert_driver_summary(ghost_seq_push_back_proof_assert_fixture_source());

    assert!(
        snapshot
            .contractless_paths
            .iter()
            .any(|path| path == "ghost_seq_push_back_proof_assert"
                || path.ends_with("::ghost_seq_push_back_proof_assert")),
        "fixture should route through the contractless proof_assert host: {:?}",
        snapshot.contractless_paths
    );
    assert_eq!(
        snapshot.proof_assert_verified, 1,
        "ghost Seq proof_assert should verify once proof_assert dispatch synthesizes mutation-continued mut-borrow bindings"
    );
    assert_eq!(
        snapshot.proof_assert_failed, 0,
        "ghost Seq proof_assert should not fail once the mutation bridge is active"
    );
    assert_eq!(
        snapshot.proof_assert_errors, 0,
        "ghost Seq proof_assert should not demote to unknown after the driver fix"
    );
    assert_eq!(
        snapshot.exit_code, 0,
        "ghost Seq proof_assert regression fixture should verify cleanly"
    );
}

#[test]
fn ghost_seq_push_back_proof_assert_pipeline_snapshot_2616() {
    let snapshot = collect_proof_assert_pipeline_snapshot_for(
        ghost_seq_push_back_proof_assert_fixture_source(),
        "ghost_seq_push_back_proof_assert",
    );
    let prepared_preconditions: Vec<String> = snapshot
        .prepared_preconditions
        .iter()
        .map(ToString::to_string)
        .collect();
    let prepared_ensures: Vec<String> = snapshot
        .prepared_ensures
        .iter()
        .map(ToString::to_string)
        .collect();

    assert!(
        prepared_ensures
            .iter()
            .any(|text| text.contains("call_4.push_back(30).index_logic(0) == 30")),
        "ghost Seq proof_assert should inline the ghost-helper post-state fact into the assertion: {prepared_ensures:?}"
    );
    assert!(
        prepared_ensures
            .iter()
            .all(|text| !text.contains("^call_4.index_logic(0)")),
        "ghost Seq proof_assert should no longer leave the assertion on the symbolic final carrier once the snapshot fact is available: {prepared_ensures:?}"
    );
    assert!(
        prepared_preconditions
            .iter()
            .any(|text| text.contains("call_4 == seq_empty()")),
        "ghost Seq proof_assert should retain the symbolic pre-state carrier: {prepared_preconditions:?}"
    );
    assert!(
        prepared_preconditions
            .iter()
            .any(|text| text.contains("call_4.len() == 0")),
        "ghost Seq proof_assert should retain the empty-seq precondition: {prepared_preconditions:?}"
    );
    assert!(
        prepared_preconditions
            .iter()
            .any(|text| text.contains("^call_4@ == call_4.push_back(30)")),
        "ghost Seq proof_assert should project the ghost-helper post-state fact into Seq view space: {prepared_preconditions:?}"
    );
    assert!(
        prepared_preconditions
            .iter()
            .all(|text| !text.contains("v == call_4")),
        "ghost Seq proof_assert should not fall back to the stale pre-mutation alias: {prepared_preconditions:?}"
    );
}

#[test]
fn ghost_side_channel_call_obligations_are_preserved() {
    let snapshot = collect_proof_assert_pipeline_snapshot_for(
        ghost_side_channel_obligation_fixture_source(),
        "ghost_side_channel_obligation",
    );

    let prepared_ensures: Vec<String> = snapshot
        .prepared_ensures
        .iter()
        .map(ToString::to_string)
        .collect();

    assert!(
        prepared_ensures.iter().any(|text| text == "false"),
        "ghost side-channel postconditions must carry their matching call obligations: {prepared_ensures:?}"
    );
}

#[test]
fn closure_caller_capture_proof_assert_pipeline_snapshot() {
    let source = closure_caller_capture_verify_fixture_source();
    let snapshot = collect_proof_assert_pipeline_snapshot_for(&source, "direct_fnmut_call");
    let prepared_preconditions_expr = snapshot.prepared_preconditions.clone();
    let prepared_preconditions: Vec<String> = snapshot
        .prepared_preconditions
        .iter()
        .map(ToString::to_string)
        .collect();
    let prepared_ensures: Vec<String> = snapshot
        .prepared_ensures
        .iter()
        .map(ToString::to_string)
        .collect();
    assert!(
        prepared_preconditions
            .iter()
            .any(|text| text.contains("x == 10")),
        "caller precondition should survive in prepared preconditions: {prepared_preconditions:?}"
    );
    assert!(
        prepared_preconditions
            .iter()
            .any(|text| text.contains("^x == (x + 1)")),
        "closure call ensure should still be grounded into the VC: {prepared_preconditions:?}"
    );
    assert!(
        prepared_preconditions
            .iter()
            .all(|text| !text.contains("c == __trust_wp_tuple1(^^x)")),
        "double-final closure capture alias should not be merged into prepared preconditions: {prepared_preconditions:?}"
    );
    assert!(
        prepared_ensures
            .iter()
            .all(|text| !text.contains("c == __trust_wp_tuple1(^^x)")),
        "double-final closure capture alias should not be merged into prepared ensures: {prepared_ensures:?}"
    );
    assert!(
        snapshot
            .substitution_facts
            .iter()
            .any(|expr| format!("{expr}").contains("c == __trust_wp_tuple1(^^x)")),
        "expected the closure carrier substitution fact to remain available in the snapshot"
    );
    assert!(
        snapshot
            .call_assumptions
            .iter()
            .any(|expr| format!("{expr}").contains("^x")),
        "expected proof_assert call assumptions to carry the mutating closure post-state fact"
    );
    assert!(
        snapshot
            .call_effect_expr
            .as_ref()
            .map(|expr| matches!(
                expr,
                PureExpr::LetAssume { .. } | PureExpr::LetObligation { .. } | PureExpr::Ite(..)
            ))
            .unwrap_or(false),
        "expected the preserved call-effect expression to retain wrapper structure"
    );
    assert!(
        snapshot.has_mutating_call_effect,
        "expected extraction to preserve mutating-call provenance"
    );
    assert_eq!(
        diagnose_identity_final_value_synthesis_skip_with_expr(
            false,
            &prepared_preconditions_expr,
            &snapshot.call_assumptions,
            snapshot.call_effect_expr.as_ref(),
        ),
        Some(IdentityFinalValueSynthesisSkipReason::MutatingOrOpaqueCallAssumption),
        "the preserved wrapper tree still lacks mutating provenance, so the bridge should report the exact opaque-call blocker"
    );
    assert_eq!(
        diagnose_identity_final_value_synthesis_skip(
            false,
            &prepared_preconditions_expr,
            &snapshot.call_assumptions,
        ),
        Some(IdentityFinalValueSynthesisSkipReason::MutatingOrOpaqueCallAssumption),
        "wrapper-level identity final value synthesis should report the raw mutating assumption as the skip reason"
    );
    assert!(
        snapshot
            .substitution_facts
            .iter()
            .all(|expr| !format!("{expr}").contains("x == ^x")),
        "snapshot substitution facts should drop the stale self-alias before driver merge"
    );
}
