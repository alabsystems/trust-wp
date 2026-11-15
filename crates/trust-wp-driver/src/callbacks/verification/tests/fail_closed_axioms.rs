// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::{HashMap, HashSet};

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_interface::interface::Compiler;
use rustc_middle::{
    mir::{Location, Rvalue, StatementKind},
    ty::TyCtxt,
};
use trust_wp_core::{
    formula::{BinOp, PureExpr},
    logic::LogicFnDef,
};
use trust_wp_driver::StdSpec;

use super::rustc_callback_harness::run_test_compiler;
use crate::{
    callbacks::{
        discovery::find_contract_functions,
        ghost_context::collect_trusted_proof_assert_assumptions_for_assert,
        helpers::build_proof_assert_setup,
        parsing::build_user_spec_table,
        proof_assert_leading_calls::collect_leading_proof_assert_assumptions,
        verification::{downgrade_unverified_logic_specs, filter_downstream_logic_fns},
    },
    logic::extract_logic_fn_defs,
    mir_analysis::{extract::extract_return_expr_with_context, resolve_arg_names_or_warn},
    proof_assert::ProofAssert,
};

fn spec(requires: &[&str], ensures: &[&str]) -> StdSpec {
    StdSpec {
        inv_requires: Vec::new(),
        capture_inv_requires: Vec::new(),
        requires: requires.iter().map(|s| (*s).to_string()).collect(),
        ensures: ensures.iter().map(|s| (*s).to_string()).collect(),
        param_names: None,
    }
}

fn contains_gt_assumption(exprs: &[PureExpr], var: &str, rhs: i64) -> bool {
    // A call postcondition is scoped under the call's own preconditions
    // (`pre ==> post`); look through that guard.
    exprs.iter().any(|expr| {
        let expr = match expr {
            PureExpr::BinOp(_, BinOp::Implies, post) => post.as_ref(),
            other => other,
        };
        matches!(
            expr,
            PureExpr::BinOp(lhs, BinOp::Gt, rhs_expr)
                if matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == var)
                    && matches!(rhs_expr.as_ref(), PureExpr::Int(value) if *value == rhs)
        )
    })
}

fn proof_assert_source() -> &'static str {
    r#"
#[doc = "trust-wp:logic:"]
#[doc = "trust-wp:ensures:x > 1"]
pub fn lemma(x: i32) -> i32 {
    x
}

pub fn caller(x: i32) {
    let proof = || {
        lemma(x);
        true
    };
    let _ = proof();
}
"#
}

fn call_spec_source() -> &'static str {
    r#"
#[doc = "trust-wp:logic:"]
#[doc = "trust-wp:requires:x > 0"]
#[doc = "trust-wp:ensures:x > 1"]
pub fn lemma(x: i32) -> i32 {
    x
}

pub fn caller(y: i32) {
    let _ = lemma(y);
}
"#
}

fn trusted_proof_assert_source() -> &'static str {
    r#"
#[doc = "trust-wp:logic:"]
#[doc = "trust-wp:ensures:x > 1"]
pub fn lemma(x: i32) -> i32 {
    x
}

pub fn caller(x: i32) {
    let proof = || {
        lemma(x);
        x > 0
    };
    let _ = proof();
}
"#
}

fn path_matches_name(tcx: TyCtxt<'_>, def_id: DefId, name: &str) -> bool {
    let path = tcx.def_path_str(def_id);
    path == name || path.ends_with(&format!("::{name}"))
}

fn find_body_owner(tcx: TyCtxt<'_>, name: &str) -> LocalDefId {
    tcx.hir_body_owners()
        .find(|local_def_id| path_matches_name(tcx, local_def_id.to_def_id(), name))
        .expect("requested body owner should exist")
}

fn first_closure_proof_assert(
    tcx: TyCtxt<'_>,
    containing_fn: LocalDefId,
    expr_text: &str,
    trusted: bool,
) -> ProofAssert {
    let body = tcx.optimized_mir(containing_fn.to_def_id());
    for (bb_idx, bb_data) in body.basic_blocks.iter_enumerated() {
        for (stmt_idx, stmt) in bb_data.statements.iter().enumerate() {
            let Some(closure_def_id) = (match stmt.kind {
                StatementKind::Assign((
                    _,
                    Rvalue::Aggregate(rustc_middle::mir::AggregateKind::Closure(def_id, _), _),
                )) => Some(def_id),
                _ => None,
            }) else {
                continue;
            };

            return ProofAssert {
                span: stmt.source_info.span,
                containing_fn,
                expr_text: Some(expr_text.to_string()),
                trusted,
                closure_def_id: Some(closure_def_id),
                source_scope: Some(stmt.source_info.scope),
                location: Some(Location {
                    block: bb_idx,
                    statement_index: stmt_idx,
                }),
            };
        }
    }
    panic!("proof_assert-style closure should be present in caller body");
}

#[test]
fn downgrade_unverified_logic_specs_clears_only_unverified_ensures() {
    let mut user_specs = HashMap::from([
        (
            "verified_logic".to_string(),
            spec(&["x > 0"], &["result == x"]),
        ),
        (
            "unverified_logic".to_string(),
            spec(&["x > 1"], &["result == x + 1"]),
        ),
        ("normal_fn".to_string(), spec(&["y > 2"], &["result == y"])),
    ]);

    downgrade_unverified_logic_specs(&mut user_specs, |name| name == "unverified_logic");

    assert_eq!(
        user_specs["verified_logic"].requires,
        vec!["x > 0".to_string()]
    );
    assert_eq!(
        user_specs["verified_logic"].ensures,
        vec!["result == x".to_string()]
    );
    assert_eq!(
        user_specs["unverified_logic"].requires,
        vec!["x > 1".to_string()]
    );
    assert!(
        user_specs["unverified_logic"].ensures.is_empty(),
        "unverified logic specs should keep requires but drop ensures"
    );
    assert_eq!(
        user_specs["normal_fn"].ensures,
        vec!["result == y".to_string()],
        "non-logic specs should be unchanged"
    );
}

#[test]
fn filter_downstream_logic_fns_neutralizes_unverified_entries_in_place() {
    let mut second = LogicFnDef::new(
        "second".to_string(),
        "test::second".to_string(),
        vec![],
        PureExpr::Int(2),
    );
    second.set_ensures(vec![PureExpr::Bool(true)]);
    let logic_fns = vec![
        LogicFnDef::new(
            "first".to_string(),
            "test::first".to_string(),
            vec![],
            PureExpr::Int(1),
        ),
        second,
        LogicFnDef::new(
            "third".to_string(),
            "test::third".to_string(),
            vec![],
            PureExpr::Int(3),
        ),
    ];
    let unverified_axioms = HashSet::from(["test::second".to_string()]);

    let filtered = filter_downstream_logic_fns(&logic_fns, &unverified_axioms);
    let filtered_names: Vec<&str> = filtered.iter().map(|lf| lf.name()).collect();

    // All entries are retained in order (so mode_overrides stay aligned and the
    // declaration remains available for sort resolution) ...
    assert_eq!(
        filtered_names,
        vec!["first", "second", "third"],
        "downstream set retains every entry, preserving order"
    );

    // ... but the unverified entry is neutralized: forced opaque (no body
    // axiom) with its ensures cleared (no spec axiom). This is soundness-
    // equivalent to dropping it, without the demoting sort fallback.
    let neutralized = &filtered[1];
    assert!(
        neutralized.is_opaque(),
        "unverified logic function must be forced opaque"
    );
    assert!(
        neutralized.ensures().is_empty(),
        "unverified logic function must have its ensures cleared"
    );

    // Verified entries are untouched.
    assert!(!filtered[0].is_opaque());
    assert!(!filtered[2].is_opaque());
}

#[derive(Default)]
struct ProofAssertSetupSnapshot {
    raw_assumptions: Vec<PureExpr>,
    downgraded_assumptions: Vec<PureExpr>,
    downgraded_lemma_ensures: Vec<String>,
    warnings: usize,
    ran: bool,
}

struct ProofAssertSetupCallbacks {
    snapshot: ProofAssertSetupSnapshot,
}

impl Callbacks for ProofAssertSetupCallbacks {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let contracts = find_contract_functions(tcx);
        let logic_fns = extract_logic_fn_defs(tcx);
        let raw_user_specs = build_user_spec_table(tcx, &contracts, &[]);
        let lemma_def_id = contracts
            .iter()
            .find(|contract| path_matches_name(tcx, contract.def_id, "lemma"))
            .map(|contract| contract.def_id)
            .expect("lemma contract should be discovered");
        let caller_local_def_id = find_body_owner(tcx, "caller");
        let proof_assert =
            first_closure_proof_assert(tcx, caller_local_def_id, "lemma(x); true", false);

        let mut downgraded_user_specs = raw_user_specs.clone();
        downgrade_unverified_logic_specs(&mut downgraded_user_specs, |def_id| {
            *def_id == lemma_def_id
        });
        let logic_method_names: HashSet<String> = logic_fns
            .iter()
            .filter(|logic_fn| {
                logic_fn
                    .params()
                    .first()
                    .is_some_and(|param| param == "self")
            })
            .map(|logic_fn| logic_fn.name().to_string())
            .collect();
        let (setup, warnings) =
            build_proof_assert_setup(tcx, &contracts, &logic_fns, &downgraded_user_specs);

        self.snapshot.raw_assumptions = collect_leading_proof_assert_assumptions(
            tcx,
            &proof_assert,
            &logic_fns,
            &raw_user_specs,
            &logic_method_names,
        )
        .0;
        self.snapshot.downgraded_assumptions = collect_leading_proof_assert_assumptions(
            tcx,
            &proof_assert,
            &logic_fns,
            &setup.user_specs,
            &logic_method_names,
        )
        .0;
        self.snapshot.downgraded_lemma_ensures = setup
            .user_specs
            .get(&lemma_def_id)
            .expect("lemma spec should be present in proof_assert setup")
            .ensures
            .clone();
        self.snapshot.warnings = warnings;
        self.snapshot.ran = true;
        Compilation::Stop
    }
}

fn collect_proof_assert_setup_snapshot(source: &str) -> ProofAssertSetupSnapshot {
    let mut callbacks = ProofAssertSetupCallbacks {
        snapshot: ProofAssertSetupSnapshot::default(),
    };
    run_test_compiler(source, "trust_wp_fail_closed_proof_assert", &mut callbacks);
    assert!(callbacks.snapshot.ran, "proof_assert callback should run");
    callbacks.snapshot
}

#[test]
fn build_proof_assert_setup_uses_downgraded_specs_for_leading_calls() {
    let snapshot = collect_proof_assert_setup_snapshot(proof_assert_source());

    assert_eq!(
        snapshot.warnings, 0,
        "fixture should parse without warnings"
    );
    assert!(
        contains_gt_assumption(&snapshot.raw_assumptions, "x", 1),
        "raw user_specs should still inject the lemma postcondition"
    );
    assert!(
        snapshot.downgraded_assumptions.is_empty(),
        "downgraded proof_assert setup should suppress leading-call assumptions from unverified logic ensures"
    );
    assert!(
        snapshot.downgraded_lemma_ensures.is_empty(),
        "build_proof_assert_setup should carry the downgraded user_specs rather than rebuilding raw specs"
    );
}

#[derive(Default)]
struct CallSpecEffectsSnapshot {
    raw_assumptions: Vec<PureExpr>,
    raw_obligations: Vec<PureExpr>,
    downgraded_assumptions: Vec<PureExpr>,
    downgraded_obligations: Vec<PureExpr>,
    ran: bool,
}

struct CallSpecEffectsCallbacks {
    snapshot: CallSpecEffectsSnapshot,
}

impl Callbacks for CallSpecEffectsCallbacks {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let contracts = find_contract_functions(tcx);
        let raw_user_specs = build_user_spec_table(tcx, &contracts, &[]);
        let lemma_def_id = contracts
            .iter()
            .find(|contract| path_matches_name(tcx, contract.def_id, "lemma"))
            .map(|contract| contract.def_id)
            .expect("lemma contract should be discovered");
        let caller_def_id = find_body_owner(tcx, "caller").to_def_id();

        let mut downgraded_user_specs = raw_user_specs.clone();
        downgrade_unverified_logic_specs(&mut downgraded_user_specs, |def_id| {
            *def_id == lemma_def_id
        });

        let body = tcx.optimized_mir(caller_def_id);
        let arg_names = resolve_arg_names_or_warn(tcx, caller_def_id, None);
        let trait_specs: HashMap<DefId, StdSpec> = HashMap::new();

        let (_raw_expr, raw_effects) = extract_return_expr_with_context(
            tcx,
            body,
            &arg_names,
            &raw_user_specs,
            &trait_specs,
            &HashMap::new(),
        );
        let (_downgraded_expr, downgraded_effects) = extract_return_expr_with_context(
            tcx,
            body,
            &arg_names,
            &downgraded_user_specs,
            &trait_specs,
            &HashMap::new(),
        );

        self.snapshot.raw_assumptions = raw_effects.assumptions;
        self.snapshot.raw_obligations = raw_effects.obligations;
        self.snapshot.downgraded_assumptions = downgraded_effects.assumptions;
        self.snapshot.downgraded_obligations = downgraded_effects.obligations;
        self.snapshot.ran = true;
        Compilation::Stop
    }
}

fn collect_call_spec_snapshot(source: &str) -> CallSpecEffectsSnapshot {
    let mut callbacks = CallSpecEffectsCallbacks {
        snapshot: CallSpecEffectsSnapshot::default(),
    };
    run_test_compiler(source, "trust_wp_fail_closed_call_spec", &mut callbacks);
    assert!(callbacks.snapshot.ran, "call-spec callback should run");
    callbacks.snapshot
}

#[test]
fn downgraded_call_specs_keep_requires_but_drop_ensures() {
    let snapshot = collect_call_spec_snapshot(call_spec_source());

    assert!(
        contains_gt_assumption(&snapshot.raw_assumptions, "y", 1),
        "raw user_specs should inject the logic-function postcondition as a call assumption"
    );
    assert!(
        snapshot.downgraded_assumptions.is_empty(),
        "downgraded user_specs should not inject ensures-derived call assumptions"
    );
    assert!(
        contains_gt_assumption(&snapshot.raw_obligations, "y", 0),
        "raw user_specs should still enforce the call precondition"
    );
    assert!(
        contains_gt_assumption(&snapshot.downgraded_obligations, "y", 0),
        "downgraded user_specs should preserve requires-derived obligations"
    );
}

#[derive(Default)]
struct TrustedAssumptionSnapshot {
    raw_assumptions: Vec<PureExpr>,
    downgraded_assumptions: Vec<PureExpr>,
    raw_warnings: usize,
    downgraded_warnings: usize,
    ran: bool,
}

struct TrustedAssumptionCallbacks {
    snapshot: TrustedAssumptionSnapshot,
}

impl Callbacks for TrustedAssumptionCallbacks {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let contracts = find_contract_functions(tcx);
        let logic_fns = extract_logic_fn_defs(tcx);
        let raw_user_specs = build_user_spec_table(tcx, &contracts, &[]);
        let lemma_def_id = contracts
            .iter()
            .find(|contract| path_matches_name(tcx, contract.def_id, "lemma"))
            .map(|contract| contract.def_id)
            .expect("lemma contract should be discovered");
        let caller_local_def_id = find_body_owner(tcx, "caller");
        let proof_assert = first_closure_proof_assert(tcx, caller_local_def_id, "x > 0", true);

        let mut downgraded_user_specs = raw_user_specs.clone();
        downgrade_unverified_logic_specs(&mut downgraded_user_specs, |def_id| {
            *def_id == lemma_def_id
        });

        let (mut raw_assumptions, raw_trusted_assumption, raw_warnings) =
            collect_trusted_proof_assert_assumptions_for_assert(
                tcx,
                &proof_assert,
                &raw_user_specs,
                &logic_fns,
            );
        let (mut downgraded_assumptions, downgraded_trusted_assumption, downgraded_warnings) =
            collect_trusted_proof_assert_assumptions_for_assert(
                tcx,
                &proof_assert,
                &downgraded_user_specs,
                &logic_fns,
            );

        if let Some(assumption) = raw_trusted_assumption {
            raw_assumptions.push(assumption);
        }
        if let Some(assumption) = downgraded_trusted_assumption {
            downgraded_assumptions.push(assumption);
        }

        self.snapshot.raw_assumptions = raw_assumptions;
        self.snapshot.downgraded_assumptions = downgraded_assumptions;
        self.snapshot.raw_warnings = raw_warnings;
        self.snapshot.downgraded_warnings = downgraded_warnings;
        self.snapshot.ran = true;
        Compilation::Stop
    }
}

fn collect_trusted_assumption_snapshot(source: &str) -> TrustedAssumptionSnapshot {
    let mut callbacks = TrustedAssumptionCallbacks {
        snapshot: TrustedAssumptionSnapshot::default(),
    };
    run_test_compiler(source, "trust_wp_fail_closed_trusted_pa", &mut callbacks);
    assert!(
        callbacks.snapshot.ran,
        "trusted proof_assert callback should run"
    );
    callbacks.snapshot
}

#[test]
fn trusted_proof_assert_assumptions_do_not_include_downgraded_logic_postconditions() {
    let snapshot = collect_trusted_assumption_snapshot(trusted_proof_assert_source());

    assert_eq!(
        snapshot.raw_warnings, 0,
        "fixture should parse without warnings"
    );
    assert_eq!(
        snapshot.downgraded_warnings, 0,
        "downgraded fixture should parse without warnings"
    );
    assert!(
        contains_gt_assumption(&snapshot.raw_assumptions, "x", 1),
        "raw trusted-proof-assert assumptions should include the leading logic postcondition"
    );
    assert!(
        contains_gt_assumption(&snapshot.raw_assumptions, "x", 0),
        "trusted proof_assert expressions should still be recorded"
    );
    assert!(
        !contains_gt_assumption(&snapshot.downgraded_assumptions, "x", 1),
        "downgraded trusted-proof-assert assumptions should drop leading logic postconditions"
    );
    assert!(
        contains_gt_assumption(&snapshot.downgraded_assumptions, "x", 0),
        "downgrade should not remove the trusted proof_assert expression itself"
    );
}
