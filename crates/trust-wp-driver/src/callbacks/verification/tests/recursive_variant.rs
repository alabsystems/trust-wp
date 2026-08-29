// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
    time::Duration,
};

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def_id::DefId;
use rustc_interface::interface::{Compiler, Config};
use rustc_middle::ty::TyCtxt;
use trust_wp_ay::{VerificationOutcome, VerificationResult};
use trust_wp_core::{
    formula::{BinOp, ExprSort, PureExpr},
    logic::TypeInvariantDef,
    TrackLevel,
};
use trust_wp_driver::{builtin_trust_wp_std_specs, StdSpec};

use super::rustc_callback_harness::{
    run_test_compiler, run_test_compiler_with_args, trust_wp_probe_args,
};
use crate::{
    callbacks::{
        callgraph, copy_mir_bodies,
        discovery::find_contract_functions,
        reporting::recursive_variant_mir_unavailable_warning,
        verification::{
            recursive_verify::{
                build_recursive_variant_requires, classify_variant_type,
                merge_recursive_variant_requires, record_recursive_structural_variant_evidence_gap,
                record_recursive_variant_evidence_gap_if_any, structural_variant_decreases,
                StructuralRecursiveField, VariantKind,
            },
            verify_contracts,
        },
        verification_context::VerificationRunConfig,
    },
    ghost::find_ghost_blocks,
    logic::extract_logic_fn_defs,
    mir_analysis::extract_recursive_call_args,
};

struct RecursiveVariantRequiresCallbacks {
    fn_name: String,
    arg_names: Vec<String>,
    base_requires: Vec<PureExpr>,
    path_conditions: Vec<PureExpr>,
    variant_requires: Option<Vec<PureExpr>>,
    ran: bool,
}

struct RecursiveCloneCallCallbacks {
    call_arg: Option<PureExpr>,
    variant_kind: Option<VariantKind>,
    ran: bool,
}

#[derive(Debug, Default)]
struct RecursiveVariantSummarySnapshot {
    verified: usize,
    failed: usize,
    errors: usize,
    warnings: usize,
    evidence_gaps: usize,
    exit_code: i32,
    rustc_exit_code: i32,
    ran: bool,
}

struct RecursiveVariantSummaryCallbacks {
    snapshot: RecursiveVariantSummarySnapshot,
}

fn install_recursive_variant_mir_borrowck_cache(config: &mut Config) {
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

impl Callbacks for RecursiveCloneCallCallbacks {
    #[allow(clippy::elidable_lifetime_names)] // Matches rustc_driver::Callbacks trait signature
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        for local_def_id in tcx.hir_body_owners() {
            let def_id = local_def_id.to_def_id();
            let def_path = tcx.def_path_str(def_id);
            if !def_path.ends_with("::clone") || !def_path.contains("List") {
                continue;
            }

            let arg_names = vec!["self".to_string()];
            let body = tcx.optimized_mir(def_id);
            let sites = extract_recursive_call_args(body, &arg_names, def_id, Some(tcx));
            self.call_arg = sites
                .first()
                .and_then(|site| site.call_args.first())
                .cloned();
            self.variant_kind = Some(classify_variant_type(
                tcx,
                def_id,
                &PureExpr::Var("self".to_string(), None),
                &arg_names,
            ));
            self.ran = true;
            break;
        }

        Compilation::Stop
    }
}

impl Callbacks for RecursiveVariantSummaryCallbacks {
    fn config(&mut self, config: &mut Config) {
        install_recursive_variant_mir_borrowck_cache(config);
    }

    #[allow(clippy::elidable_lifetime_names)] // Matches rustc_driver::Callbacks trait signature
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let contracts = find_contract_functions(tcx);
        let call_graph = callgraph::build_call_graph(tcx, &contracts);
        let recursive_fns = callgraph::detect_recursive_nodes(&call_graph);
        let logic_fn_defs = extract_logic_fn_defs(tcx);
        let ghost_blocks = find_ghost_blocks(tcx);
        let type_invariant_defs: Vec<TypeInvariantDef> = Vec::new();
        let trait_specs: HashMap<DefId, StdSpec> = HashMap::new();
        let trait_contracts = Vec::new();
        let trait_refinement_overrides = HashSet::new();
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
        self.snapshot.verified = summary.verified;
        self.snapshot.failed = summary.failed;
        self.snapshot.errors = summary.errors;
        self.snapshot.warnings = summary.warnings;
        self.snapshot.evidence_gaps = summary.evidence_gaps;
        self.snapshot.exit_code = summary.exit_code();
        self.snapshot.rustc_exit_code = summary.rustc_process_exit_code();
        self.snapshot.ran = true;
        Compilation::Stop
    }
}

fn collect_recursive_variant_test_invariants<'tcx>(
    tcx: TyCtxt<'tcx>,
    inputs: impl IntoIterator<Item = rustc_middle::ty::Ty<'tcx>>,
) -> Vec<TypeInvariantDef> {
    let mut seen_type_names = HashSet::new();
    inputs
        .into_iter()
        .filter_map(|arg_ty| {
            let inner_ty = match arg_ty.kind() {
                rustc_middle::ty::TyKind::Ref(_, inner, _) => *inner,
                _ => arg_ty,
            };
            let rustc_middle::ty::TyKind::Adt(adt_def, _) = inner_ty.kind() else {
                return None;
            };
            let type_name = tcx.def_path_str(adt_def.did());
            if !seen_type_names.insert(type_name.clone()) {
                return None;
            }
            Some(trust_wp_core::type_invariant_def! {
                type_name: type_name,
                self_param: "self".to_string(),
                param_sort: None,
                body: PureExpr::Bool(true),
                is_newtype: false,
                element_invariant_method: None,
            })
        })
        .collect()
}

impl Callbacks for RecursiveVariantRequiresCallbacks {
    #[allow(clippy::elidable_lifetime_names)] // Matches rustc_driver::Callbacks trait signature
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let suffix = format!("::{}", self.fn_name);
        for local_def_id in tcx.hir_body_owners() {
            let def_id = local_def_id.to_def_id();
            let def_path = tcx.def_path_str(def_id);
            if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                continue;
            }

            let sig = tcx.fn_sig(def_id).instantiate_identity();
            let type_invariants = collect_recursive_variant_test_invariants(
                tcx,
                sig.skip_binder().inputs().iter().copied(),
            );

            self.variant_requires = Some(build_recursive_variant_requires(
                tcx,
                def_id,
                &self.arg_names,
                &self.base_requires,
                &[], // no call_assumptions in unit tests
                &self.path_conditions,
                Some(&type_invariants),
            ));
            self.ran = true;
            break;
        }

        Compilation::Stop
    }
}

fn collect_recursive_variant_requires(
    source: &str,
    fn_name: &str,
    arg_names: &[&str],
    base_requires: Vec<PureExpr>,
    path_conditions: Vec<PureExpr>,
) -> Vec<PureExpr> {
    let mut callbacks = RecursiveVariantRequiresCallbacks {
        fn_name: fn_name.to_string(),
        arg_names: arg_names.iter().map(|name| (*name).to_string()).collect(),
        base_requires,
        path_conditions,
        variant_requires: None,
        ran: false,
    };
    run_test_compiler(
        source,
        "trust_wp_recursive_variant_requires",
        &mut callbacks,
    );

    assert!(
        callbacks.ran,
        "failed to locate function `{fn_name}` in rustc callback"
    );
    callbacks
        .variant_requires
        .expect("variant requires should be collected for requested function")
}

fn collect_recursive_variant_summary(source: &str) -> RecursiveVariantSummarySnapshot {
    let mut callbacks = RecursiveVariantSummaryCallbacks {
        snapshot: RecursiveVariantSummarySnapshot::default(),
    };
    run_test_compiler_with_args(
        source,
        "trust_wp_recursive_variant_summary",
        &trust_wp_probe_args(),
        &mut callbacks,
    );
    assert!(
        callbacks.snapshot.ran,
        "recursive variant summary callback should run"
    );
    callbacks.snapshot
}

#[test]
fn recursive_clone_tail_call_is_structural_subterm_variant_decrease() {
    let source = r#"
pub enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

impl<T: Clone> Clone for List<T> {
    fn clone(&self) -> Self {
        match self {
            List::Nil => List::Nil,
            List::Cons(t, tl) => List::Cons(Clone::clone(t), Box::new(Clone::clone(&*tl))),
        }
    }
}
"#;

    let mut callbacks = RecursiveCloneCallCallbacks {
        call_arg: None,
        variant_kind: None,
        ran: false,
    };
    run_test_compiler(source, "trust_wp_recursive_clone_tail", &mut callbacks);

    assert!(callbacks.ran, "failed to locate List<T>::clone");
    let call_arg = callbacks
        .call_arg
        .expect("recursive clone call should be extracted");
    let VariantKind::StructuralSubterm {
        root_name,
        recursive_fields,
    } = callbacks
        .variant_kind
        .expect("variant kind should be classified")
    else {
        panic!("self variant for List<T>::clone should classify as structural subterm");
    };
    assert!(
        structural_variant_decreases(&call_arg, &root_name, &recursive_fields),
        "recursive clone call arg should be a structural recursive field of self, got {call_arg:?}"
    );
    assert_eq!(recursive_fields.len(), 1);
    assert!(
        matches!(
            recursive_fields.as_slice(),
            [StructuralRecursiveField {
                index: 1,
                allow_field0_carriers: true,
            }]
        ),
        "List<T>::clone should identify the boxed tail as the only recursive structural field"
    );
}

#[test]
fn variant_decrease_with_logic_fn_verifies_when_axioms_provided() {
    use trust_wp_ay::{verify_function_with_modes, VerificationRequest};
    use trust_wp_core::logic::{LogicFnDef, LogicMode};

    // Model: recursive function f(v) with variant len(v).
    // Precondition: v > 0 (so v-1 >= 0).
    // Variant decrease: len(v-1) < len(v).
    // Logic fn: len(x) = x (identity, so len(v-1) = v-1 < v = len(v)).
    let logic_fn = LogicFnDef::new(
        "len".to_string(),
        "crate::len".to_string(),
        vec!["x".to_string()],
        PureExpr::Var("x".to_string(), None),
    )
    .with_mode(LogicMode::Open)
    .with_param_sorts(vec![Some(ExprSort::Int)])
    .with_return_sort(Some(ExprSort::Int));

    // requires: v > 0
    let req = PureExpr::BinOp(
        Arc::new(PureExpr::Var("v".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );
    // ensures: len(v - 1) < len(v)  (variant decrease condition)
    let call_variant = PureExpr::LogicFnCall {
        name: "len".to_string(),
        args: vec![PureExpr::BinOp(
            Arc::new(PureExpr::Var("v".to_string(), None)),
            BinOp::Sub,
            Arc::new(PureExpr::Int(1)),
        )],
    };
    let current_variant = PureExpr::LogicFnCall {
        name: "len".to_string(),
        args: vec![PureExpr::Var("v".to_string(), None)],
    };
    let decrease = PureExpr::BinOp(Arc::new(call_variant), BinOp::Lt, Arc::new(current_variant));

    let requires = [req];
    let ensures = [decrease];

    // With logic fn axiom: should VERIFY
    let result = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .logic_fns(Some(std::slice::from_ref(&logic_fn)))
            .track(Some(TrackLevel::Auto)),
    )
    .expect("encoding should succeed");
    assert!(
        matches!(result, VerificationResult::Verified(_)),
        "variant decrease should verify with logic fn axiom, got {result:?}"
    );

    // Without the defining axiom, keep only len's exact typed declaration.
    // This is the negative control: it must fail because len is uninterpreted,
    // not become Unknown through a missing-signature Int fallback.
    let opaque_logic_fn = logic_fn.clone().with_opaque(true);
    let result_no_axiom = verify_function_with_modes(
        VerificationRequest::new(&requires, &ensures)
            .logic_fns(Some(std::slice::from_ref(&opaque_logic_fn)))
            .track(Some(TrackLevel::Auto)),
    )
    .expect("encoding should succeed");
    assert!(
        matches!(result_no_axiom, VerificationResult::Failed(_)),
        "variant decrease should fail without logic fn axiom (len uninterpreted), got {result_no_axiom:?}"
    );
}

#[test]
fn recursive_variant_mir_unavailable_warning_is_explicit() {
    let warning = recursive_variant_mir_unavailable_warning("crate::f");
    assert!(
        warning.contains("warning"),
        "expected warning severity, got {warning}"
    );
    assert!(
        warning.contains("recursive with variants"),
        "warning should explain recursive+variant context, got {warning}"
    );
    assert!(
        warning.contains("variant decrease not checked"),
        "warning should explain skipped obligation, got {warning}"
    );
}

#[test]
fn recursive_variant_verified_without_provenance_records_evidence_gap_not_verified() {
    let mut counters = crate::callbacks::reporting::VerificationCounters::default();
    let outcome = VerificationOutcome::without_provenance(VerificationResult::Verified(None));

    let recorded = record_recursive_variant_evidence_gap_if_any(
        &outcome,
        "crate::f",
        "src/lib.rs:1:1",
        0,
        &mut counters,
    );

    assert!(recorded);
    assert_eq!(counters.verified, 0);
    assert_eq!(counters.evidence_gaps, 1);
    assert_eq!(counters.warnings, 1);
    assert_eq!(counters.failed, 0);
    assert_eq!(counters.errors, 0);
}

#[test]
fn recursive_structural_variant_decrease_counts_structural_gap_not_verified() {
    let mut counters = crate::callbacks::reporting::VerificationCounters::default();

    record_recursive_structural_variant_evidence_gap(
        "crate::structural_len",
        "src/lib.rs:1:1",
        0,
        "xs",
        &mut counters,
    );

    assert_eq!(counters.verified, 0);
    assert_eq!(counters.evidence_gaps, 1);
    assert_eq!(counters.warnings, 1);
    assert_eq!(counters.failed, 0);
    assert_eq!(counters.errors, 0);
}

#[test]
fn variant_only_structural_recursion_exits_2_not_0() {
    let source = r#"
use trust_wp::{check, variant};

pub enum List {
    Nil,
    Cons(u32, Box<List>),
}

#[check(terminates)]
#[variant(xs)]
pub fn structural_len(xs: &List) -> u32 {
    match xs {
        List::Nil => 0,
        List::Cons(_, tail) => 1 + structural_len(&**tail),
    }
}
"#;

    let summary = collect_recursive_variant_summary(source);

    assert_eq!(
        summary.verified, 0,
        "structural-only variant evidence must not count as clean verified"
    );
    assert_eq!(summary.failed, 0);
    assert_eq!(summary.errors, 0);
    assert_eq!(summary.evidence_gaps, 1);
    assert_eq!(summary.warnings, 1);
    assert_eq!(summary.exit_code, 2);
    assert_eq!(summary.rustc_exit_code, 2);
}

#[test]
fn recursive_variant_requires_insert_type_invariant_preconditions_before_path_conditions() {
    let source = r#"
pub struct NonNeg(i32);

pub fn quux(i: NonNeg) -> i32 {
    if i.0 <= 0 { 0 } else { quux(NonNeg(i.0 - 1)) }
}
"#;
    let variant_requires = collect_recursive_variant_requires(
        source,
        "quux",
        &["i"],
        vec![PureExpr::Bool(true)],
        vec![PureExpr::Bool(false)],
    );

    assert_eq!(
        variant_requires.len(),
        3,
        "recursive variant requests should add exactly one invariant \
         precondition for the NonNeg argument"
    );
    assert!(
        matches!(variant_requires.first(), Some(PureExpr::Bool(true))),
        "user requires should stay at the front of the recursive variant request"
    );
    match &variant_requires[1] {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            assert!(
                args.is_empty(),
                "type invariant preconditions should be zero-argument method calls"
            );
            assert!(
                method.contains("NonNeg"),
                "expected injected invariant method for NonNeg, got {method}"
            );
            assert!(
                matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "i"),
                "expected injected invariant receiver to be the recursive parameter `i`, got {receiver:?}"
            );
        }
        other => panic!("expected injected invariant method call, got {other:?}"),
    }
    assert!(
        matches!(variant_requires.get(2), Some(PureExpr::Bool(false))),
        "path conditions should remain after injected invariant preconditions"
    );
}

#[test]
fn recursive_variant_requires_deref_mut_reference_receivers_for_type_invariants() {
    let source = r#"
pub struct NonNeg(i32);

pub fn quux(i: &mut NonNeg) -> i32 {
    if i.0 <= 0 { 0 } else { quux(i) }
}
"#;
    let variant_requires = collect_recursive_variant_requires(
        source,
        "quux",
        &["i"],
        vec![PureExpr::Bool(true)],
        vec![PureExpr::Bool(false)],
    );

    assert_eq!(
        variant_requires.len(),
        3,
        "mutable reference parameters should still inject exactly one invariant precondition"
    );
    match &variant_requires[1] {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            assert!(args.is_empty());
            assert!(
                method.contains("NonNeg"),
                "expected injected invariant method for NonNeg, got {method}"
            );
            assert!(
                matches!(
                    receiver.as_ref(),
                    PureExpr::Deref(inner)
                        if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "i")
                ),
                "expected injected invariant receiver to dereference the recursive parameter `i`, got {receiver:?}"
            );
        }
        other => panic!("expected injected invariant method call, got {other:?}"),
    }
    assert!(
        matches!(variant_requires.get(2), Some(PureExpr::Bool(false))),
        "path conditions should remain after injected invariant preconditions for mutable references"
    );
}

#[test]
fn recursive_variant_requires_include_all_invariant_params_before_path_conditions() {
    let source = r#"
#[allow(dead_code)]
pub struct NonNeg(i32);
#[allow(dead_code)]
pub struct Positive(i32);

pub fn quux(left: NonNeg, right: Positive) -> i32 {
    if left.0 <= 0 { 0 } else { quux(NonNeg(left.0 - 1), right) }
}
"#;
    let variant_requires = collect_recursive_variant_requires(
        source,
        "quux",
        &["left", "right"],
        vec![PureExpr::Bool(true)],
        vec![PureExpr::Bool(false)],
    );

    assert_eq!(
        variant_requires.len(),
        4,
        "recursive variant requests should inject one invariant precondition per invariant-bearing parameter"
    );
    assert!(matches!(
        variant_requires.first(),
        Some(PureExpr::Bool(true))
    ));
    match &variant_requires[1] {
        PureExpr::MethodCall {
            receiver, method, ..
        } => {
            assert!(method.contains("NonNeg"));
            assert!(matches!(
                receiver.as_ref(),
                PureExpr::Var(name, _) if name == "left"
            ));
        }
        other => panic!("expected NonNeg invariant method call, got {other:?}"),
    }
    match &variant_requires[2] {
        PureExpr::MethodCall {
            receiver, method, ..
        } => {
            assert!(method.contains("Positive"));
            assert!(matches!(
                receiver.as_ref(),
                PureExpr::Var(name, _) if name == "right"
            ));
        }
        other => panic!("expected Positive invariant method call, got {other:?}"),
    }
    assert!(
        matches!(variant_requires.get(3), Some(PureExpr::Bool(false))),
        "path conditions should remain after all injected invariant preconditions"
    );
}

#[test]
fn recursive_variant_requires_preserve_existing_assumptions_without_invariants() {
    let base_requires = vec![PureExpr::Bool(true)];
    let path_conditions = vec![PureExpr::Bool(false)];

    let variant_requires =
        merge_recursive_variant_requires(&base_requires, &[], Vec::new(), &path_conditions);

    assert_eq!(
        variant_requires,
        vec![PureExpr::Bool(true), PureExpr::Bool(false)],
        "empty invariant injection should leave recursive variant assumptions unchanged"
    );
}
