// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    fs,
    sync::{
        atomic::{AtomicU64, Ordering},
        Arc,
    },
};

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::{mir::VarDebugInfoContents, ty::TyCtxt};
use trust_wp_core::formula::{ExprSort, NamedBindingValue};

use super::{
    infer_stable_loop_invariants, infer_unsigned_nonneg_invariants, infer_unsigned_nonneg_requires,
    BinOp, PureExpr,
};

const LOOP_VERIFY_TEST_CRATE_NAME: &str = "trust_wp_loop_verify_test";
static LOOP_VERIFY_TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

struct UnsignedInferenceResults {
    invariants: Vec<PureExpr>,
    requires: Vec<PureExpr>,
    debug_names: Vec<String>,
}

struct UnsignedInferenceCallbacks {
    fn_name: String,
    arg_names: Vec<String>,
    results: Option<UnsignedInferenceResults>,
    ran: bool,
}

impl Callbacks for UnsignedInferenceCallbacks {
    #[allow(clippy::elidable_lifetime_names)] // Matches rustc_driver::Callbacks trait signature
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let suffix = format!("::{}", self.fn_name);
        for local_def_id in tcx.hir_body_owners() {
            let def_id = local_def_id.to_def_id();
            let def_path = tcx.def_path_str(def_id);
            if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                continue;
            }

            let body = tcx.optimized_mir(def_id);
            let debug_names = body
                .var_debug_info
                .iter()
                .filter_map(|dbg| match &dbg.value {
                    VarDebugInfoContents::Place(place) if place.projection.is_empty() => {
                        Some(dbg.name.to_string())
                    }
                    _ => None,
                })
                .collect();

            self.results = Some(UnsignedInferenceResults {
                invariants: infer_unsigned_nonneg_invariants(body, &self.arg_names),
                requires: infer_unsigned_nonneg_requires(body, &self.arg_names),
                debug_names,
            });
            self.ran = true;
            break;
        }
        Compilation::Stop
    }
}

fn collect_unsigned_inference_results(
    source: &str,
    fn_name: &str,
    arg_names: &[&str],
) -> UnsignedInferenceResults {
    let unique = LOOP_VERIFY_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_loop_verify_unsigned_{}_{}",
        std::process::id(),
        unique
    ));
    fs::create_dir_all(&temp_dir).expect("create test temp dir");

    let source_path = temp_dir.join("test.rs");
    fs::write(&source_path, source).expect("write test source");

    let args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        LOOP_VERIFY_TEST_CRATE_NAME.to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = UnsignedInferenceCallbacks {
        fn_name: fn_name.to_string(),
        arg_names: arg_names.iter().map(|name| (*name).to_string()).collect(),
        results: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to locate function `{fn_name}` in rustc callback"
    );
    callbacks
        .results
        .expect("unsigned inference results should be collected")
}

// --- infer_unsigned_nonneg_{invariants,requires} tests (#1114) ---

#[test]
fn unsigned_arg_infers_single_nonneg_require_and_invariant() {
    let results = collect_unsigned_inference_results(
        r#"
pub fn f(u: usize) {
    let _ = u;
}
"#,
        "f",
        &["u"],
    );
    let expected = PureExpr::BinOp(
        Arc::new(PureExpr::Var("u".to_string(), Some(ExprSort::Int))),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );

    assert_eq!(
        results.requires,
        vec![expected.clone()],
        "unsigned arg should infer exactly one require"
    );
    assert_eq!(
        results.invariants,
        vec![expected],
        "unsigned arg should infer exactly one invariant"
    );
}

#[test]
fn signed_arg_does_not_infer_nonneg_facts() {
    let results = collect_unsigned_inference_results(
        r#"
pub fn f(i: i32) {
    let _ = i;
}
"#,
        "f",
        &["i"],
    );

    assert!(
        results.requires.is_empty(),
        "signed arg should not infer requires: {:?}",
        results.requires
    );
    assert!(
        results.invariants.is_empty(),
        "signed arg should not infer invariants: {:?}",
        results.invariants
    );
}

#[test]
fn duplicate_debug_names_do_not_duplicate_unsigned_invariants() {
    let results = collect_unsigned_inference_results(
        r#"
pub fn f(u: usize) -> usize {
    let u = u + 1;
    let u = u + 1;
    u
}
"#,
        "f",
        &["u"],
    );
    let duplicate_u_names = results
        .debug_names
        .iter()
        .filter(|name| name.as_str() == "u")
        .count();
    let expected = PureExpr::BinOp(
        Arc::new(PureExpr::Var("u".to_string(), Some(ExprSort::Int))),
        BinOp::Ge,
        Arc::new(PureExpr::Int(0)),
    );

    assert!(
        duplicate_u_names >= 2,
        "test should exercise duplicated debug names, got {:?}",
        results.debug_names
    );
    assert_eq!(
        results.invariants,
        vec![expected],
        "duplicate debug names should still infer one invariant"
    );
}

// --- infer_stable_loop_invariants tests (#1816) ---

fn make_pre_loop_assignments(
    entries: &[(&str, PureExpr)],
) -> std::collections::HashMap<String, NamedBindingValue> {
    entries
        .iter()
        .map(|(k, v)| (k.to_string(), NamedBindingValue::untyped(v.clone())))
        .collect()
}

#[test]
fn stable_invariant_unmodified_pre_loop_assignment_becomes_invariant() {
    let pre = make_pre_loop_assignments(&[("n", PureExpr::Int(10))]);
    let modified = vec!["i".to_string()];
    let result = infer_stable_loop_invariants(&[], &pre, &modified, &[], &[]);
    assert_eq!(result.len(), 1);
    assert_eq!(
        result[0],
        PureExpr::BinOp(
            Arc::new(PureExpr::Var("n".to_string(), None)),
            BinOp::Eq,
            Arc::new(PureExpr::Int(10)),
        )
    );
}

#[test]
fn stable_invariant_modified_pre_loop_assignment_excluded() {
    let pre = make_pre_loop_assignments(&[("i", PureExpr::Int(0))]);
    let modified = vec!["i".to_string()];
    let result = infer_stable_loop_invariants(&[], &pre, &modified, &[], &[]);
    assert!(
        result.is_empty(),
        "modified variable should not produce invariant: {result:?}"
    );
}

#[test]
fn stable_invariant_stable_requires_becomes_invariant() {
    // requires: n > 0 — n is unmodified
    let req = PureExpr::BinOp(
        Arc::new(PureExpr::Var("n".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );
    let pre = std::collections::HashMap::new();
    let modified = vec!["i".to_string()];
    let result =
        infer_stable_loop_invariants(std::slice::from_ref(&req), &pre, &modified, &[], &[]);
    assert_eq!(result.len(), 1);
    assert_eq!(result[0], req);
}

#[test]
fn stable_invariant_requires_referencing_modified_var_excluded() {
    // requires: i < n — i is modified
    let req = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    );
    let pre = std::collections::HashMap::new();
    let modified = vec!["i".to_string()];
    let result = infer_stable_loop_invariants(&[req], &pre, &modified, &[], &[]);
    assert!(
        result.is_empty(),
        "requires referencing modified var should not be inferred: {result:?}"
    );
}

#[test]
fn stable_invariant_deduplicates_against_existing() {
    let pre = make_pre_loop_assignments(&[("n", PureExpr::Int(10))]);
    let existing_inv = PureExpr::BinOp(
        Arc::new(PureExpr::Var("n".to_string(), None)),
        BinOp::Eq,
        Arc::new(PureExpr::Int(10)),
    );
    let modified: Vec<String> = vec![];
    let result = infer_stable_loop_invariants(&[], &pre, &modified, &[existing_inv], &[]);
    assert!(
        result.is_empty(),
        "should not duplicate existing invariant: {result:?}"
    );
}

#[test]
fn stable_invariant_mixed_modified_and_unmodified() {
    let pre = make_pre_loop_assignments(&[
        ("i", PureExpr::Int(0)),
        ("n", PureExpr::Int(10)),
        ("step", PureExpr::Int(1)),
    ]);
    let modified = vec!["i".to_string()];
    let result = infer_stable_loop_invariants(&[], &pre, &modified, &[], &[]);
    // n and step are unmodified — should get 2 invariants
    assert_eq!(
        result.len(),
        2,
        "expected 2 unmodified invariants, got: {result:?}"
    );
    let var_names: Vec<String> = result
        .iter()
        .filter_map(|e| {
            if let PureExpr::BinOp(lhs, BinOp::Eq, _) = e {
                if let PureExpr::Var(name, _) = lhs.as_ref() {
                    return Some(name.clone());
                }
            }
            None
        })
        .collect();
    assert!(var_names.contains(&"n".to_string()));
    assert!(var_names.contains(&"step".to_string()));
}

#[test]
fn stable_invariant_empty_inputs_empty_result() {
    let pre = std::collections::HashMap::new();
    let modified: Vec<String> = vec![];
    let result = infer_stable_loop_invariants(&[], &pre, &modified, &[], &[]);
    assert!(result.is_empty());
}

#[test]
fn stable_invariant_both_assignment_and_requires_inferred() {
    // pre_loop: n = 10 (unmodified)
    // requires: n > 0 (stable — n unmodified)
    let pre = make_pre_loop_assignments(&[("n", PureExpr::Int(10))]);
    let req = PureExpr::BinOp(
        Arc::new(PureExpr::Var("n".to_string(), None)),
        BinOp::Gt,
        Arc::new(PureExpr::Int(0)),
    );
    let modified = vec!["i".to_string()];
    let result =
        infer_stable_loop_invariants(std::slice::from_ref(&req), &pre, &modified, &[], &[]);
    assert_eq!(
        result.len(),
        2,
        "expected both assignment equality and stable requires: {result:?}"
    );
}

#[test]
fn stable_invariant_value_referencing_modified_var_excluded() {
    // pre_loop: n = i where i is modified — n == i would be unsound as invariant
    let pre = make_pre_loop_assignments(&[("n", PureExpr::Var("i".to_string(), None))]);
    let modified = vec!["i".to_string()];
    let result = infer_stable_loop_invariants(&[], &pre, &modified, &[], &[]);
    assert!(
        result.is_empty(),
        "assignment whose value references modified var should not be inferred: {result:?}"
    );
}

#[test]
fn stable_invariant_value_referencing_unmodified_var_included() {
    // pre_loop: n = m where m is also unmodified — n == m is safe
    let pre = make_pre_loop_assignments(&[("n", PureExpr::Var("m".to_string(), None))]);
    let modified = vec!["i".to_string()];
    let result = infer_stable_loop_invariants(&[], &pre, &modified, &[], &[]);
    assert_eq!(
        result.len(),
        1,
        "assignment whose value only references unmodified var should be inferred: {result:?}"
    );
}

#[test]
fn stable_invariant_rejects_fallback_arg_placeholder() {
    // pre_loop: __trust_wp_ghost_value = arg0 — arg0 is a synthetic fallback
    // placeholder from pre-loop call resolution, not a real function arg.
    // Inferring this as an invariant injects a TypeParam-sorted variable into
    // the loop encoder, triggering spurious sort-coercion fresh constants in
    // the preservation VC (bug/1743, #5226).
    let pre = make_pre_loop_assignments(&[(
        "__trust_wp_ghost_value",
        PureExpr::Var("arg0".to_string(), None),
    )]);
    let modified: Vec<String> = vec![];
    // Real function args: only `self`. `arg0` is NOT a real arg name.
    let arg_names = vec!["self".to_string()];
    let result = infer_stable_loop_invariants(&[], &pre, &modified, &[], &arg_names);
    assert!(
        result.is_empty(),
        "fallback arg{{N}} placeholder should not produce a stable invariant: {result:?}"
    );
}

#[test]
fn stable_invariant_accepts_real_arg_name_matching_placeholder_pattern() {
    // Edge case: if the user happens to have a real function argument named
    // `arg0`, treat it as a real variable, not a synthetic placeholder.
    let pre = make_pre_loop_assignments(&[("n", PureExpr::Var("arg0".to_string(), None))]);
    let modified: Vec<String> = vec![];
    let arg_names = vec!["arg0".to_string()];
    let result = infer_stable_loop_invariants(&[], &pre, &modified, &[], &arg_names);
    assert_eq!(
        result.len(),
        1,
        "assignment referencing real arg name (even if it matches the fallback pattern) \
         should be inferred: {result:?}"
    );
}
