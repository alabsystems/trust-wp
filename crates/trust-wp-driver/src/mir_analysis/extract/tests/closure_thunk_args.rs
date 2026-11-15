// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Primary (call_spec) pipeline: a capture-free, parameter-free closure
//! argument with a closed return value replaces the opaque `argN` fallback in
//! the callee's contract; any capturing closure keeps the fallback.
//! (option.rs `ok_or_else`)

use std::{
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use trust_wp_driver::builtin_trust_wp_std_specs;

use super::*;

static COUNTER: AtomicU64 = AtomicU64::new(0);

struct AssumptionCallbacks {
    fn_name: String,
    assumptions: Option<Vec<String>>,
}

impl Callbacks for AssumptionCallbacks {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_expansion<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let suffix = format!("::{}", self.fn_name);
        for local_def_id in tcx.hir_body_owners() {
            let def_path = tcx.def_path_str(local_def_id);
            if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                continue;
            }
            // Borrowck-shaped MIR (what the driver consumes); read before
            // borrowck steals it — hence `after_expansion` below.
            let body = &tcx.mir_promoted(local_def_id).0.borrow().clone();
            let arg_names = resolve_arg_names_or_warn(tcx, local_def_id.to_def_id(), None);
            let (_expr, effects) = extract_return_expr_with_context(
                tcx,
                body,
                &arg_names,
                &HashMap::new(),
                &HashMap::new(),
                &builtin_trust_wp_std_specs(),
            );
            self.assumptions = Some(effects.assumptions.iter().map(|a| format!("{a}")).collect());
            return Compilation::Stop;
        }
        Compilation::Stop
    }
}

fn assumptions_in_source(source: &str, fn_name: &str) -> Vec<String> {
    let unique = COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_closure_thunk_{}_{}",
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
        "trust_wp_closure_thunk_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];
    let mut callbacks = AssumptionCallbacks {
        fn_name: fn_name.to_string(),
        assumptions: None,
    };
    run_compiler(&args, &mut callbacks);
    let _ = fs::remove_dir_all(&temp_dir);
    callbacks.assumptions.expect("target function found")
}

#[test]
fn ok_or_else_thunk_value_reaches_the_contract() {
    let assumptions = assumptions_in_source(
        "pub fn f(n: Option<i32>) -> Result<i32, bool> { n.ok_or_else(|| true) }",
        "f",
    );
    let joined = assumptions.join("\n");
    assert!(
        !joined.contains("arg1")
            && !joined.contains("Err(__trust_wp_tuple0())")
            && !joined.contains("Err(())"),
        "thunk argument must not stay an opaque fallback: {joined}"
    );
    assert!(
        joined.contains("true"),
        "thunk value must appear in the Err branch: {joined}"
    );
}

#[test]
fn ok_or_else_thunk_with_non_closed_body_keeps_fallback() {
    // Capture-free and parameter-free, but the body's value is a call result
    // (a free name, not a closed term): it must NOT be substituted.
    let assumptions = assumptions_in_source(
        "fn g() -> bool { true }
         pub fn f(n: Option<i32>) -> Result<i32, bool> { n.ok_or_else(|| g()) }",
        "f",
    );
    let joined = assumptions.join("\n");
    // The body value `g()` is a call result, not a closed term: it must never
    // be substituted into the Err payload.
    assert!(
        !joined.contains("Err(call") && !joined.contains("Err(_call"),
        "non-closed thunk body must not be substituted: {joined}"
    );
}
