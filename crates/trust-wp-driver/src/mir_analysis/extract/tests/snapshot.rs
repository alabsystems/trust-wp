// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::mir::{Rvalue, StatementKind};
use trust_wp_core::formula::ExprSort;

use super::*;

static SNAPSHOT_TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

struct SnapshotCallAssumptionCallbacks {
    fn_name: String,
    assumptions: Option<Vec<PureExpr>>,
    ran: bool,
}

impl Callbacks for SnapshotCallAssumptionCallbacks {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let suffix = format!("::{}", self.fn_name);

        for local_def_id in tcx.hir_body_owners() {
            let def_path = tcx.def_path_str(local_def_id);
            if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                continue;
            }

            let body = tcx.optimized_mir(local_def_id.to_def_id());
            let arg_names = resolve_arg_names_or_warn(tcx, local_def_id.to_def_id(), None);
            let (_expr, effects) = extract_return_expr_with_context(
                tcx,
                body,
                &arg_names,
                &HashMap::new(),
                &HashMap::new(),
                &HashMap::new(),
            );
            self.assumptions = Some(effects.assumptions);
            self.ran = true;
            return Compilation::Stop;
        }

        Compilation::Stop
    }
}

fn extract_call_assumptions_in_cfg_trust_wp_source(source: &str, fn_name: &str) -> Vec<PureExpr> {
    let unique = SNAPSHOT_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_snapshot_extract_{}_{}",
        std::process::id(),
        unique,
    ));
    fs::create_dir_all(&temp_dir).expect("create test temp dir");

    let source_path = temp_dir.join("test.rs");
    fs::write(&source_path, source).expect("write test source");

    let args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        "trust_wp_snapshot_extract_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--cfg".to_string(),
        // Crate-name form for `--cfg` (Rust identifier, no hyphens).
        "trust_wp".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = SnapshotCallAssumptionCallbacks {
        fn_name: fn_name.to_string(),
        assumptions: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to extract call assumptions for `{fn_name}`"
    );
    callbacks
        .assumptions
        .expect("assumptions should be set when ran=true")
}

fn has_push_back_assumption(assumptions: &[PureExpr], value: i64) -> bool {
    assumptions.iter().any(|assumption| {
        matches!(
            assumption,
            PureExpr::BinOp(lhs, BinOp::Eq, rhs)
                if matches!(
                    lhs.as_ref(),
                    PureExpr::View(inner)
                        if matches!(inner.as_ref(), PureExpr::Final(_))
                ) && matches!(
                    rhs.as_ref(),
                    PureExpr::MethodCall { method, args, .. }
                        if method == "push_back"
                        && matches!(args.as_slice(), [PureExpr::Int(v)] if *v == value)
                )
        )
    })
}

struct SnapshotSubstitutionCallbacks {
    fn_name: String,
    substitutions: Option<NameSubstitutions>,
    ran: bool,
}

impl Callbacks for SnapshotSubstitutionCallbacks {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let suffix = format!("::{}", self.fn_name);

        for local_def_id in tcx.hir_body_owners() {
            let def_path = tcx.def_path_str(local_def_id);
            if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                continue;
            }

            let body = tcx.optimized_mir(local_def_id.to_def_id());
            let arg_names = resolve_arg_names_or_warn(tcx, local_def_id.to_def_id(), None);
            let location =
                body.basic_blocks
                    .iter_enumerated()
                    .find_map(|(bb_idx, bb_data)| {
                        bb_data.statements.iter().enumerate().find_map(
                            |(stmt_idx, stmt)| match stmt.kind {
                                StatementKind::Assign(box (
                                    _,
                                    Rvalue::Aggregate(
                                        box rustc_middle::mir::AggregateKind::Closure(_, _),
                                        _,
                                    ),
                                )) => Some(Location {
                                    block: bb_idx,
                                    statement_index: stmt_idx,
                                }),
                                _ => None,
                            },
                        )
                    })
                    .expect("closure marker should be present");
            self.substitutions = extract_name_substitutions_until_location(
                tcx,
                body,
                &arg_names,
                &HashMap::new(),
                &HashMap::new(),
                &HashMap::new(),
                location,
            );
            self.ran = true;
            return Compilation::Stop;
        }

        Compilation::Stop
    }
}

fn extract_substitutions_at_proof_assert_in_source(
    source: &str,
    fn_name: &str,
) -> NameSubstitutions {
    let unique = SNAPSHOT_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_snapshot_subst_{}_{}",
        std::process::id(),
        unique,
    ));
    fs::create_dir_all(&temp_dir).expect("create test temp dir");

    let source_path = temp_dir.join("test.rs");
    fs::write(&source_path, source).expect("write test source");

    let args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        "trust_wp_snapshot_extract_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = SnapshotSubstitutionCallbacks {
        fn_name: fn_name.to_string(),
        substitutions: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to extract substitutions for `{fn_name}`"
    );
    callbacks
        .substitutions
        .expect("substitutions should be set when ran=true")
}

#[test]
fn cfg_trust_wp_snapshot_block_preserves_call_assumptions() {
    let source = r#"
pub mod trust_wp_std {
    pub mod ghost {
        pub struct Snapshot<T>(::std::marker::PhantomData<T>);

        impl<T> Snapshot<T> {
            pub fn new_phantom() -> Self {
                Self(::std::marker::PhantomData)
            }
        }
    }
}

pub fn snapshot_block_preserves_push(mut v: Vec<i32>) -> Vec<i32> {
    let _snap: trust_wp_std::ghost::Snapshot<()> = {
        #[cfg(trust_wp)]
        {
            v.push(1);
        }
        trust_wp_std::ghost::Snapshot::new_phantom()
    };
    v
}
"#;

    let assumptions =
        extract_call_assumptions_in_cfg_trust_wp_source(source, "snapshot_block_preserves_push");

    assert!(
        has_push_back_assumption(&assumptions, 1),
        "cfg(trust_wp) snapshot block should preserve Vec::push assumptions, got: {assumptions:?}"
    );
}

/// Callbacks that build `user_specs` from a named "lemma" function, then
/// extract a target function with those specs active. Verifies that
/// postconditions from user-defined functions propagate as assumptions
/// through the MIR extraction pipeline.
struct SnapshotUserSpecCallbacks {
    /// Function to extract (must call the lemma inside a cfg(trust_wp) block).
    target_fn_name: String,
    /// Function whose DefId + spec will be placed in `user_specs`.
    lemma_fn_name: String,
    /// The StdSpec to assign to the lemma function.
    lemma_spec: StdSpec,
    /// Collected assumptions from extraction.
    assumptions: Option<Vec<PureExpr>>,
    ran: bool,
}

impl Callbacks for SnapshotUserSpecCallbacks {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let target_suffix = format!("::{}", self.target_fn_name);
        let lemma_suffix = format!("::{}", self.lemma_fn_name);

        // Step 1: Find the lemma function's DefId
        let mut lemma_def_id = None;
        let mut target_def_id = None;
        for local_def_id in tcx.hir_body_owners() {
            let def_path = tcx.def_path_str(local_def_id);
            if def_path == self.lemma_fn_name || def_path.ends_with(&lemma_suffix) {
                lemma_def_id = Some(local_def_id.to_def_id());
            }
            if def_path == self.target_fn_name || def_path.ends_with(&target_suffix) {
                target_def_id = Some(local_def_id);
            }
        }

        let Some(lemma_def_id) = lemma_def_id else {
            panic!("lemma function `{}` not found", self.lemma_fn_name);
        };
        let Some(target_def_id) = target_def_id else {
            panic!("target function `{}` not found", self.target_fn_name);
        };

        // Step 2: Build user_specs with the lemma's spec
        let mut user_specs = HashMap::new();
        user_specs.insert(lemma_def_id, self.lemma_spec.clone());

        // Step 3: Extract the target function with user_specs active
        let body = tcx.optimized_mir(target_def_id.to_def_id());
        let arg_names = resolve_arg_names_or_warn(tcx, target_def_id.to_def_id(), None);
        let (_expr, effects) = extract_return_expr_with_context(
            tcx,
            body,
            &arg_names,
            &user_specs,
            &HashMap::new(),
            &HashMap::new(),
        );
        self.assumptions = Some(effects.assumptions);
        self.ran = true;
        Compilation::Stop
    }
}

fn extract_user_spec_assumptions_in_cfg_trust_wp_source(
    source: &str,
    target_fn: &str,
    lemma_fn: &str,
    lemma_spec: StdSpec,
) -> Vec<PureExpr> {
    let unique = SNAPSHOT_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_snapshot_user_spec_{}_{}",
        std::process::id(),
        unique,
    ));
    fs::create_dir_all(&temp_dir).expect("create test temp dir");

    let source_path = temp_dir.join("test.rs");
    fs::write(&source_path, source).expect("write test source");

    let args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        "trust_wp_snapshot_user_spec_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--cfg".to_string(),
        // Crate-name form for `--cfg` (Rust identifier, no hyphens).
        "trust_wp".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = SnapshotUserSpecCallbacks {
        target_fn_name: target_fn.to_string(),
        lemma_fn_name: lemma_fn.to_string(),
        lemma_spec,
        assumptions: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to extract user-spec assumptions for `{target_fn}`"
    );
    callbacks
        .assumptions
        .expect("assumptions should be set when ran=true")
}

/// Verify that user-defined lemma postconditions propagate as assumptions
/// when the lemma is called inside a `cfg(trust_wp)` snapshot block.
///
/// This is the core test for #2299: snapshot! blocks must preserve lemma
/// postconditions through MIR extraction when user_specs are provided.
#[test]
fn cfg_trust_wp_snapshot_block_preserves_user_spec_lemma_postconditions() {
    let source = r#"
pub mod trust_wp_std {
    pub mod ghost {
        pub struct Snapshot<T>(::std::marker::PhantomData<T>);

        impl<T> Snapshot<T> {
            pub fn new_phantom() -> Self {
                Self(::std::marker::PhantomData)
            }
        }
    }
}

pub fn my_lemma(_x: i32) {
    // Body is irrelevant — the spec comes from user_specs
}

pub fn caller_with_snapshot(x: i32) -> i32 {
    let _snap: trust_wp_std::ghost::Snapshot<()> = {
        #[cfg(trust_wp)]
        {
            my_lemma(x);
        }
        trust_wp_std::ghost::Snapshot::new_phantom()
    };
    x
}
"#;

    let lemma_spec = StdSpec {
        requires: Vec::new(),
        ensures: vec!["x >= 0".to_string()],
        param_names: Some(vec!["x".to_string()]),
    };

    let assumptions = extract_user_spec_assumptions_in_cfg_trust_wp_source(
        source,
        "caller_with_snapshot",
        "my_lemma",
        lemma_spec,
    );

    // The lemma postcondition `x >= 0` is parsed and substituted with the
    // actual argument. Since the caller passes its own `x`, the result is
    // BinOp(Var("x", Some(Int)), Ge, Int(0)). Keep the exact sort in the
    // expectation: accepting an untyped variable here would hide a sort-loss
    // regression in the snapshot lane.
    let expected = PureExpr::BinOp(
        std::sync::Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Int))),
        BinOp::Ge,
        std::sync::Arc::new(PureExpr::Int(0)),
    );
    assert!(
        assumptions.contains(&expected),
        "cfg(trust_wp) snapshot block should preserve user-spec lemma postcondition \
         `x >= 0` as assumption, got: {assumptions:?}"
    );
}

/// Verify that when a lemma call appears as the argument to `Snapshot::capture`,
/// the lemma's postconditions are preserved as assumptions. This covers the
/// expression-style `snapshot!(lemma(x))` expansion which becomes
/// `Snapshot::capture(&(lemma(x)))`.
///
/// Regression test for #2299: expression-style snapshot! lemma postconditions.
#[test]
fn snapshot_capture_expression_lemma_preserves_postconditions() {
    let source = r#"
pub mod trust_wp_std {
    pub mod ghost {
        pub struct Snapshot<T>(::std::marker::PhantomData<T>);

        impl<T> Snapshot<T> {
            pub fn capture(_value: &T) -> Self {
                Self(::std::marker::PhantomData)
            }
        }
    }
}

pub fn my_lemma(_x: i32) -> i32 {
    0
}

pub fn caller_snapshot_capture(x: i32) -> i32 {
    let _snap = trust_wp_std::ghost::Snapshot::capture(&my_lemma(x));
    x
}
"#;

    let lemma_spec = StdSpec {
        requires: Vec::new(),
        ensures: vec!["x >= 0".to_string()],
        param_names: Some(vec!["x".to_string()]),
    };

    let assumptions = extract_user_spec_assumptions_in_cfg_trust_wp_source(
        source,
        "caller_snapshot_capture",
        "my_lemma",
        lemma_spec,
    );

    // The lemma postcondition `x >= 0` should propagate as an assumption
    // even when called as an argument to Snapshot::capture.
    let expected = PureExpr::BinOp(
        std::sync::Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Int))),
        BinOp::Ge,
        std::sync::Arc::new(PureExpr::Int(0)),
    );
    assert!(
        assumptions.contains(&expected),
        "Snapshot::capture expression-style lemma call should preserve postcondition \
         `x >= 0` as assumption, got: {assumptions:?}"
    );
}

/// Verify that extern_specs-resolved lemma postconditions propagate through
/// snapshot blocks. When a lemma function is resolved via extern_specs (path-based
/// lookup) rather than user_specs (DefId-based lookup), the postconditions
/// should still be injected as assumptions.
///
/// This uses a custom callback that discovers the actual `def_path_str` for the
/// lemma at runtime and registers it in `extern_specs`. For local crate items,
/// `def_path_str` omits the crate prefix (e.g., `my_extern_lemma` not
/// `crate_name::my_extern_lemma`), matching how `resolve_call` performs lookups.
///
/// Regression test for #2299: extern_spec path for snapshot lemma calls.
#[test]
fn cfg_trust_wp_snapshot_block_extern_spec_lemma_preserves_postconditions() {
    struct SnapshotExternSpecCallbacks {
        target_fn_name: String,
        /// Short name to match against the end of `def_path_str` output.
        lemma_short_name: String,
        lemma_spec: StdSpec,
        assumptions: Option<Vec<PureExpr>>,
        ran: bool,
    }

    impl Callbacks for SnapshotExternSpecCallbacks {
        #[allow(clippy::elidable_lifetime_names)]
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            let target_suffix = format!("::{}", self.target_fn_name);

            let mut target_def_id = None;
            let mut lemma_path = None;
            for local_def_id in tcx.hir_body_owners() {
                let def_path = tcx.def_path_str(local_def_id);
                if def_path == self.target_fn_name || def_path.ends_with(&target_suffix) {
                    target_def_id = Some(local_def_id);
                }
                // Discover the actual extern_spec path by matching the short name
                if def_path == self.lemma_short_name
                    || def_path.ends_with(&format!("::{}", self.lemma_short_name))
                {
                    lemma_path = Some(def_path);
                }
            }

            let Some(target_def_id) = target_def_id else {
                panic!("target function `{}` not found", self.target_fn_name);
            };
            let Some(lemma_path) = lemma_path else {
                panic!("lemma function `{}` not found", self.lemma_short_name);
            };

            // Register the lemma via extern_specs using the actual def_path_str
            let mut extern_specs = HashMap::new();
            extern_specs.insert(lemma_path, self.lemma_spec.clone());

            let body = tcx.optimized_mir(target_def_id.to_def_id());
            let arg_names = resolve_arg_names_or_warn(tcx, target_def_id.to_def_id(), None);
            let (_expr, effects) = extract_return_expr_with_context(
                tcx,
                body,
                &arg_names,
                &HashMap::new(), // no user_specs
                &HashMap::new(), // no trait_specs
                &extern_specs,
            );
            self.assumptions = Some(effects.assumptions);
            self.ran = true;
            Compilation::Stop
        }
    }

    let source = r#"
pub mod trust_wp_std {
    pub mod ghost {
        pub struct Snapshot<T>(::std::marker::PhantomData<T>);

        impl<T> Snapshot<T> {
            pub fn new_phantom() -> Self {
                Self(::std::marker::PhantomData)
            }
        }
    }
}

pub fn my_extern_lemma(_x: i32) {
    // Body is irrelevant — the spec comes from extern_specs
}

pub fn caller_with_extern_spec_lemma(x: i32) -> i32 {
    let _snap: trust_wp_std::ghost::Snapshot<()> = {
        #[cfg(trust_wp)]
        {
            my_extern_lemma(x);
        }
        trust_wp_std::ghost::Snapshot::new_phantom()
    };
    x
}
"#;

    let unique = SNAPSHOT_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_snapshot_extern_spec_{}_{}",
        std::process::id(),
        unique,
    ));
    fs::create_dir_all(&temp_dir).expect("create test temp dir");
    let source_path = temp_dir.join("test.rs");
    fs::write(&source_path, source).expect("write test source");

    let args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        "trust_wp_snapshot_extern_spec_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--cfg".to_string(),
        // Crate-name form for `--cfg` (Rust identifier, no hyphens).
        "trust_wp".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let lemma_spec = StdSpec {
        requires: Vec::new(),
        ensures: vec!["x >= 0".to_string()],
        param_names: Some(vec!["x".to_string()]),
    };

    let mut callbacks = SnapshotExternSpecCallbacks {
        target_fn_name: "caller_with_extern_spec_lemma".to_string(),
        lemma_short_name: "my_extern_lemma".to_string(),
        lemma_spec,
        assumptions: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to extract extern-spec assumptions for `caller_with_extern_spec_lemma`"
    );
    let assumptions = callbacks
        .assumptions
        .expect("assumptions should be set when ran=true");

    let expected = PureExpr::BinOp(
        std::sync::Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Int))),
        BinOp::Ge,
        std::sync::Arc::new(PureExpr::Int(0)),
    );
    assert!(
        assumptions.contains(&expected),
        "extern_spec-resolved lemma postcondition `x >= 0` should propagate as assumption \
         through cfg(trust_wp) snapshot block, got: {assumptions:?}"
    );
}

/// Verify that multiple lemma calls inside a single snapshot block all
/// have their postconditions preserved as assumptions.
///
/// Regression test for #2299: multi-lemma snapshot blocks.
#[test]
fn cfg_trust_wp_snapshot_block_multiple_lemma_calls_preserve_all_postconditions() {
    let source = r#"
pub mod trust_wp_std {
    pub mod ghost {
        pub struct Snapshot<T>(::std::marker::PhantomData<T>);

        impl<T> Snapshot<T> {
            pub fn new_phantom() -> Self {
                Self(::std::marker::PhantomData)
            }
        }
    }
}

pub fn lemma_a(_x: i32) {}
pub fn lemma_b(_y: i32) {}

pub fn caller_with_multiple_lemmas(x: i32, y: i32) -> i32 {
    let _snap: trust_wp_std::ghost::Snapshot<()> = {
        #[cfg(trust_wp)]
        {
            lemma_a(x);
            lemma_b(y);
        }
        trust_wp_std::ghost::Snapshot::new_phantom()
    };
    x + y
}
"#;

    // We need a custom callback that registers TWO lemma specs
    struct MultiLemmaCallbacks {
        target_fn_name: String,
        lemma_specs: Vec<(String, StdSpec)>,
        assumptions: Option<Vec<PureExpr>>,
        ran: bool,
    }

    impl Callbacks for MultiLemmaCallbacks {
        #[allow(clippy::elidable_lifetime_names)]
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            let target_suffix = format!("::{}", self.target_fn_name);

            let mut user_specs = HashMap::new();
            let mut target_def_id = None;
            for local_def_id in tcx.hir_body_owners() {
                let def_path = tcx.def_path_str(local_def_id);
                if def_path == self.target_fn_name || def_path.ends_with(&target_suffix) {
                    target_def_id = Some(local_def_id);
                }
                for (lemma_name, spec) in &self.lemma_specs {
                    let lemma_suffix = format!("::{lemma_name}");
                    if def_path == *lemma_name || def_path.ends_with(&lemma_suffix) {
                        user_specs.insert(local_def_id.to_def_id(), spec.clone());
                    }
                }
            }

            let Some(target_def_id) = target_def_id else {
                panic!("target function `{}` not found", self.target_fn_name);
            };

            let body = tcx.optimized_mir(target_def_id.to_def_id());
            let arg_names = resolve_arg_names_or_warn(tcx, target_def_id.to_def_id(), None);
            let (_expr, effects) = extract_return_expr_with_context(
                tcx,
                body,
                &arg_names,
                &user_specs,
                &HashMap::new(),
                &HashMap::new(),
            );
            self.assumptions = Some(effects.assumptions);
            self.ran = true;
            Compilation::Stop
        }
    }

    let unique = SNAPSHOT_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_snapshot_multi_lemma_{}_{}",
        std::process::id(),
        unique,
    ));
    fs::create_dir_all(&temp_dir).expect("create test temp dir");
    let source_path = temp_dir.join("test.rs");
    fs::write(&source_path, source).expect("write test source");

    let args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        "trust_wp_snapshot_multi_lemma_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--cfg".to_string(),
        // Crate-name form for `--cfg` (Rust identifier, no hyphens).
        "trust_wp".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = MultiLemmaCallbacks {
        target_fn_name: "caller_with_multiple_lemmas".to_string(),
        lemma_specs: vec![
            (
                "lemma_a".to_string(),
                StdSpec {
                    requires: Vec::new(),
                    ensures: vec!["x >= 0".to_string()],
                    param_names: Some(vec!["x".to_string()]),
                },
            ),
            (
                "lemma_b".to_string(),
                StdSpec {
                    requires: Vec::new(),
                    ensures: vec!["y < 100".to_string()],
                    param_names: Some(vec!["y".to_string()]),
                },
            ),
        ],
        assumptions: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to extract multi-lemma assumptions for `caller_with_multiple_lemmas`"
    );
    let assumptions = callbacks
        .assumptions
        .expect("assumptions should be set when ran=true");

    let expected_a = PureExpr::BinOp(
        std::sync::Arc::new(PureExpr::Var("x".to_string(), Some(ExprSort::Int))),
        BinOp::Ge,
        std::sync::Arc::new(PureExpr::Int(0)),
    );
    let expected_b = PureExpr::BinOp(
        std::sync::Arc::new(PureExpr::Var("y".to_string(), Some(ExprSort::Int))),
        BinOp::Lt,
        std::sync::Arc::new(PureExpr::Int(100)),
    );

    assert!(
        assumptions.contains(&expected_a),
        "first lemma postcondition `x >= 0` should propagate as assumption, got: {assumptions:?}"
    );
    assert!(
        assumptions.contains(&expected_b),
        "second lemma postcondition `y < 100` should propagate as assumption, got: {assumptions:?}"
    );
}

#[test]
fn proof_assert_snapshot_after_loop_symbolizes_cycle_recovery_state() {
    let source = r#"
pub fn loop_then_proof_assert(flag: bool) {
    let mut x = 0;
    while flag {
        x += 1;
    }
    let proof = || -> bool {
        let _ = (&x,);
        true
    };
    let _ = proof();
}
"#;

    let substitutions =
        extract_substitutions_at_proof_assert_in_source(source, "loop_then_proof_assert");
    assert_eq!(
        substitutions.get("x"),
        Some(&PureExpr::Var("x".to_string(), Some(ExprSort::Int))),
        "post-loop substitution should not preserve the pre-loop concrete value: {substitutions:?}",
    );
}

#[test]
fn proof_assert_snapshot_after_for_loop_symbolizes_cycle_recovery_state() {
    let source = r#"
pub fn for_loop_then_proof_assert() {
    let mut sum = 0;
    for x in 0..3 {
        sum += x;
    }
    let proof = || -> bool {
        let _ = (&sum,);
        true
    };
    let _ = proof();
}
"#;

    let substitutions =
        extract_substitutions_at_proof_assert_in_source(source, "for_loop_then_proof_assert");
    assert_eq!(
        substitutions.get("sum"),
        Some(&PureExpr::Var("sum".to_string(), Some(ExprSort::Int))),
        "post-for-loop substitution should not preserve the pre-loop concrete value: {substitutions:?}",
    );
}
