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
use rustc_hir::def::DefKind;
use rustc_interface::{interface::Compiler, Config};
use rustc_middle::ty::{TyCtxt, CAPTURE_STRUCT_LOCAL};
use trust_wp_core::formula::{BorrowIdOrigin, BorrowIdStep, ExprSort};
use trust_wp_driver::StdSpec;

use super::{super::translate::allows_field0_identity_fallback, *};
use crate::callbacks::{copy_mir_bodies, thread_locals::clear_caches, try_get_body_with_context};

static TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

#[allow(clippy::option_option)] // Outer Option = "callback ran?", inner = extraction result
struct MutBorrowCallbacks {
    fn_name: String,
    arg_names: Vec<String>,
    result: Option<Option<MutBorrowBody>>,
    ran: bool,
}

impl Callbacks for MutBorrowCallbacks {
    fn config(&mut self, config: &mut Config) {
        install_mir_borrowck_cache(config);
    }

    #[allow(clippy::elidable_lifetime_names)] // Matches rustc_driver::Callbacks trait signature
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let suffix = format!("::{}", self.fn_name);
        for owner in tcx.hir_body_owners() {
            let def_id = owner.to_def_id();
            let path = tcx.def_path_str(def_id);
            if path != self.fn_name && !path.ends_with(&suffix) {
                continue;
            }
            let root = tcx.typeck_root_def_id(def_id).expect_local();
            let _ = tcx.mir_borrowck(root);
            let body_with_facts = try_get_body_with_context(owner)
                .expect("borrowck-backed MIR body should be cached");
            let body = super::super::get_mir_body(body_with_facts);
            self.result = Some(extract_mut_borrow_body(
                tcx,
                body,
                Some(body_with_facts),
                &self.arg_names,
                &HashMap::new(),
                &HashMap::new(),
                &HashMap::new(),
            ));
            self.ran = true;
            break;
        }
        Compilation::Stop
    }
}

fn extract_from_source(source: &str, fn_name: &str, arg_names: &[&str]) -> MutBorrowBody {
    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_mut_borrow_reborrow_{}_{}",
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
        "trust_wp_mut_borrow_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = MutBorrowCallbacks {
        fn_name: fn_name.to_string(),
        arg_names: arg_names.iter().map(|name| (*name).to_string()).collect(),
        result: None,
        ran: false,
    };
    clear_caches();
    run_compiler(&args, &mut callbacks);
    clear_caches();

    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to locate function `{fn_name}` in rustc callback"
    );

    callbacks
        .result
        .expect("callback should capture extraction result")
        .expect("mut borrow extraction should succeed")
}

fn extract_from_first_closure_source(source: &str) -> MutBorrowBody {
    #[allow(clippy::option_option)] // Outer Option = "callback ran?", inner = extraction result
    struct ClosureCallbacks {
        result: Option<Option<MutBorrowBody>>,
        ran: bool,
    }

    impl Callbacks for ClosureCallbacks {
        fn config(&mut self, config: &mut Config) {
            install_mir_borrowck_cache(config);
        }

        #[allow(clippy::elidable_lifetime_names)] // Matches rustc_driver::Callbacks trait signature
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            for owner in tcx.hir_body_owners() {
                let def_id = owner.to_def_id();
                if tcx.def_kind(def_id) != DefKind::Closure {
                    continue;
                }

                let root = tcx.typeck_root_def_id(def_id).expect_local();
                let _ = tcx.mir_borrowck(root);
                let body_with_facts =
                    try_get_body_with_context(owner).expect("closure MIR body should be cached");
                let body = super::super::get_mir_body(body_with_facts);
                let arg_names = vec!["self".to_string()];
                self.result = Some(extract_mut_borrow_body(
                    tcx,
                    body,
                    Some(body_with_facts),
                    &arg_names,
                    &HashMap::new(),
                    &HashMap::new(),
                    &HashMap::new(),
                ));
                self.ran = true;
                break;
            }
            Compilation::Stop
        }
    }

    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_mut_borrow_closure_extract_{}_{}",
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
        "trust_wp_mut_borrow_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = ClosureCallbacks {
        result: None,
        ran: false,
    };
    clear_caches();
    run_compiler(&args, &mut callbacks);
    clear_caches();

    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to locate closure body in rustc callback"
    );

    callbacks
        .result
        .expect("callback should capture closure extraction result")
        .expect("closure mut borrow extraction should succeed")
}

/// Like `extract_from_first_closure_source`, but returns `None` when extraction
/// bails (e.g., due to complex control flow or unsupported call patterns),
/// instead of panicking.
fn try_extract_from_first_closure_source(source: &str) -> Option<MutBorrowBody> {
    #[allow(clippy::option_option)]
    struct ClosureCallbacks {
        result: Option<Option<MutBorrowBody>>,
        ran: bool,
    }

    impl Callbacks for ClosureCallbacks {
        fn config(&mut self, config: &mut Config) {
            install_mir_borrowck_cache(config);
        }

        #[allow(clippy::elidable_lifetime_names)]
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            for owner in tcx.hir_body_owners() {
                let def_id = owner.to_def_id();
                if tcx.def_kind(def_id) != DefKind::Closure {
                    continue;
                }
                let root = tcx.typeck_root_def_id(def_id).expect_local();
                let _ = tcx.mir_borrowck(root);
                let body_with_facts =
                    try_get_body_with_context(owner).expect("closure MIR body should be cached");
                let body = super::super::get_mir_body(body_with_facts);
                let arg_names = vec!["self".to_string()];
                self.result = Some(extract_mut_borrow_body(
                    tcx,
                    body,
                    Some(body_with_facts),
                    &arg_names,
                    &HashMap::new(),
                    &HashMap::new(),
                    &HashMap::new(),
                ));
                self.ran = true;
                break;
            }
            Compilation::Stop
        }
    }

    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_mut_borrow_try_closure_{}_{}",
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
        "trust_wp_mut_borrow_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = ClosureCallbacks {
        result: None,
        ran: false,
    };
    clear_caches();
    run_compiler(&args, &mut callbacks);
    clear_caches();

    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to locate closure body in rustc callback"
    );

    callbacks.result.expect("callback should capture result")
}

/// Dump MIR basic blocks for the first closure in the source. Returns a
/// formatted string with statements and terminators per block for debugging.
#[allow(dead_code)]
fn dump_closure_mir(source: &str) -> String {
    struct MirDumpCallbacks {
        output: String,
        ran: bool,
    }

    impl Callbacks for MirDumpCallbacks {
        fn config(&mut self, config: &mut Config) {
            install_mir_borrowck_cache(config);
        }

        #[allow(clippy::elidable_lifetime_names)]
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            for owner in tcx.hir_body_owners() {
                let def_id = owner.to_def_id();
                if tcx.def_kind(def_id) != DefKind::Closure {
                    continue;
                }
                let root = tcx.typeck_root_def_id(def_id).expect_local();
                let _ = tcx.mir_borrowck(root);
                let body_with_facts =
                    try_get_body_with_context(owner).expect("closure MIR body should be cached");
                let body = super::super::get_mir_body(body_with_facts);
                self.output.push_str(&format!("=== Closure MIR ===\n"));
                self.output.push_str(&format!("Local declarations:\n"));
                for (idx, decl) in body.local_decls.iter_enumerated() {
                    self.output
                        .push_str(&format!("  _{}: {:?}\n", idx.as_u32(), decl.ty));
                }
                self.output.push_str("\n");
                for (bb_idx, bb) in body.basic_blocks.iter_enumerated() {
                    self.output.push_str(&format!("bb{}:\n", bb_idx.as_u32()));
                    for (stmt_idx, stmt) in bb.statements.iter().enumerate() {
                        self.output
                            .push_str(&format!("  s{}: {:?}\n", stmt_idx, stmt.kind));
                    }
                    self.output
                        .push_str(&format!("  term: {:?}\n\n", bb.terminator().kind));
                }
                self.ran = true;
                break;
            }
            Compilation::Stop
        }
    }

    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_mir_dump_{}_{}",
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
        "trust_wp_mut_borrow_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = MirDumpCallbacks {
        output: String::new(),
        ran: false,
    };
    clear_caches();
    run_compiler(&args, &mut callbacks);
    clear_caches();

    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(callbacks.ran, "failed to locate closure body");
    callbacks.output
}

fn assert_deref_var(expr: &PureExpr, var_name: &str) {
    match expr {
        PureExpr::Deref(inner) => match inner.as_ref() {
            PureExpr::Var(name, _sort) => {
                assert_eq!(
                    name, var_name,
                    "expected deref of `{var_name}`, got deref of `{name}`"
                );
            }
            other => panic!("expected Deref(Var(\"{var_name}\", _)), got Deref({other:?})"),
        },
        other => {
            panic!("expected expression to remain identity deref for `{var_name}`, got {other:?}")
        }
    }
}

fn assert_deref_plus_int(expr: &PureExpr, var_name: &str, delta: i64) {
    match expr {
        PureExpr::BinOp(lhs, trust_wp_core::formula::BinOp::Add, rhs) => {
            match lhs.as_ref() {
                PureExpr::Deref(inner) => match inner.as_ref() {
                    PureExpr::Var(name, _sort) => {
                        assert_eq!(name, var_name);
                    }
                    other => {
                        panic!("expected Deref(Var(\"{var_name}\", _)), got Deref({other:?})")
                    }
                },
                other => panic!("expected Deref(Var(\"{var_name}\", _)), got {other:?}"),
            }
            assert_eq!(rhs.as_ref(), &PureExpr::Int(delta));
        }
        other => panic!("expected `{var_name}` to update by +{delta}, got {other:?}"),
    }
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

fn expr_is_delayed_writeback(expr: &PureExpr, parent_name: &str, child_name: &str) -> bool {
    match expr {
        PureExpr::BinOp(lhs, trust_wp_core::formula::BinOp::Eq, rhs) => {
            matches!(
                lhs.as_ref(),
                PureExpr::Deref(inner)
                    if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == parent_name)
            ) && matches!(
                rhs.as_ref(),
                PureExpr::Final(inner)
                    if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == child_name)
            )
        }
        _ => false,
    }
}

fn expr_is_final_writeback(expr: &PureExpr, parent_name: &str, child_name: &str) -> bool {
    match expr {
        PureExpr::BinOp(lhs, trust_wp_core::formula::BinOp::Eq, rhs) => {
            matches!(
                lhs.as_ref(),
                PureExpr::Final(inner)
                    if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == parent_name)
            ) && matches!(
                rhs.as_ref(),
                PureExpr::Final(inner)
                    if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == child_name)
            )
        }
        _ => false,
    }
}

#[allow(clippy::ref_option)] // matches PureExpr::Var sort field type
fn expr_contains_var_with_sort(
    expr: &PureExpr,
    var_name: &str,
    expected_sort: &Option<trust_wp_core::formula::ExprSort>,
) -> bool {
    match expr {
        PureExpr::Var(name, sort) => name == var_name && sort == expected_sort,
        PureExpr::BinOp(lhs, _, rhs) => {
            expr_contains_var_with_sort(lhs, var_name, expected_sort)
                || expr_contains_var_with_sort(rhs, var_name, expected_sort)
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => expr_contains_var_with_sort(inner, var_name, expected_sort),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            expr_contains_var_with_sort(cond, var_name, expected_sort)
                || expr_contains_var_with_sort(then_expr, var_name, expected_sort)
                || expr_contains_var_with_sort(else_expr, var_name, expected_sort)
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            expr_contains_var_with_sort(receiver, var_name, expected_sort)
                || args
                    .iter()
                    .any(|arg| expr_contains_var_with_sort(arg, var_name, expected_sort))
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            expr_contains_var_with_sort(body, var_name, expected_sort)
                || triggers
                    .iter()
                    .flatten()
                    .any(|trigger| expr_contains_var_with_sort(trigger, var_name, expected_sort))
        }
        PureExpr::Match { scrutinee, arms } => {
            expr_contains_var_with_sort(scrutinee, var_name, expected_sort)
                || arms
                    .iter()
                    .any(|arm| expr_contains_var_with_sort(&arm.body, var_name, expected_sort))
        }
        PureExpr::LogicFnCall { args, .. } => args
            .iter()
            .any(|arg| expr_contains_var_with_sort(arg, var_name, expected_sort)),
        PureExpr::Let { value, body, .. } => {
            expr_contains_var_with_sort(value, var_name, expected_sort)
                || expr_contains_var_with_sort(body, var_name, expected_sort)
        }
        PureExpr::LetAssume { assumption, body }
        | PureExpr::LetObligation {
            obligation: assumption,
            body,
        } => {
            expr_contains_var_with_sort(assumption, var_name, expected_sort)
                || expr_contains_var_with_sort(body, var_name, expected_sort)
        }
        PureExpr::Closure { body, .. } => {
            expr_contains_var_with_sort(body, var_name, expected_sort)
        }
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) => false,
        _ => false,
    }
}

fn child_name_for_parent(extracted: &MutBorrowBody, parent_name: &str) -> String {
    extracted
        .resolve_results
        .as_ref()
        .expect("reborrow extraction should record resolve metadata")
        .writebacks
        .iter()
        .find(|writeback| writeback.parent_name == parent_name)
        .map(|writeback| writeback.child_name.clone())
        .expect("expected writeback for parent")
}

#[test]
fn test_field0_identity_fallback_allows_scalar() {
    assert!(allows_field0_identity_fallback(&PureExpr::Int(7)));
}

#[test]
fn test_field0_identity_fallback_rejects_logic_fn_call() {
    let struct_like = PureExpr::LogicFnCall {
        name: "MyStruct::new".to_string(),
        args: vec![PureExpr::Int(1), PureExpr::Bool(true)],
    };
    assert!(!allows_field0_identity_fallback(&struct_like));
}

#[test]
fn test_field0_identity_fallback_allows_binop_checked_op_shape() {
    let checked_op_shape = PureExpr::BinOp(
        Arc::new(PureExpr::Var("x".to_string(), None)),
        trust_wp_core::formula::BinOp::Add,
        Arc::new(PureExpr::Int(1)),
    );
    assert!(allows_field0_identity_fallback(&checked_op_shape));
}

#[test]
fn test_field0_identity_fallback_rejects_opaque_var_base() {
    let opaque = PureExpr::Var("opaque_value".to_string(), None);
    assert!(!allows_field0_identity_fallback(&opaque));
}

#[test]
fn test_strip_generics_basic() {
    assert_eq!(
        strip_generics("trust_wp_std::ghost::Snapshot::<i32>::capture"),
        "trust_wp_std::ghost::Snapshot::capture"
    );
}

#[test]
fn test_strip_generics_no_generics() {
    assert_eq!(strip_generics("std::mem::drop"), "std::mem::drop");
}

#[test]
fn test_strip_generics_nested() {
    assert_eq!(strip_generics("Foo::<Bar::<Baz>>::method"), "Foo::method");
}

#[test]
fn test_strip_generics_snapshot_reexport() {
    let path = "trust_wp_std::Snapshot::<bool>::capture";
    let stripped = strip_generics(path);
    assert!(
        stripped.ends_with("::Snapshot::capture"),
        "stripped path should match: {stripped}"
    );
}

#[test]
fn test_extract_mut_borrow_reborrow_targets_second_param() {
    let source = r#"
pub fn bump_second(a: &mut i32, b: &mut i32) {
let r = &mut *b;
*r = *r + 1;
let _ = a;
}
"#;

    let extracted = extract_from_source(source, "bump_second", &["a", "b"]);
    let a_final = extracted
        .final_values
        .get("a")
        .expect("expected final value for first &mut param");
    let b_final = extracted
        .final_values
        .get("b")
        .expect("expected final value for second &mut param");
    assert_deref_var(a_final, "a");
    assert_deref_plus_int(b_final, "b", 1);

    let resolve_results = extracted
        .resolve_results
        .as_ref()
        .expect("reborrow extraction should record resolve metadata");
    let writeback = resolve_results
        .writebacks
        .iter()
        .find(|writeback| writeback.parent_name == "b")
        .expect("simple reborrow should use an immediate writeback");
    assert!(
        writeback.activation.is_none(),
        "ordinary reborrows should stay on the immediate writeback path: {writeback:?}"
    );
    assert!(
        extracted.delayed_writeback_assumptions.is_empty(),
        "ordinary reborrows should not synthesize delayed assumptions"
    );
}

#[test]
fn test_extract_mut_borrow_transitive_reborrow_targets_second_param() {
    let source = r#"
pub fn bump_second_transitive(a: &mut i32, b: &mut i32) {
let r1 = &mut *b;
let r2 = &mut *r1;
*r2 = *r2 + 2;
let _ = a;
}
"#;

    let extracted = extract_from_source(source, "bump_second_transitive", &["a", "b"]);
    let a_final = extracted
        .final_values
        .get("a")
        .expect("expected final value for first &mut param");
    let b_final = extracted
        .final_values
        .get("b")
        .expect("expected final value for second &mut param");
    assert_deref_var(a_final, "a");
    assert_deref_plus_int(b_final, "b", 2);
}

#[test]
fn test_direct_final_reborrow_records_same_parent_borrow_id_origin() {
    let source = r#"
pub fn final_reborrow(x: &mut i32) {
let y = &mut *x;
*y = *y + 1;
}
"#;

    let extracted = extract_from_source(source, "final_reborrow", &["x"]);
    let child_name = child_name_for_parent(&extracted, "x");

    assert!(
        extracted
            .finality
            .get(&child_name)
            .is_some_and(|value| matches!(
                value,
                trust_wp_core::formula::BorrowFinality::Final { .. }
            )),
        "simple same-place reborrow should be final: {:?}",
        extracted.finality
    );
    assert_eq!(
        extracted.borrow_id_origins.get(&child_name),
        Some(&BorrowIdOrigin::SameParent {
            parent: "x".to_string()
        }),
        "final same-place reborrow should reuse the parent's borrow id"
    );
}

#[test]
fn test_reborrowed_parent_again_records_fresh_borrow_id_origin() {
    let source = r#"
pub fn fresh_reborrow(x: &mut i32) {
let y = &mut *x;
*y = *y + 1;
let z = &mut *x;
*z = *z + 1;
}
"#;

    let extracted = extract_from_source(source, "fresh_reborrow", &["x"]);
    let child_name = child_name_for_parent(&extracted, "x");

    assert_eq!(
        extracted.finality.get(&child_name),
        Some(&trust_wp_core::formula::BorrowFinality::Fresh),
        "reborrowing the parent again after the child should force Fresh finality"
    );
    assert_eq!(
        extracted.borrow_id_origins.get(&child_name),
        Some(&BorrowIdOrigin::Fresh {
            parent: "x".to_string()
        }),
        "non-final reborrow should get a fresh borrow id"
    );
}

#[test]
fn test_field_reborrow_records_derived_borrow_id_origin() {
    let source = r#"
pub fn bump_field(x: &mut (i32, i32)) {
let y = &mut (*x).1;
*y = *y + 1;
}
"#;

    let extracted = extract_from_source(source, "bump_field", &["x"]);
    let child_name = child_name_for_parent(&extracted, "x");

    assert_eq!(
        extracted.borrow_id_origins.get(&child_name),
        Some(&BorrowIdOrigin::Derived {
            parent: "x".to_string(),
            steps: vec![BorrowIdStep::Field(1)],
        }),
        "field reborrow should derive its borrow id from the parent field projection"
    );
}

#[test]
fn test_index_reborrow_records_index_borrow_id_origin() {
    let source = r#"
pub fn bump_index(x: &mut [i32], i: usize) {
let y = &mut (*x)[i];
*y = *y + 1;
}
"#;

    let extracted = extract_from_source(source, "bump_index", &["x", "i"]);
    let child_name = child_name_for_parent(&extracted, "x");

    match extracted
        .borrow_id_origins
        .get(&child_name)
        .expect("index reborrow should record a borrow-id origin")
    {
        BorrowIdOrigin::Derived { parent, steps } => {
            assert_eq!(parent, "x");
            assert_eq!(
                steps.len(),
                1,
                "index reborrow should record one projection step"
            );
            assert!(
                matches!(
                    steps.as_slice(),
                    [BorrowIdStep::Index(PureExpr::Var(name, Some(ExprSort::Int)))] if name == "i"
                ),
                "index reborrow should carry the translated index expression, got {steps:?}"
            );
        }
        other => panic!("expected derived borrow-id origin for index reborrow, got {other:?}"),
    }
}

/// Spec-driven state advancement: Vec::push (#2124).
///
/// When `extract_mut_borrow_body` encounters `v.push(42)` and Vec::push has
/// a known spec (`ensures: (^self)@ == self@.push_back(value)`), the extractor
/// should advance the receiver's symbolic state instead of bailing. The
/// extraction should succeed (return `Some`) with a final value for `v` that
/// reflects the post-push state.
#[test]
fn test_spec_advancement_vec_push_succeeds() {
    let source = r#"
pub fn push_one(v: &mut Vec<i32>) {
v.push(42);
}
"#;
    // With spec-driven advancement, extraction should succeed for a single
    // Vec::push call. Before #2124, this would bail with `None` at the
    // call_may_mutate_params check.
    let extracted = extract_from_source(source, "push_one", &["v"]);

    // The final value for `v` should exist and NOT be identity (Deref(Var("v")))
    // — it should reflect the spec-advanced state.
    let v_final = extracted
        .final_values
        .get("v")
        .expect("spec advancement should produce final value for v");

    // The final value should be the spec-derived expression, not identity deref.
    assert!(
        !matches!(v_final, PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(n, _) if n == "v")),
        "v's final value should NOT be identity deref (Deref(Var(\"v\"))) after push; got {v_final:?}"
    );
}

/// Chained spec advancement: two consecutive Vec::push calls (#2124).
///
/// The extractor must advance state twice: after the first push, the symbolic
/// state reflects push_back(42). After the second push, it should reflect a
/// nested push_back(push_back(42), 7) or equivalent chain.
#[test]
fn test_spec_advancement_chained_push() {
    let source = r#"
pub fn push_two(v: &mut Vec<i32>) {
v.push(42);
v.push(7);
}
"#;
    let extracted = extract_from_source(source, "push_two", &["v"]);

    let v_final = extracted
        .final_values
        .get("v")
        .expect("chained spec advancement should produce final value for v");

    // After two pushes, the final value should NOT be identity deref.
    assert!(
        !matches!(v_final, PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(n, _) if n == "v")),
        "v's final value should NOT be identity deref after two pushes; got {v_final:?}"
    );
}

/// Spec advancement preserves non-mutated params as identity (#2124).
///
/// When `push_one(v)` only mutates `v`, any other `&mut` params should
/// retain their identity deref (they were not advanced).
#[test]
fn test_spec_advancement_non_mutated_param_identity() {
    let source = r#"
pub fn push_one_of_two(a: &mut i32, v: &mut Vec<i32>) {
// keep the first mut param present so extraction proves non-mutated params stay identity
let _ = a;
v.push(42);
}
"#;
    let extracted = extract_from_source(source, "push_one_of_two", &["a", "v"]);

    // `a` is not mutated — should remain identity deref
    let a_final = extracted
        .final_values
        .get("a")
        .expect("non-mutated param should have final value");
    assert_deref_var(a_final, "a");

    // `v` was pushed to — should NOT be identity deref
    let v_final = extracted
        .final_values
        .get("v")
        .expect("mutated param should have final value");
    assert!(
        !matches!(v_final, PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(n, _) if n == "v")),
        "v should not be identity after push; got {v_final:?}"
    );
}

/// Spec-driven result binding: v.push(v.len()) — the two-phase borrow pattern.
///
/// This is the core pattern from `bug/two_phase.rs`. The len() call's result
/// must be bound to a concrete expression (via its spec `result@ == self@.len()`)
/// rather than an opaque variable, so that the push-back expression includes
/// a meaningful length value.
#[test]
fn test_spec_result_binding_push_len() {
    let source = r#"
pub fn push_len(v: &mut Vec<usize>) {
v.push(v.len());
}
"#;
    let extracted = extract_from_source(source, "push_len", &["v"]);

    let v_final = extracted
        .final_values
        .get("v")
        .expect("spec advancement should produce final value for v");

    // The final value should NOT be identity deref — the push advanced it.
    assert!(
        !matches!(v_final, PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(n, _) if n == "v")),
        "v's final value should NOT be identity deref after push(len()); got {v_final:?}"
    );

    // Verify the expression contains no opaque _call_N variables — the
    // spec result binding should produce a concrete expression for len().
    let has_opaque = contains_opaque_call_var(v_final);
    assert!(
        !has_opaque,
        "v's final value should NOT contain opaque _call_N variables; \
         the len() result should be bound via spec. Got {v_final:?}"
    );
}

#[test]
fn test_two_phase_push_len_delays_receiver_writeback() {
    let source = r#"
pub fn push_len(v: &mut Vec<usize>) {
v.push(v.len());
}
"#;
    let extracted = extract_from_source(source, "push_len", &["v"]);

    let resolve_results = extracted
        .resolve_results
        .as_ref()
        .expect("push(len()) should record resolve metadata");
    let writeback = resolve_results
        .writebacks
        .iter()
        .find(|writeback| writeback.parent_name == "v" && writeback.activation.is_some())
        .expect("push(len()) receiver borrow should be classified as delayed");

    assert!(
        extracted
            .delayed_writeback_assumptions
            .iter()
            .any(|expr| expr_is_delayed_writeback(expr, "v", &writeback.child_name)),
        "push(len()) should lower the receiver writeback into a delayed assumption"
    );

    if extracted
        .finality
        .get(&writeback.child_name)
        .is_some_and(|value| matches!(value, trust_wp_core::formula::BorrowFinality::Final { .. }))
    {
        assert!(
            extracted
                .delayed_writeback_assumptions
                .iter()
                .any(|expr| expr_is_final_writeback(expr, "v", &writeback.child_name)),
            "final two-phase borrows should also propagate parent_final == child_final"
        );
    }
}

/// Spec-driven result binding: chained push-then-len (#2124 Phase 3).
///
/// After v.push(42), v.len() should still be extractable. This tests that
/// the result binding works alongside mutation advancement.
#[test]
fn test_spec_result_binding_len_after_push() {
    let source = r#"
pub fn len_after_push(v: &mut Vec<i32>) -> usize {
v.push(42);
v.len()
}
"#;
    let extracted = extract_from_source(source, "len_after_push", &["v"]);

    let v_final = extracted
        .final_values
        .get("v")
        .expect("spec advancement should produce final value for v");

    // v was pushed to — should reflect post-push state
    assert!(
        !matches!(v_final, PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(n, _) if n == "v")),
        "v should not be identity after push; got {v_final:?}"
    );
}

/// Recursively check if an expression contains opaque `_call_N` variables.
fn contains_opaque_call_var(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(name, _) => name.starts_with("_call_"),
        PureExpr::Deref(inner)
        | PureExpr::View(inner)
        | PureExpr::Final(inner)
        | PureExpr::Old(inner) => contains_opaque_call_var(inner),
        PureExpr::BinOp(l, _, r) => contains_opaque_call_var(l) || contains_opaque_call_var(r),
        PureExpr::UnOp(_, inner) => contains_opaque_call_var(inner),
        PureExpr::Ite(c, t, e) => {
            contains_opaque_call_var(c)
                || contains_opaque_call_var(t)
                || contains_opaque_call_var(e)
        }
        PureExpr::MethodCall { receiver, args, .. } => {
            contains_opaque_call_var(receiver) || args.iter().any(contains_opaque_call_var)
        }
        PureExpr::LogicFnCall { args, .. } => args.iter().any(contains_opaque_call_var),
        _ => false,
    }
}

/// IndexMut continuation: `a[i] = x` through explicit IndexMut call (#2124 Phase 4).
///
/// Before Phase 4, `IndexMut::index_mut` calls would cause the mut_borrow
/// extraction to bail because the IndexMut spec uses relational postconditions
/// (`(^self)@[i] == ^result`) rather than a closed-form `(^self)@ == <expr>`.
/// Phase 4 detects IndexMut calls and records the returned `&mut T` reference
/// as a pending write, converting it to an IndexedWrite when `*result = val`
/// is encountered.
#[test]
fn test_index_mut_continuation_produces_indexed_write() {
    // Vec<i32> indexed write: a[0] = 42
    // MIR lowers this to IndexMut::index_mut(&mut a, 0) then *result = 42.
    let source = r#"
pub fn write_at_zero(a: &mut Vec<i32>) {
a[0] = 42;
}
"#;
    let extracted = extract_from_source(source, "write_at_zero", &["a"]);

    // The extraction should succeed (not bail at the IndexMut call).
    // The indexed write should be recorded.
    assert!(
        !extracted.indexed_writes.is_empty(),
        "IndexMut continuation should produce at least one IndexedWrite; got none. \
         Final values: {:?}",
        extracted.final_values
    );

    // The indexed write should reference param "a" with value 42.
    let iw = &extracted.indexed_writes[0];
    assert_eq!(
        iw.param_name, "a",
        "IndexedWrite param should be 'a', got '{}'",
        iw.param_name
    );
}

/// IndexMut continuation: slice indexed write `a[2] = 3` (#2124 Phase 4).
#[test]
fn test_index_mut_continuation_slice() {
    let source = r#"
pub fn write_at_two(a: &mut [u32]) {
a[2] = 3;
}
"#;
    let extracted = extract_from_source(source, "write_at_two", &["a"]);

    assert!(
        !extracted.indexed_writes.is_empty(),
        "Slice IndexMut should produce IndexedWrite; got none. \
         Final values: {:?}",
        extracted.final_values
    );
}

/// RangeInclusive sub-slice writes should be lifted back to parent indices.
#[test]
fn test_range_inclusive_subslice_writes_parent_indices() {
    let source = r#"
pub fn slice_range_inclusive(a: &mut [u32]) {
let s = &mut a[1..=2];
s[0] = 1;
s[1] = 1;
}
"#;
    let extracted = extract_from_source(source, "slice_range_inclusive", &["a"]);

    assert_eq!(
        extracted.indexed_writes.len(),
        2,
        "range sub-slice writes should lift to parent indexed writes; got {:?}",
        extracted.indexed_writes
    );
    assert!(
        extracted
            .indexed_writes
            .iter()
            .all(|write| write.param_name == "a"),
        "all lifted writes should target parent parameter 'a': {:?}",
        extracted.indexed_writes
    );
    assert!(
        extracted
            .indexed_writes
            .iter()
            .all(|write| !contains_opaque_call_var(&write.index)),
        "lifted range indices should use the public call-site alias, not opaque _call_N vars: {:?}",
        extracted.indexed_writes
    );
    assert!(
        extracted.final_values.get("a").is_some_and(
            |expr| matches!(expr, PureExpr::MethodCall { method, .. } if method == "set")
        ),
        "parent final value should advance through set calls; got {:?}",
        extracted.final_values.get("a")
    );
}

/// Phase 5 (#2124): After `a[0] = 42`, `final_values["a"]` should be an
/// intermediate-state expression reflecting the write — specifically a
/// `View(old).set(idx, val)` MethodCall, not the identity `Deref(Var("a"))`.
///
/// This is the key behavioral change that enables subsequent in-body reads
/// (like `assert!(a[0] == 42)`) to see the written value.
#[test]
fn test_index_mut_intermediate_state_advances_deref_exprs() {
    let source = r#"
pub fn write_at_zero(a: &mut Vec<i32>) {
a[0] = 42;
}
"#;
    let extracted = extract_from_source(source, "write_at_zero", &["a"]);

    // After Phase 5, final_values["a"] should be the intermediate state
    // expression `View(Deref(Var("a"))).set(0, 42)`, which is a MethodCall.
    let final_a = extracted
        .final_values
        .get("a")
        .expect("final_values should contain 'a' after IndexMut write");

    // The expression should be a MethodCall with method "set".
    match final_a {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            assert_eq!(
                method, "set",
                "final_values['a'] should be a .set() call; got .{method}()"
            );
            // receiver should be View(Deref(Var("a")))
            assert!(
                matches!(receiver.as_ref(), PureExpr::View(inner) if matches!(inner.as_ref(), PureExpr::Deref(_))),
                "set receiver should be View(Deref(Var(\"a\"))); got {receiver:?}"
            );
            assert_eq!(
                args.len(),
                2,
                "set should have 2 args (index, value); got {}",
                args.len()
            );
        }
        other => panic!("final_values['a'] should be MethodCall(.set()), got {other:?}"),
    }
}

/// Direct unit test for `make_typed_deref_expr` helper (#2343).
///
/// The IndexMut continuation fallback in the mut_borrow traversal calls
/// `make_typed_deref_expr`
/// to build `Deref(Var(name, sort))` with enriched sort metadata from MIR types.
/// The fallback is defensive (unreachable in normal MIR because `PendingIndexMut`
/// is only created when `deref_exprs` already has the receiver), so this test
/// validates the helper directly to prove the fix is material. If anyone regresses
/// the helper, this test catches it regardless of which call-site is affected.
#[test]
fn test_make_typed_deref_expr_produces_enriched_sort() {
    struct HelperCallbacks {
        result: Option<PureExpr>,
    }
    impl Callbacks for HelperCallbacks {
        #[allow(clippy::elidable_lifetime_names)]
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            for owner in tcx.hir_body_owners() {
                let def_id = owner.to_def_id();
                let path = tcx.def_path_str(def_id);
                if path != "identity_vec" && !path.ends_with("::identity_vec") {
                    continue;
                }
                let body = tcx.optimized_mir(def_id);
                // _1 is the first argument (a: &mut Vec<i32>)
                let local = rustc_middle::mir::Local::from_usize(1);
                self.result = Some(make_typed_deref_expr(tcx, body, local, "a"));
                break;
            }
            Compilation::Stop
        }
    }

    let source = r#"pub fn identity_vec(_a: &mut Vec<i32>) {}"#;

    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_mut_borrow_helper_{}_{}",
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
        "trust_wp_mut_borrow_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];
    let mut callbacks = HelperCallbacks { result: None };
    run_compiler(&args, &mut callbacks);
    let _ = fs::remove_dir_all(&temp_dir);

    let expr = callbacks
        .result
        .expect("callback should invoke make_typed_deref_expr");

    // make_typed_deref_expr must produce Deref(Var("a", Some(sort)))
    let PureExpr::Deref(inner) = &expr else {
        panic!("expected Deref(...); got {expr:?}");
    };
    let PureExpr::Var(name, sort) = inner.as_ref() else {
        panic!("expected Var inside Deref; got {inner:?}");
    };
    assert_eq!(name, "a", "helper should use the supplied name");
    assert!(
        sort.is_some(),
        "make_typed_deref_expr must produce non-None sort for &mut Vec<i32>; \
         got Var(\"{name}\", None) — this is the #2343 sort-erasure bug"
    );
}

#[test]
fn test_direct_closure_field_seeds_preserve_capture_sort() {
    struct ClosureSeedCallbacks {
        result: Option<Vec<type_analysis::ClosureFieldSeed>>,
    }

    impl Callbacks for ClosureSeedCallbacks {
        #[allow(clippy::elidable_lifetime_names)]
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            for owner in tcx.hir_body_owners() {
                let def_id = owner.to_def_id();
                if tcx.def_kind(def_id) != DefKind::Closure {
                    continue;
                }

                let body = tcx.optimized_mir(def_id);
                self.result = Some(type_analysis::direct_closure_field_seeds(
                    tcx,
                    body,
                    CAPTURE_STRUCT_LOCAL,
                ));
                break;
            }
            Compilation::Stop
        }
    }

    let source = r#"
pub fn make_bool_closure(flag: &mut bool) {
    let _c = move || {
        *flag = true;
    };
}
"#;

    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_mut_borrow_closure_seed_{}_{}",
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
        "trust_wp_mut_borrow_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];
    let mut callbacks = ClosureSeedCallbacks { result: None };
    run_compiler(&args, &mut callbacks);
    let _ = fs::remove_dir_all(&temp_dir);

    let seeds = callbacks
        .result
        .expect("callback should collect closure field seeds");
    assert_eq!(
        seeds.len(),
        1,
        "expected exactly one direct closure field seed for moved `&mut bool`; got {seeds:?}"
    );
    assert_eq!(seeds[0].field_idx, 0);
    assert_eq!(
        seeds[0].sort,
        Some(trust_wp_core::formula::ExprSort::MutRef(Box::new(
            trust_wp_core::formula::ExprSort::Bool,
        ))),
        "closure field seed should preserve the declared `&mut bool` sort"
    );
}

#[test]
fn test_extract_mut_borrow_closure_field_placeholder_preserves_capture_sort() {
    let source = r#"
pub fn make_bool_closure(flag: &mut bool) {
    let mut c = move || {
        *flag = !*flag;
    };
    c();
}
"#;

    let extracted = extract_from_first_closure_source(source);
    let final_self_0 = extracted
        .final_values
        .get("self.0")
        .expect("closure extraction should record final value for self.0");

    let expected_sort = Some(trust_wp_core::formula::ExprSort::MutRef(Box::new(
        trust_wp_core::formula::ExprSort::Bool,
    )));
    assert!(
        expr_contains_var_with_sort(final_self_0, "self.0", &expected_sort),
        "closure field placeholder should preserve the declared `&mut bool` sort \
         through extract_mut_borrow_body; got {final_self_0:?}"
    );
}

/// Regression test (#2343): The IndexMut continuation fallback must preserve
/// the receiver's `ExprSort` annotation. Before the fix, the fallback
/// reconstructed `Deref(Var(name, None))` — dropping the sort from MIR types.
/// The inner `Var` in `View(Deref(Var("a", sort))).set(...)` must carry
/// `Some(ExprSort::Seq)` for `Vec<i32>`, not `None`.
#[test]
fn test_index_mut_fallback_preserves_receiver_sort() {
    let source = r#"
pub fn write_at_zero(a: &mut Vec<i32>) {
a[0] = 42;
}
"#;
    let extracted = extract_from_source(source, "write_at_zero", &["a"]);

    let final_a = extracted
        .final_values
        .get("a")
        .expect("final_values should contain 'a' after IndexMut write");

    // Drill into MethodCall { receiver: View(Deref(Var("a", sort))), ... }
    let PureExpr::MethodCall { receiver, .. } = final_a else {
        panic!("expected MethodCall(.set()); got {final_a:?}");
    };
    let PureExpr::View(view_inner) = receiver.as_ref() else {
        panic!("expected View(...) receiver; got {receiver:?}");
    };
    let PureExpr::Deref(deref_inner) = view_inner.as_ref() else {
        panic!("expected Deref(...) inside View; got {view_inner:?}");
    };
    let PureExpr::Var(name, sort) = deref_inner.as_ref() else {
        panic!("expected Var inside Deref; got {deref_inner:?}");
    };
    assert_eq!(name, "a", "inner Var name should be 'a'");
    assert!(
        sort.is_some(),
        "inner Var sort must not be None (sort erasure bug #2343); got Var(\"{name}\", None)"
    );
}

/// Phase 5 (#2124): Two indexed writes chain correctly — the second write's
/// receiver is the intermediate state from the first write, not the entry state.
#[test]
fn test_index_mut_chained_writes_advance_state() {
    let source = r#"
pub fn two_writes(a: &mut Vec<i32>) {
a[0] = 10;
a[1] = 20;
}
"#;
    let extracted = extract_from_source(source, "two_writes", &["a"]);

    assert_eq!(
        extracted.indexed_writes.len(),
        2,
        "should produce 2 IndexedWrites; got {}",
        extracted.indexed_writes.len()
    );

    // final_values["a"] should be the result of chaining: set(set(initial, 0, 10), 1, 20)
    let final_a = extracted
        .final_values
        .get("a")
        .expect("final_values should contain 'a'");

    // Outer should be set(..., 1, 20)
    match final_a {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            assert_eq!(method, "set", "outer should be .set()");
            // Inner receiver should also be a .set() call (the first write)
            match receiver.as_ref() {
                PureExpr::MethodCall {
                    method: inner_method,
                    ..
                } => {
                    assert_eq!(
                        inner_method, "set",
                        "inner receiver should also be .set() (chained writes)"
                    );
                }
                // Also acceptable: View(set(...)) depending on encoding
                PureExpr::View(inner) => match inner.as_ref() {
                    PureExpr::MethodCall {
                        method: inner_method,
                        ..
                    } => {
                        assert_eq!(
                            inner_method, "set",
                            "inner View'd receiver should be .set() (chained writes)"
                        );
                    }
                    other => panic!("inner View should contain .set(); got {other:?}"),
                },
                other => {
                    panic!("chained write receiver should be .set() or View(.set()); got {other:?}")
                }
            }
            assert_eq!(args.len(), 2, "set should have 2 args");
        }
        other => panic!("final_values['a'] should be MethodCall(.set()), got {other:?}"),
    }
}

// --- reborrow_map edge case tests (#1701) ---

/// Both `&mut` params mutated through distinct reborrows simultaneously.
///
/// Exercises reborrow_map holding two concurrent entries and
/// `get_deref_target` resolving each to the correct origin.
/// Previous tests only mutated the second param.
#[test]
fn test_reborrow_both_params_mutated_simultaneously() {
    let source = r#"
pub fn bump_both(a: &mut i32, b: &mut i32) {
let ra = &mut *a;
let rb = &mut *b;
*ra = *ra + 1;
*rb = *rb + 2;
}
"#;

    let extracted = extract_from_source(source, "bump_both", &["a", "b"]);
    let a_final = extracted
        .final_values
        .get("a")
        .expect("expected final value for first &mut param");
    let b_final = extracted
        .final_values
        .get("b")
        .expect("expected final value for second &mut param");
    assert_deref_plus_int(a_final, "a", 1);
    assert_deref_plus_int(b_final, "b", 2);
}

/// First-param-only reborrow (existing tests only reborrow param 1, never param 0 alone).
///
/// Exercises `resolve_reborrow_param_local` for `Local::from_usize(1)` (first param)
/// while the second param stays identity.
#[test]
fn test_reborrow_first_param_only() {
    let source = r#"
pub fn bump_first(a: &mut i32, b: &mut i32) {
let r = &mut *a;
*r = *r + 10;
let _ = b;
}
"#;

    let extracted = extract_from_source(source, "bump_first", &["a", "b"]);
    let a_final = extracted
        .final_values
        .get("a")
        .expect("expected final value for first &mut param");
    let b_final = extracted
        .final_values
        .get("b")
        .expect("expected final value for second &mut param");
    assert_deref_plus_int(a_final, "a", 10);
    assert_deref_var(b_final, "b");
}

/// 3+ `&mut` params: exercises `Local::from_usize(i + 1)` indexing beyond `_1` and `_2`.
///
/// With 3 params `(a, b, c)`, the locals are `_1`, `_2`, `_3`. The reborrow
/// targets `c` (`_3`) to verify `find_mut_borrow_params` generates the
/// correct local set and reborrow resolution works for the third param.
#[test]
fn test_reborrow_three_mut_params() {
    let source = r#"
pub fn bump_third(a: &mut i32, b: &mut i32, c: &mut i32) {
let r = &mut *c;
*r = *r + 3;
let _ = a;
let _ = b;
}
"#;

    let extracted = extract_from_source(source, "bump_third", &["a", "b", "c"]);
    let a_final = extracted
        .final_values
        .get("a")
        .expect("expected final value for param a");
    let b_final = extracted
        .final_values
        .get("b")
        .expect("expected final value for param b");
    let c_final = extracted
        .final_values
        .get("c")
        .expect("expected final value for param c");
    assert_deref_var(a_final, "a");
    assert_deref_var(b_final, "b");
    assert_deref_plus_int(c_final, "c", 3);
}

/// Conditional reborrow writes: SwitchInt branch cloning of `reborrow_map`.
///
/// The reborrow `r = &mut *b` is established before the branch. Both branches
/// write through `r`, which requires `reborrow_map` to be cloned (line 893)
/// so each branch independently resolves `*r` → `b`. The result should be
/// an `Ite(flag, Deref(b)+1, Deref(b)+2)`.
#[test]
fn test_reborrow_conditional_writes() {
    let source = r#"
pub fn cond_bump(a: &mut i32, b: &mut i32, flag: bool) {
let r = &mut *b;
if flag {
    *r = *r + 1;
} else {
    *r = *r + 2;
}
let _ = a;
}
"#;

    let extracted = extract_from_source(source, "cond_bump", &["a", "b", "flag"]);
    let a_final = extracted
        .final_values
        .get("a")
        .expect("expected final value for param a");
    let b_final = extracted
        .final_values
        .get("b")
        .expect("expected final value for param b");
    // a is unchanged but the SwitchInt merge wraps all mut params in Ite.
    // Accept either plain identity or Ite with both branches identity.
    match a_final {
        PureExpr::Deref(_) => assert_deref_var(a_final, "a"),
        PureExpr::Ite(_cond, then_val, else_val) => {
            assert_deref_var(then_val, "a");
            assert_deref_var(else_val, "a");
        }
        other => panic!("expected identity (or Ite-wrapped identity) for a; got {other:?}"),
    }

    // b should be Ite(flag_condition, Deref(Var("b"))+1, Deref(Var("b"))+2)
    match b_final {
        PureExpr::Ite(cond, then_val, else_val) => {
            // The condition should reference the flag parameter
            assert!(
                !matches!(cond.as_ref(), PureExpr::Bool(_)),
                "condition should be symbolic (flag), not a constant; got {cond:?}"
            );
            // Both branches should update b by different amounts
            assert_deref_plus_int(then_val, "b", 1);
            assert_deref_plus_int(else_val, "b", 2);
        }
        other => panic!(
            "expected Ite(flag, Deref(b)+1, Deref(b)+2) for conditional reborrow; got {other:?}"
        ),
    }
}

/// Sequential reborrow from different params: reborrow `a`, write, then reborrow `b`, write.
///
/// Exercises the reborrow_map tracking across sequential reborrows from
/// different `&mut` params. In optimized MIR, the compiler may eliminate
/// intermediate reborrows and write directly through params, but the
/// final values must still correctly attribute writes to the right params.
/// If reborrows survive optimization, this also exercises the eviction
/// at lines 578-579 (stale mapping removal on reassignment).
#[test]
fn test_reborrow_sequential_different_params() {
    let source = r#"
pub fn sequential_reborrow(a: &mut i32, b: &mut i32) {
let r1 = &mut *a;
*r1 = *r1 + 1;
let r2 = &mut *b;
*r2 = *r2 + 2;
}
"#;

    let extracted = extract_from_source(source, "sequential_reborrow", &["a", "b"]);
    let a_final = extracted
        .final_values
        .get("a")
        .expect("expected final value for param a");
    let b_final = extracted
        .final_values
        .get("b")
        .expect("expected final value for param b");
    // a gets +1 from the first reborrow write
    assert_deref_plus_int(a_final, "a", 1);
    // b gets +2 from the second reborrow write
    assert_deref_plus_int(b_final, "b", 2);
}

/// Diverging branch (panic from `assert!()`) should not bail the extraction.
///
/// Before Phase 7 (#2124), any branch that reached a diverging call (panic!,
/// unreachable!, etc.) caused the SwitchInt handler to propagate None, bailing
/// the entire extraction. This test verifies that when one SwitchInt branch
/// diverges, the non-diverging branch's final values are used directly.
#[test]
fn test_diverging_branch_assert_does_not_bail_extraction() {
    let source = r#"
pub fn write_then_assert(x: &mut i32, val: i32) {
*x = val;
assert!(*x > 0);
}
"#;

    let extracted = extract_from_source(source, "write_then_assert", &["x", "val"]);
    let x_final = extracted
        .final_values
        .get("x")
        .expect("expected final value for param x — extraction should not bail on assert!()");
    // The final value of *x should be `val` (the written value), not identity.
    // The assert!() generates a SwitchInt where the panic branch diverges.
    match x_final {
        PureExpr::Var(name, _) => {
            assert_eq!(
                name, "val",
                "expected *x final value to be `val` (written), got Var({name:?})"
            );
        }
        other => panic!(
            "expected final value Var(\"val\") for x after `*x = val; assert!(...)`, got {other:?}"
        ),
    }
}

/// Newtype wrapping `&mut T`: the bug/486 pattern.
///
/// `HasMutRef<'a, T>(pub &'a mut T)` is a single-field struct wrapping a `&mut`.
/// Writing `*x.0 = 5` must produce `final_values["x.0"] = Int(5)` and
/// `final_values["x"] = tuple1(Int(5))` (the newtype wrapper). (#2124)
#[test]
fn test_newtype_wrapping_mut_field_deref_write() {
    let source = r#"
pub struct HasMutRef<'a, T>(pub &'a mut T);

pub fn test(x: HasMutRef<'_, u32>) {
*x.0 = 5
}
"#;
    let extracted = extract_from_source(source, "test", &["x"]);

    // final_values should contain "x.0" (the field's final value)
    let x0_final = extracted
        .final_values
        .get("x.0")
        .expect("field deref write should produce final value for x.0");
    // The value written is the literal 5
    assert!(
        matches!(x0_final, PureExpr::Int(5)),
        "x.0 final value should be Int(5); got {x0_final:?}"
    );

    // final_values should also contain "x" wrapped in tuple1
    let whole_param_final = extracted
        .final_values
        .get("x")
        .expect("newtype should produce whole-param final value for x");
    // Should be LogicFnCall { name: "__trust_wp_tuple1", args: [Int(5)] }
    match whole_param_final {
        PureExpr::LogicFnCall { name, args } => {
            assert!(
                name.contains("tuple1"),
                "newtype wrapping should produce tuple1; got {name}"
            );
            assert_eq!(args.len(), 1, "tuple1 should have 1 arg");
        }
        other => panic!("expected tuple1 wrapper for newtype x; got {other:?}"),
    }
}

// ── Lane P1b: driver-backed MutRef sort annotation probes (#2141) ───────

/// Verifies that `ExprSort::MutRef(Int)` survives through `extract_mut_borrow_body`
/// into `final_values`. This is the driver-backed positive control for the whole-MutRef
/// carrier path: if the Var node inside Deref loses its sort annotation, the ay
/// encoder's whole-borrow gate (bindings.rs) will never activate.
///
/// Re: #2141, designs/2026-03-19-2141-post-gate-mutref-evidence-split.md Slice 1
#[test]
fn test_final_values_preserve_mutref_int_sort_annotation() {
    let source = r#"
pub fn increment_ref(v: &mut i32) {
    *v += 1;
}
"#;

    let extracted = extract_from_source(source, "increment_ref", &["v"]);
    let v_final = extracted
        .final_values
        .get("v")
        .expect("v should have a final value");

    let expected_sort = Some(ExprSort::MutRef(Box::new(ExprSort::Int)));
    assert!(
        expr_contains_var_with_sort(v_final, "v", &expected_sort),
        "final_values[v] should preserve MutRef(Int) sort annotation from MIR type: {v_final:?}"
    );
}

/// Verifies that `ExprSort::MutRef(Bool)` survives for boolean `&mut` parameters.
/// Bool-sorted vars take a different inference path in the ay encoder; confirming
/// the driver preserves the annotation avoids a fallback-to-Int demotion.
///
/// Re: #2141, designs/2026-03-19-2141-post-gate-mutref-evidence-split.md Slice 1
#[test]
fn test_final_values_preserve_mutref_bool_sort_annotation() {
    let source = r#"
pub fn toggle_ref(flag: &mut bool) {
    *flag = !*flag;
}
"#;

    let extracted = extract_from_source(source, "toggle_ref", &["flag"]);
    let flag_final = extracted
        .final_values
        .get("flag")
        .expect("flag should have a final value");

    let expected_sort = Some(ExprSort::MutRef(Box::new(ExprSort::Bool)));
    assert!(
        expr_contains_var_with_sort(flag_final, "flag", &expected_sort),
        "final_values[flag] should preserve MutRef(Bool) sort annotation: {flag_final:?}"
    );
}

/// Verifies that reborrow chains preserve `ExprSort::MutRef(Int)` on the
/// parent's final_values entry. When `y = &mut *x` creates a reborrow, the
/// parent `x`'s final_values entry must still carry MutRef so the ay
/// whole-borrow gate activates for the parent variable.
///
/// Re: #2141, designs/2026-03-19-2141-post-gate-mutref-evidence-split.md Slice 1
#[test]
fn test_reborrow_parent_preserves_mutref_sort_on_final_values() {
    let source = r#"
pub fn reborrow_increment(x: &mut i32) {
    let y = &mut *x;
    *y = *y + 1;
}
"#;

    let extracted = extract_from_source(source, "reborrow_increment", &["x"]);
    let x_final = extracted
        .final_values
        .get("x")
        .expect("parent x should have a final value");

    let expected_sort = Some(ExprSort::MutRef(Box::new(ExprSort::Int)));
    assert!(
        expr_contains_var_with_sort(x_final, "x", &expected_sort),
        "parent x final_values should preserve MutRef(Int) through reborrow chain: {x_final:?}"
    );

    // Also verify the child borrow-id origin is recorded
    let child_name = child_name_for_parent(&extracted, "x");
    assert!(
        extracted.borrow_id_origins.contains_key(&child_name),
        "reborrow child {child_name} should have a borrow-id origin"
    );
}

/// Verifies that tuple-of-`&mut` parameters preserve `ExprSort::Tuple(2)` sort on the
/// whole-tuple Var and produce per-field entries in `final_values`. This is the Lane A1
/// tuple transport probe: when the driver processes `_x: (&mut u32, &mut u32)`, the
/// encoder needs both the Tuple sort (for `tuple_get` axioms) and the field-level
/// entries (for per-field final-value reasoning).
///
/// Unlike single-&mut probes (`test_final_values_preserve_mutref_int_sort_annotation`),
/// the Var for `_x` carries `Tuple(2)`, not `MutRef(Int)` — the `MutRef` is on the
/// *field types*, not the whole parameter.
///
/// Re: #2141, designs/2026-03-19-2141-post-gate-mutref-evidence-split.md Slice 1
#[test]
fn test_tuple_of_mut_ref_preserves_tuple_sort_and_field_entries() {
    let source = r#"
pub fn drop_pair(_x: (&mut u32, &mut u32)) {}
"#;

    let extracted = extract_from_source(source, "drop_pair", &["_x"]);

    // 1. Whole-tuple Var should carry Tuple(2) sort
    let x_final = extracted
        .final_values
        .get("_x")
        .expect("_x should have a final value");

    let expected_sort = Some(ExprSort::Tuple(2));
    assert!(
        expr_contains_var_with_sort(x_final, "_x", &expected_sort),
        "final_values[_x] should preserve Tuple(2) sort for tuple-of-&mut param: {x_final:?}"
    );

    // 2. Per-field entries should exist (field decomposition active)
    assert!(
        extracted.final_values.contains_key("_x.0"),
        "final_values should contain per-field entry _x.0 for tuple field 0"
    );
    assert!(
        extracted.final_values.contains_key("_x.1"),
        "final_values should contain per-field entry _x.1 for tuple field 1"
    );
}

/// Regression test (#2318): A FnMut closure capturing `Box<&mut i32>` by move
/// must produce final_values with at least a whole-deref entry for "self".
/// This verifies that `direct_closure_field_seeds` + `type_eventually_contains_mut_ref`
/// correctly admit Box-wrapped captures through the mut-borrow extraction pipeline.
///
/// For FnMut closures (_1 is &mut ClosureEnv), `type_contains_mut_ref_with_tcx`
/// detects the outer &mut directly. The field-level tracking depends on
/// `direct_closure_field_seeds` producing seeds for the Box-wrapped capture.
#[test]
fn test_fnmut_closure_box_wrapped_mut_ref_capture_produces_final_values() {
    let source = r#"
pub fn test_box_capture(bx: Box<&mut i32>) {
    let mut c = move || {
        **bx += 1;
    };
    c();
}
"#;

    // Use extract_from_first_closure_source which names the closure env "self".
    let extracted = extract_from_first_closure_source(source);

    // The closure captures bx (Box<&mut i32>). After extraction, we should
    // have at minimum a "self" whole-deref entry (FnMut path).
    assert!(
        !extracted.final_values.is_empty(),
        "FnMut closure with Box<&mut i32> capture should produce non-empty \
         final_values; keys: {:?}",
        extracted.final_values.keys().collect::<Vec<_>>()
    );
    // Accept either "self" (whole-deref) or "self.0" (per-field) — both indicate
    // successful admission. Per-field tracking may or may not activate depending
    // on the MIR shape.
    assert!(
        extracted.final_values.contains_key("self")
            || extracted.final_values.contains_key("self.0"),
        "final_values should contain either 'self' or 'self.0' entry for the \
         Box<&mut i32> capture; keys: {:?}",
        extracted.final_values.keys().collect::<Vec<_>>()
    );
}

/// Regression test (#2318): Same as above but with `Box<Box<&mut i32>>` —
/// two levels of wrapping. Verifies that `type_eventually_contains_mut_ref`
/// walks through arbitrarily nested single-field ADTs.
#[test]
fn test_fnmut_closure_double_box_wrapped_mut_ref_capture_produces_final_values() {
    let source = r#"
pub fn test_double_box_capture(by: Box<Box<&mut i32>>) {
    let mut c = move || {
        ***by += 2;
    };
    c();
}
"#;

    let extracted = extract_from_first_closure_source(source);

    assert!(
        !extracted.final_values.is_empty(),
        "FnMut closure with Box<Box<&mut i32>> capture should produce non-empty \
         final_values; keys: {:?}",
        extracted.final_values.keys().collect::<Vec<_>>()
    );
    assert!(
        extracted.final_values.contains_key("self")
            || extracted.final_values.contains_key("self.0"),
        "final_values should contain either 'self' or 'self.0' entry for the \
         Box<Box<&mut i32>> capture; keys: {:?}",
        extracted.final_values.keys().collect::<Vec<_>>()
    );
}

/// Regression test (#2318): A closure env type for FnOnce is passed by value
/// (not `&mut Self`). `type_contains_mut_ref_with_tcx` won't detect nested
/// `&mut` through wrapper chains. The fix in `find_mut_borrow_params` uses
/// `closure_env_has_nested_mut_ref` to walk upvar types at arbitrary depth.
///
/// This test verifies that `direct_closure_field_seeds` sees Box-wrapped
/// mut-ref captures in the upvar metadata.
#[test]
fn test_direct_closure_field_seeds_box_wrapped_mut_ref() {
    struct ClosureSeedCallbacks {
        result: Option<Vec<type_analysis::ClosureFieldSeed>>,
    }

    impl Callbacks for ClosureSeedCallbacks {
        #[allow(clippy::elidable_lifetime_names)]
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            for owner in tcx.hir_body_owners() {
                let def_id = owner.to_def_id();
                if tcx.def_kind(def_id) != DefKind::Closure {
                    continue;
                }

                let body = tcx.optimized_mir(def_id);
                self.result = Some(type_analysis::direct_closure_field_seeds(
                    tcx,
                    body,
                    CAPTURE_STRUCT_LOCAL,
                ));
                break;
            }
            Compilation::Stop
        }
    }

    let source = r#"
pub fn test_box_capture(bx: Box<&mut i32>) {
    let mut c = move || {
        **bx += 1;
    };
    c();
}
"#;

    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_mut_borrow_box_seed_{}_{}",
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
        "trust_wp_mut_borrow_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];
    let mut callbacks = ClosureSeedCallbacks { result: None };
    run_compiler(&args, &mut callbacks);
    let _ = fs::remove_dir_all(&temp_dir);

    let seeds = callbacks
        .result
        .expect("callback should collect closure field seeds");
    assert!(
        !seeds.is_empty(),
        "expected at least one closure field seed for moved `Box<&mut i32>`; got {seeds:?}"
    );
    assert_eq!(seeds[0].field_idx, 0);
}

/// Regression test (#2318): FnOnce closures take `self` by value, so the
/// closure env type is `ClosureEnv` (not `&mut ClosureEnv`). When a FnOnce
/// closure captures `Box<&mut i32>`, `type_contains_mut_ref_with_tcx` returns
/// false because the env type itself has no direct `&mut` at depth 0-1.
/// The fix in `find_mut_borrow_params` uses `closure_env_has_nested_mut_ref`
/// to walk upvar types at arbitrary depth through Box/Unique/NonNull wrappers.
///
/// This test forces FnOnce semantics by consuming (dropping) the Box inside
/// the closure body, which prevents the closure from implementing FnMut.
#[test]
fn test_fnonce_closure_box_wrapped_mut_ref_capture_produces_final_values() {
    // Force FnOnce: `drop(bx)` moves the Box out of the env, so the closure
    // can only be called once. The `_1` parameter type in the closure MIR is
    // `ClosureEnv` (by value), not `&mut ClosureEnv`.
    let source = r#"
fn consume_box(_b: Box<&mut i32>) {}
pub fn test_fnonce_box_capture(bx: Box<&mut i32>) {
    let c = move || {
        consume_box(bx);
    };
    c();
}
"#;

    let extracted = extract_from_first_closure_source(source);

    // FnOnce closure: self is by-value. The pipeline should still detect the
    // nested &mut inside Box and produce final_values.
    assert!(
        !extracted.final_values.is_empty(),
        "FnOnce closure with Box<&mut i32> capture should produce non-empty \
         final_values; keys: {:?}",
        extracted.final_values.keys().collect::<Vec<_>>()
    );
    assert!(
        extracted.final_values.contains_key("self")
            || extracted.final_values.contains_key("self.0"),
        "final_values should contain either 'self' or 'self.0' entry for the \
         Box<&mut i32> FnOnce capture; keys: {:?}",
        extracted.final_values.keys().collect::<Vec<_>>()
    );
}

/// Regression test (#2318 slice 2): `get_deref_target` must peel wrapper
/// projections back to the owning capture field for `Box<&mut T>`-style
/// writes, even when the place carries extra deref layers after the field.
#[test]
fn test_get_deref_target_box_wrapped_mut_ref_peels_to_capture_field() {
    struct TargetCallbacks {
        result: Option<Option<super::data::DerefTarget>>,
    }

    impl Callbacks for TargetCallbacks {
        #[allow(clippy::elidable_lifetime_names)]
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            for owner in tcx.hir_body_owners() {
                let def_id = owner.to_def_id();
                if tcx.def_kind(def_id) != DefKind::Fn {
                    continue;
                }

                let body = tcx.optimized_mir(def_id);
                let base_place =
                    rustc_middle::mir::Place::from(rustc_middle::mir::Local::from_usize(1));
                let projected = base_place.project_deeper(
                    &[
                        rustc_middle::mir::ProjectionElem::Deref,
                        rustc_middle::mir::ProjectionElem::Field(
                            rustc_abi::FieldIdx::from_u32(0),
                            tcx.types.i32,
                        ),
                        rustc_middle::mir::ProjectionElem::Deref,
                        rustc_middle::mir::ProjectionElem::Deref,
                    ],
                    tcx,
                );
                self.result = Some(super::place_utils::get_deref_target(
                    &projected,
                    body,
                    &[rustc_middle::mir::Local::from_usize(1)],
                    &std::collections::HashMap::new(),
                ));
                break;
            }
            Compilation::Stop
        }
    }

    let source = r#"
pub fn test_box_capture(x: &mut i32) {
    let _ = x;
}
"#;

    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_mut_borrow_box_target_{}_{}",
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
        "trust_wp_mut_borrow_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];
    let mut callbacks = TargetCallbacks { result: None };
    run_compiler(&args, &mut callbacks);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(matches!(
        callbacks.result.expect("callback should collect target result"),
        Some(super::data::DerefTarget::Field(local, 0))
            if local == rustc_middle::mir::Local::from_usize(1)
    ));
}

/// Regression test (#2318 slice 2): same as above, but with an extra wrapper
/// layer to cover `Box<Box<&mut T>>`-style writes.
#[test]
fn test_get_deref_target_double_box_wrapped_mut_ref_peels_to_capture_field() {
    struct TargetCallbacks {
        result: Option<Option<super::data::DerefTarget>>,
    }

    impl Callbacks for TargetCallbacks {
        #[allow(clippy::elidable_lifetime_names)]
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            for owner in tcx.hir_body_owners() {
                let def_id = owner.to_def_id();
                if tcx.def_kind(def_id) != DefKind::Fn {
                    continue;
                }

                let body = tcx.optimized_mir(def_id);
                let base_place =
                    rustc_middle::mir::Place::from(rustc_middle::mir::Local::from_usize(1));
                let projected = base_place.project_deeper(
                    &[
                        rustc_middle::mir::ProjectionElem::Deref,
                        rustc_middle::mir::ProjectionElem::Field(
                            rustc_abi::FieldIdx::from_u32(0),
                            tcx.types.i32,
                        ),
                        rustc_middle::mir::ProjectionElem::Deref,
                        rustc_middle::mir::ProjectionElem::Deref,
                        rustc_middle::mir::ProjectionElem::Deref,
                    ],
                    tcx,
                );
                self.result = Some(super::place_utils::get_deref_target(
                    &projected,
                    body,
                    &[rustc_middle::mir::Local::from_usize(1)],
                    &std::collections::HashMap::new(),
                ));
                break;
            }
            Compilation::Stop
        }
    }

    let source = r#"
pub fn test_box_capture(x: &mut i32) {
    let _ = x;
}
"#;

    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_mut_borrow_dblbox_target_{}_{}",
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
        "trust_wp_mut_borrow_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];
    let mut callbacks = TargetCallbacks { result: None };
    run_compiler(&args, &mut callbacks);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(matches!(
        callbacks.result.expect("callback should collect target result"),
        Some(super::data::DerefTarget::Field(local, 0))
            if local == rustc_middle::mir::Local::from_usize(1)
    ));
}

/// Regression test (#2318): FnOnce closure with `Box<Box<&mut i32>>` — two
/// levels of Box wrapping. Verifies that `closure_env_has_nested_mut_ref`
/// correctly walks through arbitrarily deep Box chains (Box -> Unique ->
/// NonNull -> *const -> Box -> Unique -> NonNull -> *const -> &mut).
/// Forces FnOnce by consuming the outer Box inside the closure.
#[test]
fn test_fnonce_closure_double_box_wrapped_mut_ref_capture_produces_final_values() {
    let source = r#"
fn consume_double_box(_b: Box<Box<&mut i32>>) {}
pub fn test_fnonce_double_box_capture(by: Box<Box<&mut i32>>) {
    let c = move || {
        consume_double_box(by);
    };
    c();
}
"#;

    let extracted = extract_from_first_closure_source(source);

    assert!(
        !extracted.final_values.is_empty(),
        "FnOnce closure with Box<Box<&mut i32>> capture should produce non-empty \
         final_values; keys: {:?}",
        extracted.final_values.keys().collect::<Vec<_>>()
    );
    assert!(
        extracted.final_values.contains_key("self")
            || extracted.final_values.contains_key("self.0"),
        "final_values should contain either 'self' or 'self.0' entry for the \
         Box<Box<&mut i32>> FnOnce capture; keys: {:?}",
        extracted.final_values.keys().collect::<Vec<_>>()
    );
}

/// Regression test (#2318): FnOnce closure capturing multiple Box-wrapped
/// `&mut` references. Both captures should be admitted through the mut-borrow
/// pipeline. This exercises `direct_closure_field_seeds` returning multiple
/// seeds (one per captured upvar) and `closure_env_has_nested_mut_ref`
/// triggering for the env as a whole.
/// Forces FnOnce by consuming both Boxes inside the closure via helper fns.
#[test]
fn test_fnonce_closure_multiple_box_wrapped_mut_ref_captures() {
    let source = r#"
fn consume_int(_b: Box<&mut i32>) {}
fn consume_bool(_b: Box<&mut bool>) {}
pub fn test_multi_capture(bx: Box<&mut i32>, by: Box<&mut bool>) {
    let c = move || {
        consume_int(bx);
        consume_bool(by);
    };
    c();
}
"#;

    let extracted = extract_from_first_closure_source(source);

    assert!(
        !extracted.final_values.is_empty(),
        "FnOnce closure with multiple Box<&mut T> captures should produce non-empty \
         final_values; keys: {:?}",
        extracted.final_values.keys().collect::<Vec<_>>()
    );
    // The closure env should be admitted (at least a whole-deref "self" entry).
    assert!(
        extracted.final_values.contains_key("self")
            || extracted.final_values.contains_key("self.0")
            || extracted.final_values.contains_key("self.1"),
        "final_values should contain entries for Box-wrapped captures; keys: {:?}",
        extracted.final_values.keys().collect::<Vec<_>>()
    );
}

/// Regression test (#2318 Slice 1): admit only the top-level capture fields
/// whose types eventually contain `&mut`, even when the closure env also
/// carries unrelated captures.
///
/// This mirrors the real `09_fnonce_resolve` capture shape:
/// - `self.0`: unrelated bool capture
/// - `self.1`: `Box<&mut i32>`
/// - `self.2`: `Box<Box<&mut i32>>`
///
/// The extraction boundary should seed `final_values` for `self.1` and
/// `self.2`, but not for the non-mut-borrow `self.0` capture.
#[test]
fn test_fnonce_closure_nested_box_captures_seed_only_mut_ref_fields() {
    let source = r#"
fn consume_int(_b: Box<&mut i32>) {}
fn consume_double_box(_b: Box<Box<&mut i32>>) {}

pub fn test_nested_capture_fields(c: bool, bx: Box<&mut i32>, by: Box<Box<&mut i32>>) {
    let f = move || {
        let _keep_bool_capture = c;
        consume_int(bx);
        consume_double_box(by);
    };
    f();
}
"#;

    let extracted = extract_from_first_closure_source(source);

    assert!(
        !extracted.final_values.contains_key("self.0"),
        "non-mut-borrow capture self.0 should not be seeded; keys: {:?}",
        extracted.final_values.keys().collect::<Vec<_>>()
    );

    let bx_field = extracted
        .final_values
        .get("self.1")
        .expect("final_values should contain self.1 for Box<&mut i32> capture");
    assert_deref_var(bx_field, "self.1");

    let by_field = extracted
        .final_values
        .get("self.2")
        .expect("final_values should contain self.2 for Box<Box<&mut i32>> capture");
    assert_deref_var(by_field, "self.2");
}

/// Regression test (#2318): `direct_closure_field_seeds` should produce seeds
/// for both fields when a closure captures two Box-wrapped `&mut` references.
/// Each seed should have a distinct `field_idx` (0 and 1).
#[test]
fn test_direct_closure_field_seeds_multiple_box_wrapped_captures() {
    struct ClosureSeedCallbacks {
        result: Option<Vec<type_analysis::ClosureFieldSeed>>,
    }

    impl Callbacks for ClosureSeedCallbacks {
        #[allow(clippy::elidable_lifetime_names)]
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            for owner in tcx.hir_body_owners() {
                let def_id = owner.to_def_id();
                if tcx.def_kind(def_id) != DefKind::Closure {
                    continue;
                }

                let body = tcx.optimized_mir(def_id);
                self.result = Some(type_analysis::direct_closure_field_seeds(
                    tcx,
                    body,
                    CAPTURE_STRUCT_LOCAL,
                ));
                break;
            }
            Compilation::Stop
        }
    }

    let source = r#"
pub fn test_multi_seed(ax: Box<&mut i32>, bx: Box<&mut bool>) {
    let mut c = move || {
        **ax += 5;
        **bx = false;
    };
    c();
}
"#;

    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_mut_borrow_multi_box_seed_{}_{}",
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
        "trust_wp_mut_borrow_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];
    let mut callbacks = ClosureSeedCallbacks { result: None };
    run_compiler(&args, &mut callbacks);
    let _ = fs::remove_dir_all(&temp_dir);

    let seeds = callbacks
        .result
        .expect("callback should collect closure field seeds");
    assert!(
        seeds.len() >= 2,
        "expected at least 2 closure field seeds for two Box<&mut T> captures; got {seeds:?}"
    );
    let field_indices: Vec<u32> = seeds.iter().map(|s| s.field_idx).collect();
    assert!(
        field_indices.contains(&0) && field_indices.contains(&1),
        "seeds should cover field indices 0 and 1; got indices: {field_indices:?}"
    );
}

/// Regression test (#2318): `direct_closure_field_seeds` should produce a seed
/// for `Box<Box<&mut i32>>` (double-wrapped). This verifies the deep search
/// path through `type_eventually_contains_mut_ref` at the seed level.
#[test]
fn test_direct_closure_field_seeds_double_box_wrapped_mut_ref() {
    struct ClosureSeedCallbacks {
        result: Option<Vec<type_analysis::ClosureFieldSeed>>,
    }

    impl Callbacks for ClosureSeedCallbacks {
        #[allow(clippy::elidable_lifetime_names)]
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            for owner in tcx.hir_body_owners() {
                let def_id = owner.to_def_id();
                if tcx.def_kind(def_id) != DefKind::Closure {
                    continue;
                }

                let body = tcx.optimized_mir(def_id);
                self.result = Some(type_analysis::direct_closure_field_seeds(
                    tcx,
                    body,
                    CAPTURE_STRUCT_LOCAL,
                ));
                break;
            }
            Compilation::Stop
        }
    }

    let source = r#"
pub fn test_double_box_seed(bx: Box<Box<&mut i32>>) {
    let mut c = move || {
        ***bx += 7;
    };
    c();
}
"#;

    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_mut_borrow_dblbox_seed_{}_{}",
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
        "trust_wp_mut_borrow_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];
    let mut callbacks = ClosureSeedCallbacks { result: None };
    run_compiler(&args, &mut callbacks);
    let _ = fs::remove_dir_all(&temp_dir);

    let seeds = callbacks
        .result
        .expect("callback should collect closure field seeds");
    assert!(
        !seeds.is_empty(),
        "expected at least one closure field seed for moved `Box<Box<&mut i32>>`; got {seeds:?}"
    );
    assert_eq!(
        seeds[0].field_idx, 0,
        "double-Box capture should be field index 0; got {:?}",
        seeds[0]
    );
}

/// Regression test (#2318): FnOnce closure with conditional mutation through
/// Box<&mut i32> and Box<Box<&mut i32>> captures — mirrors the actual
/// 09_fnonce_resolve.rs pattern. The closure captures:
///   self.0: bool (condition)
///   self.1: Box<&mut i32>
///   self.2: Box<Box<&mut i32>>
/// and mutates through the Box wrappers in both branches.
/// Verifies that both capture fields produce non-identity final values
/// that reflect the conditional mutation.
#[test]
fn test_fnonce_closure_conditional_box_wrapped_captures_produce_mutation_finals() {
    let source = r#"
pub fn test_conditional_capture(c: bool, bx: Box<&mut i32>, by: Box<Box<&mut i32>>) {
    let f = move || {
        if c {
            let bx2 = bx;
            **bx2 += 1;
        } else {
            let by2 = by;
            ***by2 += 1;
        }
    };
    f();
}
"#;

    let maybe = try_extract_from_first_closure_source(source);
    let extracted = maybe
        .expect("conditional Box-wrapped closure extraction should succeed with multi-deref fix");

    // Both self.1 and self.2 should have final values
    assert!(
        extracted.final_values.contains_key("self.1"),
        "self.1 (Box<&mut i32>) should have final value; keys: {:?}",
        extracted.final_values.keys().collect::<Vec<_>>()
    );
    assert!(
        extracted.final_values.contains_key("self.2"),
        "self.2 (Box<Box<&mut i32>>) should have final value; keys: {:?}",
        extracted.final_values.keys().collect::<Vec<_>>()
    );

    // Both should reflect conditional mutation via Ite expressions
    let val1 = &extracted.final_values["self.1"];
    let val2 = &extracted.final_values["self.2"];
    // At least one of the two must be non-identity (reflecting the += 1)
    let is_identity_1 = matches!(val1, PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(n, _) if n == "self.1"));
    let is_identity_2 = matches!(val2, PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(n, _) if n == "self.2"));
    assert!(
        !is_identity_1 || !is_identity_2,
        "at least one capture should reflect mutation; self.1={val1:?}, self.2={val2:?}"
    );
}

/// Regression test (#2318): FnOnce closure with single-branch Box-wrapped
/// mutation (no conditional). Verifies that the extraction pipeline correctly
/// tracks mutation through `**bx2 += 1` where `bx2` is a moved Box<&mut i32>.
#[test]
fn test_fnonce_closure_box_mutation_single_branch_produces_updated_final() {
    let source = r#"
fn consume_box(_b: Box<&mut i32>) {}
pub fn test_single_branch(bx: Box<&mut i32>) {
    let f = move || {
        let bx2 = bx;
        **bx2 += 1;
        consume_box(bx2);
    };
    f();
}
"#;

    let extracted = extract_from_first_closure_source(source);

    assert!(
        !extracted.final_values.is_empty(),
        "FnOnce closure with Box<&mut i32> mutation should produce final_values; keys: {:?}",
        extracted.final_values.keys().collect::<Vec<_>>()
    );

    // self.0 should be the capture field for the Box<&mut i32>
    let field_key = if extracted.final_values.contains_key("self.0") {
        "self.0"
    } else if extracted.final_values.contains_key("self") {
        "self"
    } else {
        panic!(
            "expected self.0 or self final value; keys: {:?}",
            extracted.final_values.keys().collect::<Vec<_>>()
        );
    };

    let final_val = &extracted.final_values[field_key];
    // The final value should NOT be a bare identity Deref — it should
    // reflect the `+= 1` mutation.
    assert!(
        !matches!(final_val, PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == field_key)),
        "final value for {field_key} should reflect mutation (not identity); got: {final_val:?}"
    );

    // Verify the expression structure: should be BinOp(Deref(Var("self.0")), Add, Int(1))
    // representing the `+= 1` mutation.
    match final_val {
        PureExpr::BinOp(left, op, right) => {
            assert_eq!(
                *op,
                trust_wp_core::formula::BinOp::Add,
                "expected Add operation for += 1"
            );
            assert!(
                matches!(right.as_ref(), PureExpr::Int(1)),
                "expected Int(1) as right operand; got: {right:?}"
            );
            assert!(
                matches!(left.as_ref(), PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "self.0")),
                "expected Deref(Var(\"self.0\")) as left operand; got: {left:?}"
            );
        }
        other => panic!("expected BinOp for += 1 mutation; got: {other:?}"),
    }
}

/// Regression test (#2318): FnOnce closure with Box<Box<&mut i32>> capture.
/// Verifies that triple-deref mutation `***by2 += 1` is tracked correctly.
#[test]
fn test_fnonce_closure_nested_box_mutation_produces_updated_final() {
    let source = r#"
fn consume_boxbox(_b: Box<Box<&mut i32>>) {}
pub fn test_nested_box(by: Box<Box<&mut i32>>) {
    let f = move || {
        let by2 = by;
        ***by2 += 1;
        consume_boxbox(by2);
    };
    f();
}
"#;

    let extracted = extract_from_first_closure_source(source);

    assert!(
        extracted.final_values.contains_key("self.0"),
        "self.0 (Box<Box<&mut i32>>) should have final value; keys: {:?}",
        extracted.final_values.keys().collect::<Vec<_>>()
    );

    let final_val = &extracted.final_values["self.0"];
    // Should be BinOp(Deref(Var("self.0")), Add, Int(1)) — same shape
    // as Box<&mut i32> because Box wrappers are transparent.
    assert!(
        !matches!(final_val, PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "self.0")),
        "final value for self.0 should reflect mutation (not identity); got: {final_val:?}"
    );
    match final_val {
        PureExpr::BinOp(left, op, right) => {
            assert_eq!(*op, trust_wp_core::formula::BinOp::Add);
            assert!(matches!(right.as_ref(), PureExpr::Int(1)));
            assert!(
                matches!(left.as_ref(), PureExpr::Deref(inner) if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "self.0")),
                "expected Deref(Var(\"self.0\")) as left operand; got: {left:?}"
            );
        }
        other => panic!("expected BinOp for += 1 mutation; got: {other:?}"),
    }
}

/// #2683: Field write on multi-field struct behind &mut reconstructs whole-struct final.
///
/// When `x.a = 34` on `&mut S { a: i32, b: i32 }`, the whole-struct final
/// value must be `tuple2(34, tuple_get_1(Deref(Var("x"))))` — NOT the identity
/// `Deref(Var("x"))` which leaves the struct-level final disconnected from
/// the field write.
#[test]
fn test_multi_field_struct_field_write_reconstructs_whole_struct_final() {
    let source = r#"
        pub struct Pair { pub a: i32, pub b: i32 }

        pub fn set_a(x: &mut Pair) {
            x.a = 34;
        }
    "#;
    let body = extract_from_source(source, "set_a", &["x"]);
    let x_final = body
        .final_values
        .get("x")
        .expect("x should have a final value");

    // The final value should be a tuple constructor (LogicFnCall), not a bare Deref
    match x_final {
        PureExpr::LogicFnCall { name, args } => {
            assert!(
                name.contains("tuple") && !name.contains("get"),
                "whole-struct final for 'x' should be a tuple constructor, got {name}"
            );
            assert_eq!(
                args.len(),
                2,
                "Pair has 2 fields, reconstructed tuple should have 2 args"
            );
        }
        other => {
            panic!("expected LogicFnCall (tuple constructor) for x_final, got: {other:?}");
        }
    }

    // Field 0 should also be tracked
    let x0_final = body
        .final_values
        .get("x.0")
        .expect("x.0 should have a per-field final value");
    // x.0 should be the written value (Int(34) or similar), not identity
    assert!(
        !matches!(x0_final, PureExpr::Deref(_)),
        "x.0 final should not be identity Deref, got: {x0_final:?}"
    );
}

// ── Nested-reborrow transfer (rusthorn inc_max_3 class) ──────────────

/// Extract with a user spec attached to a named helper function (the
/// transfer callee), mirroring how `parse_and_extract_contract` provides
/// `user_specs` in the real pipeline.
fn extract_with_callee_spec(
    source: &str,
    fn_name: &str,
    arg_names: &[&str],
    callee_name: &str,
    callee_spec: StdSpec,
) -> MutBorrowBody {
    #[allow(clippy::option_option)]
    struct SpecCallbacks {
        fn_name: String,
        arg_names: Vec<String>,
        callee_name: String,
        callee_spec: StdSpec,
        result: Option<Option<MutBorrowBody>>,
        ran: bool,
    }

    impl Callbacks for SpecCallbacks {
        fn config(&mut self, config: &mut Config) {
            install_mir_borrowck_cache(config);
        }

        #[allow(clippy::elidable_lifetime_names)]
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            let callee_suffix = format!("::{}", self.callee_name);
            let mut user_specs = HashMap::new();
            for owner in tcx.hir_body_owners() {
                let def_id = owner.to_def_id();
                let path = tcx.def_path_str(def_id);
                if path == self.callee_name || path.ends_with(&callee_suffix) {
                    user_specs.insert(def_id, self.callee_spec.clone());
                }
            }

            let suffix = format!("::{}", self.fn_name);
            for owner in tcx.hir_body_owners() {
                let def_id = owner.to_def_id();
                let path = tcx.def_path_str(def_id);
                if path != self.fn_name && !path.ends_with(&suffix) {
                    continue;
                }
                let root = tcx.typeck_root_def_id(def_id).expect_local();
                let _ = tcx.mir_borrowck(root);
                let body_with_facts = try_get_body_with_context(owner)
                    .expect("borrowck-backed MIR body should be cached");
                let body = super::super::get_mir_body(body_with_facts);
                self.result = Some(extract_mut_borrow_body(
                    tcx,
                    body,
                    Some(body_with_facts),
                    &self.arg_names,
                    &user_specs,
                    &HashMap::new(),
                    &HashMap::new(),
                ));
                self.ran = true;
                break;
            }
            Compilation::Stop
        }
    }

    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_nested_transfer_{}_{}",
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
        "trust_wp_nested_transfer_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = SpecCallbacks {
        fn_name: fn_name.to_string(),
        arg_names: arg_names.iter().map(|name| (*name).to_string()).collect(),
        callee_name: callee_name.to_string(),
        callee_spec,
        result: None,
        ran: false,
    };
    clear_caches();
    run_compiler(&args, &mut callbacks);
    clear_caches();

    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(callbacks.ran, "failed to locate function `{fn_name}`");
    callbacks
        .result
        .expect("callback should capture extraction result")
        .expect("mut borrow extraction should succeed")
}

const INC_MAX_3_SOURCE: &str = r#"
pub fn swap<'a, 'b>(mma: &'a mut &'b mut u32, mmb: &'a mut &'b mut u32) {
    std::mem::swap(mma, mmb);
}

pub fn inc_max_3<'a>(mut ma: &'a mut u32, mut mb: &'a mut u32, mut mc: &'a mut u32) {
    if *ma < *mb {
        swap(&mut ma, &mut mb);
    }
    if *mb < *mc {
        swap(&mut mb, &mut mc);
    }
    if *ma < *mb {
        swap(&mut ma, &mut mb);
    }
    *ma += 2;
    *mb += 1;
}
"#;

fn swap_spec() -> StdSpec {
    StdSpec {
        requires: vec![],
        ensures: vec!["^mma == *mmb && ^mmb == *mma".to_string()],
        param_names: None,
    }
}

/// The inc_max_3 body with a swap transfer spec produces per-slot expiry
/// resolutions and suppresses the (wrong-for-rebound-slots) identity
/// `final_values` entries for the transferred params.
#[test]
fn test_nested_transfer_emits_slot_resolutions_for_inc_max_3() {
    let body = extract_with_callee_spec(
        INC_MAX_3_SOURCE,
        "inc_max_3",
        &["ma", "mb", "mc"],
        "swap",
        swap_spec(),
    );

    assert_eq!(
        body.nested_transfer_params,
        ["ma", "mb", "mc"]
            .iter()
            .map(|s| (*s).to_string())
            .collect::<std::collections::HashSet<_>>(),
        "all three slots participate in transfers"
    );
    assert!(
        body.nested_slot_resolutions.len() >= 3,
        "at least one expiry resolution per slot; got {:?}",
        body.nested_slot_resolutions
    );
    for name in ["ma", "mb", "mc"] {
        assert!(
            !body.final_values.contains_key(name),
            "identity final_values entry for `{name}` must be removed"
        );
        assert!(
            body.mutation_continued_params.contains(name),
            "`{name}` must suppress identity resolve emission"
        );
    }

    // Each resolution is (a guarded implication whose consequent is)
    // `Final(<content>) == <value>` with the content an expression over the
    // ENTRY borrows (Var of an entry borrow, or an Ite tree of them).
    fn content_is_entry_borrow_tree(expr: &PureExpr) -> bool {
        match expr {
            PureExpr::Var(name, _) => ["ma", "mb", "mc"].contains(&name.as_str()),
            PureExpr::Ite(_, t, e) => {
                content_is_entry_borrow_tree(t) && content_is_entry_borrow_tree(e)
            }
            _ => false,
        }
    }
    for resolution in &body.nested_slot_resolutions {
        let eq = match resolution {
            PureExpr::BinOp(_, trust_wp_core::formula::BinOp::Implies, consequent) => {
                consequent.as_ref()
            }
            other => other,
        };
        let PureExpr::BinOp(lhs, trust_wp_core::formula::BinOp::Eq, _rhs) = eq else {
            panic!("resolution should be a (guarded) equality: {resolution:?}");
        };
        let PureExpr::Final(content) = lhs.as_ref() else {
            panic!("resolution LHS should be Final(<content>): {resolution:?}");
        };
        assert!(
            content_is_entry_borrow_tree(content),
            "content should be an entry-borrow expression: {content:?}"
        );
    }
}

/// A call forwarding a nested slot borrow to an UNRECOGNIZED callee poisons
/// the feature: suppressions stay (fail-closed) but no resolutions are
/// emitted.
#[test]
fn test_nested_transfer_poisoned_by_unrecognized_callee() {
    let source = r#"
pub fn swap<'a, 'b>(mma: &'a mut &'b mut u32, mmb: &'a mut &'b mut u32) {
    std::mem::swap(mma, mmb);
}

pub fn rebind(mm: &mut &mut u32) {
    let _ = mm;
}

pub fn two_calls<'a>(mut ma: &'a mut u32, mut mb: &'a mut u32) {
    swap(&mut ma, &mut mb);
    rebind(&mut ma);
    *ma += 1;
}
"#;
    let body = extract_with_callee_spec(source, "two_calls", &["ma", "mb"], "swap", swap_spec());
    assert!(
        body.nested_slot_resolutions.is_empty(),
        "unrecognized rebind call must poison slot resolutions; got {:?}",
        body.nested_slot_resolutions
    );
    // The transferred slots stay suppressed (fail-closed).
    assert!(!body.final_values.contains_key("ma"));
    assert!(body.mutation_continued_params.contains("ma"));
}

/// Without a transfer-shaped callee spec nothing changes: no resolutions,
/// no suppression beyond the legacy mutation-continuation behavior.
#[test]
fn test_nested_transfer_not_triggered_without_transfer_spec() {
    let body = extract_with_callee_spec(
        INC_MAX_3_SOURCE,
        "inc_max_3",
        &["ma", "mb", "mc"],
        "swap",
        StdSpec {
            requires: vec![],
            // Value-level contract — NOT a whole-borrow transfer.
            ensures: vec!["(^mma)@ == (*mmb)@ && (^mmb)@ == (*mma)@".to_string()],
            param_names: None,
        },
    );
    assert!(body.nested_slot_resolutions.is_empty());
    assert!(body.nested_transfer_params.is_empty());
}
