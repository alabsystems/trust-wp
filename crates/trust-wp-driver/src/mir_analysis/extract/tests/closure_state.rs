// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    collections::HashMap,
    fs,
    sync::{
        atomic::{AtomicU64, Ordering},
        Arc,
    },
};

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_interface::interface::Compiler;
use rustc_middle::{mir::Local, ty::TyCtxt};
use trust_wp_core::formula::ExprSort;

use super::*;
use crate::mir_analysis::effects::CallEffects;

static CLOSURE_STATE_TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

struct WrappedReceiverPropagationCallbacks {
    receiver_expr: PureExpr,
    propagated_x: Option<PureExpr>,
    ran: bool,
}

struct EmptyMutRefPositionCallbacks {
    marked_mutating: Option<bool>,
}

impl Callbacks for WrappedReceiverPropagationCallbacks {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        for local_def_id in tcx.hir_body_owners() {
            let def_path = tcx.def_path_str(local_def_id);
            if def_path != "caller" && !def_path.ends_with("::caller") {
                continue;
            }

            let body = tcx.optimized_mir(local_def_id.to_def_id());
            let arg_names = resolve_arg_names_or_warn(tcx, local_def_id.to_def_id(), None);
            let x_local = body
                .local_decls
                .indices()
                .find(|local| {
                    source_name_for_local(body, *local, &arg_names).as_deref() == Some("x")
                })
                .expect("source local for `x` not found");
            let c_local = body
                .local_decls
                .indices()
                .find(|local| {
                    source_name_for_local(body, *local, &arg_names).as_deref() == Some("c")
                })
                .expect("source local for `c` not found");

            let x_expr = PureExpr::Var("x".to_string(), Some(ExprSort::Int));
            let closure_env = PureExpr::LogicFnCall {
                name: "__trust_wp_tuple1".to_string(),
                args: vec![x_expr.clone()],
            };
            let mut local_exprs = HashMap::from([(x_local, x_expr), (c_local, closure_env)]);

            propagate_mutating_receiver_state_with_captures(
                &mut local_exprs,
                body,
                &arg_names,
                &self.receiver_expr,
                None,
            );

            self.propagated_x = local_exprs.get(&x_local).cloned();
            self.ran = true;
            return Compilation::Stop;
        }

        Compilation::Stop
    }
}

impl Callbacks for EmptyMutRefPositionCallbacks {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        for local_def_id in tcx.hir_body_owners() {
            let def_path = tcx.def_path_str(local_def_id);
            if def_path != "caller" && !def_path.ends_with("::caller") {
                continue;
            }

            let body = tcx.optimized_mir(local_def_id.to_def_id());
            let arg_names = resolve_arg_names_or_warn(tcx, local_def_id.to_def_id(), None);
            let mut local_exprs = HashMap::new();
            let args = Vec::new();
            let mut effects = CallEffects::new();

            propagate_mutating_ref_arg_states_for_positions(
                &mut local_exprs,
                body,
                &arg_names,
                &args,
                &[],
                Some(&mut effects),
                None,
            );

            self.marked_mutating = Some(effects.has_mutating_call_effect);
            return Compilation::Stop;
        }

        Compilation::Stop
    }
}

fn propagate_wrapped_closure_receiver_in_source(receiver_expr: PureExpr) -> PureExpr {
    let source = r#"
pub fn caller(mut x: i32) -> i32 {
    let mut c = || {
        x += 1;
    };
    c();
    x
}
"#;
    let unique = CLOSURE_STATE_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_closure_state_wrapped_receiver_{}_{}",
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
        "trust_wp_closure_state_wrapped_receiver_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = WrappedReceiverPropagationCallbacks {
        receiver_expr,
        propagated_x: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to run wrapped receiver propagation test"
    );
    callbacks
        .propagated_x
        .expect("propagated x expression should be captured")
}

#[test]
fn empty_mut_ref_positions_do_not_mark_call_mutating() {
    let source = r#"
pub fn caller(x: i32) -> i32 {
    x + 1
}
"#;
    let unique = CLOSURE_STATE_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_closure_state_empty_mut_ref_positions_{}_{}",
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
        "trust_wp_closure_state_empty_mut_ref_positions_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = EmptyMutRefPositionCallbacks {
        marked_mutating: None,
    };
    run_compiler(&args, &mut callbacks);
    let _ = fs::remove_dir_all(&temp_dir);

    assert_eq!(
        callbacks.marked_mutating,
        Some(false),
        "empty mut-ref position metadata should not mark a predicate-only mut-ref spec as mutating"
    );
}

#[test]
fn final_receiver_state_expr_nests_existing_final_capture() {
    let expr = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple1".to_string(),
        args: vec![PureExpr::Final(Arc::new(PureExpr::Var(
            "x".to_string(),
            None,
        )))],
    };

    let advanced = final_receiver_state_expr(&expr);
    assert_eq!(
        advanced,
        PureExpr::LogicFnCall {
            name: "__trust_wp_tuple1".to_string(),
            args: vec![PureExpr::Final(Arc::new(PureExpr::Final(Arc::new(
                PureExpr::Var("x".to_string(), None),
            ))))],
        }
    );
}

#[test]
fn final_receiver_state_expr_nests_existing_final_non_tuple_receiver() {
    let expr = PureExpr::Final(Arc::new(PureExpr::Var("f".to_string(), None)));

    let advanced = final_receiver_state_expr(&expr);
    assert_eq!(
        advanced,
        PureExpr::Final(Arc::new(PureExpr::Final(Arc::new(PureExpr::Var(
            "f".to_string(),
            None,
        )))))
    );
}

#[test]
fn closure_capture_bindings_extracts_tuple_capture_vars() {
    let self_expr = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple2".to_string(),
        args: vec![
            PureExpr::Var("x".to_string(), None),
            PureExpr::Var("y".to_string(), None),
        ],
    };

    let bindings = closure_capture_bindings(&self_expr);
    assert_eq!(bindings, vec![(0, "x".to_string()), (1, "y".to_string())]);
}

#[test]
fn closure_capture_bindings_handles_wrapped_receiver_expr() {
    let tuple_env = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple1".to_string(),
        args: vec![PureExpr::Var("x".to_string(), None)],
    };
    let wrapped = PureExpr::Deref(Arc::new(PureExpr::Final(Arc::new(tuple_env))));

    let bindings = closure_capture_bindings(&wrapped);
    assert_eq!(bindings, vec![(0, "x".to_string())]);
}

#[test]
fn project_capture_field_returns_tuple_argument_when_available() {
    let post_state = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple2".to_string(),
        args: vec![
            PureExpr::Final(Arc::new(PureExpr::Var("x".to_string(), None))),
            PureExpr::Int(7),
        ],
    };

    assert_eq!(
        project_capture_field(&post_state, 0),
        PureExpr::Final(Arc::new(PureExpr::Var("x".to_string(), None)))
    );
    assert_eq!(project_capture_field(&post_state, 1), PureExpr::Int(7));
}

#[test]
fn project_capture_field_normalizes_tracked_capture_pre_state() {
    let state = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple1".to_string(),
        args: vec![PureExpr::Var("self.0".to_string(), None)],
    };

    assert_eq!(
        project_capture_field(&state, 0),
        PureExpr::Deref(Arc::new(PureExpr::Var("self.0".to_string(), None)))
    );
}

#[test]
fn project_capture_field_normalizes_tracked_capture_post_state() {
    let post_state = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple1".to_string(),
        args: vec![PureExpr::Final(Arc::new(PureExpr::Var(
            "self.0".to_string(),
            None,
        )))],
    };

    assert_eq!(
        project_capture_field(&post_state, 0),
        PureExpr::Final(Arc::new(PureExpr::Deref(Arc::new(PureExpr::Var(
            "self.0".to_string(),
            None,
        )))))
    );
}

#[test]
fn project_capture_field_falls_back_to_tuple_projection_for_non_tuple_state() {
    let post_state = PureExpr::Final(Arc::new(PureExpr::Var("self".to_string(), None)));
    assert_eq!(
        project_capture_field(&post_state, 0),
        PureExpr::LogicFnCall {
            name: tuple_field_logic_fn_name(0),
            args: vec![post_state],
        }
    );
}

#[test]
fn propagate_mutating_receiver_state_preserves_existing_final_depth_for_named_var() {
    let mut local_exprs = HashMap::from([(
        Local::from_u32(1),
        PureExpr::Final(Arc::new(PureExpr::Var("own".to_string(), None))),
    )]);

    propagate_mutating_receiver_state(&mut local_exprs, &PureExpr::Var("own".to_string(), None));

    assert_eq!(
        local_exprs.get(&Local::from_u32(1)),
        Some(&PureExpr::Final(Arc::new(PureExpr::Final(Arc::new(
            PureExpr::Var("own".to_string(), None),
        ))))),
    );
}

#[test]
fn propagate_mutating_receiver_state_with_captures_resolves_deref_final_named_receiver() {
    let propagated_x = propagate_wrapped_closure_receiver_in_source(PureExpr::Deref(Arc::new(
        PureExpr::Final(Arc::new(PureExpr::Var("c".to_string(), None))),
    )));

    assert_eq!(
        propagated_x,
        PureExpr::Final(Arc::new(PureExpr::Var(
            "x".to_string(),
            Some(ExprSort::Int),
        ))),
        "wrapped closure receiver should resolve back to `c` before capture propagation"
    );
}

#[test]
fn propagate_mutating_receiver_state_with_captures_resolves_final_deref_named_receiver() {
    let propagated_x = propagate_wrapped_closure_receiver_in_source(PureExpr::Final(Arc::new(
        PureExpr::Deref(Arc::new(PureExpr::Var("c".to_string(), None))),
    )));

    assert_eq!(
        propagated_x,
        PureExpr::Final(Arc::new(PureExpr::Var(
            "x".to_string(),
            Some(ExprSort::Int),
        ))),
        "receiver-state wrappers around a closure name should not hide its captured vars"
    );
}

#[test]
fn substitute_capture_fields_in_postcondition_simplifies_tuple_capture_projection() {
    let self_expr = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple1".to_string(),
        args: vec![PureExpr::Var("x".to_string(), None)],
    };
    let expr = PureExpr::Var("x".to_string(), None);
    let substituted = substitute_capture_fields_in_postcondition(
        &expr,
        &[(0, "x".to_string())],
        &self_expr,
        false,
    );
    assert_eq!(
        substituted,
        PureExpr::Final(Arc::new(PureExpr::Var("x".to_string(), None)))
    );
}

#[test]
fn substitute_capture_fields_in_postcondition_old_uses_pre_state_capture() {
    let self_expr = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple1".to_string(),
        args: vec![PureExpr::Var("x".to_string(), None)],
    };
    let expr = PureExpr::Old(Arc::new(PureExpr::Var("x".to_string(), None)));
    let substituted = substitute_capture_fields_in_postcondition(
        &expr,
        &[(0, "x".to_string())],
        &self_expr,
        false,
    );
    assert_eq!(substituted, PureExpr::Var("x".to_string(), None));
}

#[test]
fn substitute_capture_fields_in_postcondition_normalizes_tracked_capture_post_state() {
    let self_expr = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple1".to_string(),
        args: vec![PureExpr::Var("self.0".to_string(), None)],
    };
    let expr = PureExpr::View(Arc::new(PureExpr::Var("p".to_string(), None)));
    let substituted = substitute_capture_fields_in_postcondition(
        &expr,
        &[(0, "p".to_string())],
        &self_expr,
        false,
    );
    assert_eq!(
        substituted,
        PureExpr::View(Arc::new(PureExpr::Final(Arc::new(PureExpr::Deref(
            Arc::new(PureExpr::Var("self.0".to_string(), None)),
        )))))
    );
}

#[test]
fn substitute_capture_fields_in_postcondition_normalizes_tracked_capture_old_state() {
    let self_expr = PureExpr::LogicFnCall {
        name: "__trust_wp_tuple1".to_string(),
        args: vec![PureExpr::Var("self.0".to_string(), None)],
    };
    let expr = PureExpr::Old(Arc::new(PureExpr::Var("p".to_string(), None)));
    let substituted = substitute_capture_fields_in_postcondition(
        &expr,
        &[(0, "p".to_string())],
        &self_expr,
        false,
    );
    assert_eq!(
        substituted,
        PureExpr::Deref(Arc::new(PureExpr::Var("self.0".to_string(), None)))
    );
}

#[test]
fn spec_mutates_closure_state_detects_postcondition_markers() {
    let mutating = StdSpec {
        requires: vec![],
        ensures: vec!["exists<st, r> f.postcondition_mut((), st, r)".to_string()],
        param_names: None,
    };
    assert!(
        spec_mutates_closure_state(&mutating),
        "postcondition_mut in ensures should mark call as mutating"
    );

    let once = StdSpec {
        requires: vec![],
        ensures: vec!["f.postcondition_once((), result)".to_string()],
        param_names: None,
    };
    assert!(
        spec_mutates_closure_state(&once),
        "postcondition_once in ensures should mark call as mutating"
    );

    let non_mutating = StdSpec {
        requires: vec![],
        ensures: vec!["result == x + 1".to_string()],
        param_names: None,
    };
    assert!(
        !spec_mutates_closure_state(&non_mutating),
        "plain result-equality spec should not be treated as mutating"
    );
}

#[test]
fn spec_mentions_post_state_for_aliases_ignores_predicate_only_mut_ref_spec() {
    let spec = StdSpec {
        requires: vec![],
        ensures: vec!["arg0 != arg1".to_string()],
        param_names: None,
    };
    let aliases = vec!["arg0".to_string(), "self".to_string()];
    assert!(
        !spec_mentions_post_state_for_aliases(&spec, &aliases),
        "predicate-only ensures should not force a post-state advance"
    );
}

#[test]
fn spec_mentions_post_state_for_aliases_detects_final_receiver() {
    let spec = StdSpec {
        requires: vec![],
        ensures: vec!["(^self)@ == self@.push_back(value)".to_string()],
        param_names: Some(vec!["self".to_string(), "value".to_string()]),
    };
    let aliases = vec!["arg0".to_string(), "self".to_string()];
    assert!(
        spec_mentions_post_state_for_aliases(&spec, &aliases),
        "final receiver references should advance the mut ref receiver"
    );
}

#[test]
fn spec_mentions_post_state_for_aliases_detects_old_deref_param() {
    let spec = StdSpec {
        requires: vec![],
        ensures: vec!["result == old(*dest)".to_string()],
        param_names: Some(vec!["dest".to_string(), "src".to_string()]),
    };
    let aliases = vec!["arg0".to_string(), "dest".to_string()];
    assert!(
        spec_mentions_post_state_for_aliases(&spec, &aliases),
        "old(*dest) should conservatively mark dest as post-state-sensitive"
    );
}

#[test]
fn spec_mentions_post_state_for_aliases_detects_closure_mutation_markers() {
    let spec = StdSpec {
        requires: vec![],
        ensures: vec!["(*self).postcondition_mut(arg, ^self, result)".to_string()],
        param_names: Some(vec!["self".to_string(), "arg".to_string()]),
    };
    let aliases = vec!["arg0".to_string(), "self".to_string()];
    assert!(
        spec_mentions_post_state_for_aliases(&spec, &aliases),
        "closure postcondition_mut markers should advance the receiver"
    );
}

#[test]
fn closure_capture_name_from_projected_var_maps_self_fields() {
    let capture_names = vec!["x".to_string(), "y".to_string()];
    assert_eq!(
        closure_capture_name_from_projected_var("self.0", Some(capture_names.as_slice())),
        Some("x".to_string())
    );
    assert_eq!(
        closure_capture_name_from_projected_var("self.1", Some(capture_names.as_slice())),
        Some("y".to_string())
    );
}

#[test]
fn closure_capture_name_from_projected_var_rejects_invalid_context() {
    assert_eq!(
        closure_capture_name_from_projected_var("self.0", None),
        None
    );
    assert_eq!(
        closure_capture_name_from_projected_var("self.foo", Some(&["x".to_string()])),
        None
    );
    assert_eq!(
        closure_capture_name_from_projected_var("other.0", Some(&["x".to_string()])),
        None
    );
}

#[test]
fn record_name_update_with_capture_alias_records_capture_name_for_self_field() {
    let mut updates = HashMap::new();
    let expr = PureExpr::Int(2);
    let capture_names = vec!["x".to_string()];

    record_name_update_with_capture_alias(
        &mut updates,
        "self.0",
        &expr,
        Some(capture_names.as_slice()),
    );

    assert_eq!(updates.get("x"), Some(&expr));
    assert_eq!(updates.get("self.0"), Some(&expr));
}
