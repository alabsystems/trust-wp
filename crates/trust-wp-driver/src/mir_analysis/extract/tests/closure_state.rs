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
        capture_inv_requires: Vec::new(),
        inv_requires: Vec::new(),
        requires: vec![],
        ensures: vec!["exists<st, r> f.postcondition_mut((), st, r)".to_string()],
        param_names: None,
    };
    assert!(
        spec_mutates_closure_state(&mutating),
        "postcondition_mut in ensures should mark call as mutating"
    );

    let once = StdSpec {
        capture_inv_requires: Vec::new(),
        inv_requires: Vec::new(),
        requires: vec![],
        ensures: vec!["f.postcondition_once((), result)".to_string()],
        param_names: None,
    };
    assert!(
        spec_mutates_closure_state(&once),
        "postcondition_once in ensures should mark call as mutating"
    );

    let non_mutating = StdSpec {
        capture_inv_requires: Vec::new(),
        inv_requires: Vec::new(),
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
        capture_inv_requires: Vec::new(),
        inv_requires: Vec::new(),
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
        capture_inv_requires: Vec::new(),
        inv_requires: Vec::new(),
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
        capture_inv_requires: Vec::new(),
        inv_requires: Vec::new(),
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
        capture_inv_requires: Vec::new(),
        inv_requires: Vec::new(),
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

/// `Ghost::deref_mut`'s `result == self`: the call hands the argument borrow
/// onward as the result, so its argument is NOT advanced to an unconstrained
/// post-state. (s48)
#[test]
fn spec_result_carries_arg_reference_detects_whole_reference_identity() {
    let spec = StdSpec {
        capture_inv_requires: Vec::new(),
        inv_requires: Vec::new(),
        requires: vec![],
        ensures: vec!["result == self".to_string()],
        param_names: Some(vec!["self".to_string()]),
    };
    let aliases = spec_clause_aliases_for_arg_index(Some(&["self".to_string()]), 1, 0);
    assert!(
        spec_result_carries_arg_reference(&spec, &aliases),
        "`result == self` hands the argument reference back as the result"
    );
}

/// `Box::new`'s `*result == value`: the returned container holds the argument
/// reference itself, prophecy included. The clause names the symbolic `value`
/// alias, which is bound to the first non-self argument. (s48)
#[test]
fn spec_result_carries_arg_reference_detects_value_alias_through_result_deref() {
    let spec = StdSpec {
        capture_inv_requires: Vec::new(),
        inv_requires: Vec::new(),
        requires: vec![],
        ensures: vec!["*result == value".to_string()],
        param_names: None,
    };
    let aliases = spec_clause_aliases_for_arg_index(None, 1, 0);
    assert!(
        spec_result_carries_arg_reference(&spec, &aliases),
        "`*result == value` puts the argument reference inside the result"
    );
}

/// A POINTEE-level equality pins the entry value of the pointee and says
/// nothing about `^p`: the argument must still be advanced. (s48 soundness)
#[test]
fn spec_result_carries_arg_reference_rejects_pointee_level_equality() {
    let spec = StdSpec {
        capture_inv_requires: Vec::new(),
        inv_requires: Vec::new(),
        requires: vec![],
        ensures: vec!["*result == *self".to_string()],
        param_names: Some(vec!["self".to_string()]),
    };
    let aliases = spec_clause_aliases_for_arg_index(Some(&["self".to_string()]), 1, 0);
    assert!(
        !spec_result_carries_arg_reference(&spec, &aliases),
        "`*result == *self` constrains no prophecy and must not stop the advance"
    );
}

/// `ensures(true)`, a predicate-only lemma and an entry-value clause all leave
/// `^p` unconstrained: the argument is advanced. (s48 soundness)
#[test]
fn spec_result_carries_arg_reference_rejects_contracts_silent_on_the_result() {
    let aliases = spec_clause_aliases_for_arg_index(Some(&["v".to_string()]), 1, 0);
    for ensures in [
        "true",
        "arg0 != arg1",
        "result@ == (*v)@.len()",
        "(^v)@ == (*v)@",
    ] {
        let spec = StdSpec {
            capture_inv_requires: Vec::new(),
            inv_requires: Vec::new(),
            requires: vec![],
            ensures: vec![ensures.to_string()],
            param_names: Some(vec!["v".to_string()]),
        };
        assert!(
            !spec_result_carries_arg_reference(&spec, &aliases),
            "`{ensures}` does not hand the argument back as the result"
        );
    }
}

/// The borrow-forwarding exception is keyed on the FULL def path, so a bare
/// item name a hundred other std items also carry cannot reach it. (s48
/// soundness — the review's S4)
///
/// The std constructor tier is EMPTY since the s48 v4 audit: `Box::new` was a
/// reproduced exit-0 false accept (`~/wpcamp/s48/probes4/p1_box_deref_out.rs`,
/// `p2_box_vec_push.rs`), and `Rc::new`/`Arc::new` hand the same reborrow back
/// through `get_mut`. This test pins that NONE of those spellings matches.
#[test]
fn path_forwards_mut_borrow_matches_only_the_listed_std_paths() {
    for path in [
        // Deleted by the s48 v4 audit: a `&mut` moved into a container is
        // handed straight back (`*b`, `**b`, `Rc::get_mut`), so the
        // suppression drops the caller's write through it.
        "std::boxed::Box::new",
        "std::rc::Rc::new",
        "std::sync::Arc::new",
        // Same item NAME, different item: these write through / consume their
        // receiver and must keep advancing it.
        "std::cell::RefCell::borrow_mut",
        "std::sync::Mutex::into_inner",
        "core::ops::DerefMut::deref_mut",
        "std::vec::Vec::new",
        "std::collections::HashMap::new",
        // A path that is spelled right but is not a std item.
        "alloc::boxed::Box::new::extra",
        // Deleted by the s48 v3 audit: these spellings matched NOTHING in the
        // should_succeed, should_fail or adversarial corpora, so they are
        // accept paths with no evidence behind them.
        "alloc::boxed::Box::new",
        "alloc::rc::Rc::new",
        "alloc::sync::Arc::new",
    ] {
        assert!(
            !path_forwards_mut_borrow(path, true, false, false),
            "{path} must not reach the borrow-forwarding exception"
        );
    }
}

/// The ghost identities were matched as a suffix (three crates re-export
/// them). That tier is EMPTY since the s48 v4 audit: in the encoding
/// `Ghost<T>` IS `T`, so `Ghost::new(&mut x)` stores the reborrow and
/// `into_inner` hands it back — reproduced as an exit-0 false accept at
/// `~/wpcamp/s48/probes4/p6b_ghost_new_program_ref.rs`. This test pins that no
/// ghost spelling matches, with or without spec-library provenance. (s48)
#[test]
fn path_forwards_mut_borrow_scopes_the_ghost_identities_to_the_spec_library() {
    for path in [
        // Deleted by the s48 v4 audit (the by-value ghost identities: the
        // payload comes back out, and when the payload is a `&mut` so does the
        // reborrow).
        "creusot_contracts::Ghost::new",
        "trust_wp_std::ghost::Ghost::into_inner",
        "trust_wp_std::ghost::Snapshot::capture",
        "creusot_std::ghost::Snapshot::into_inner",
        // A local or third-party item that merely spells the path.
        "my_crate::ghost::Ghost::deref_mut",
        // Spec-library items that were never the ghost identities.
        "trust_wp_std::vec::Vec::deref_mut",
        "trust_wp_std::cell::PermCell::borrow_mut",
        "trust_wp_std::ghost::GhostBox::deref_mut",
        // Deleted by the s48 v3 audit. The four `*_mut` ghost identities each
        // returned a live `&mut` reborrow of the receiver and were measured
        // exit-0 false accepts; the shared-ref ones matched no corpus test.
        "trust_wp_std::ghost::Ghost::inner_mut",
        "trust_wp_std::ghost::Ghost::borrow_mut",
        "trust_wp_std::ghost::Ghost::deref_mut",
        "creusot_std::ghost::Ghost::borrow_mut",
        "trust_wp_std::ghost::Ghost::inner",
        "trust_wp_std::ghost::Ghost::deref",
        "trust_wp_std::ghost::Ghost::borrow",
        "trust_wp_std::ghost::Snapshot::inner",
        "trust_wp_std::ghost::Snapshot::deref",
    ] {
        assert!(
            !path_forwards_mut_borrow(path, false, true, false),
            "{path} must not reach the borrow-forwarding exception"
        );
        assert!(
            !path_forwards_mut_borrow(path, true, false, false),
            "{path} must not match under std provenance either"
        );
    }
}

/// A projection TRAIT method (`std::ops::DerefMut::deref_mut`) carries `core`'s
/// provenance whatever type it runs on. `<Ghost<T> as DerefMut>::deref_mut`
/// hands `&mut self.0` back, and a write through that borrow does not reach
/// the receiver, so the entry that once admitted it for a ghost receiver was a
/// known false accept and is gone: no receiver brings it back. (s48 soundness)
#[test]
fn path_forwards_mut_borrow_requires_a_ghost_receiver_for_projection_traits() {
    for ghost_receiver in [true, false] {
        assert!(
            !path_forwards_mut_borrow("std::ops::DerefMut::deref_mut", true, false, ghost_receiver),
            "`DerefMut::deref_mut` hands a live `&mut` reborrow of its receiver back: \
             it can never suppress the receiver's advance (ghost_receiver={ghost_receiver})"
        );
    }
    // `Deref::deref` is the ONE entry the corrected criterion does not
    // condemn (its result is a `&T`), and it is deleted anyway: its receiver
    // is `&Self`, so it can never occupy a `&mut` argument position, and the
    // instrumented run measured it suppressing nothing in 1033 cases.
    for ghost_receiver in [true, false] {
        assert!(
            !path_forwards_mut_borrow("std::ops::Deref::deref", true, false, ghost_receiver),
            "`Deref::deref` was deleted by the s48 v4 audit as unmeasured"
        );
    }
    // A ghost receiver is not a licence for an arbitrary std method.
    for path in ["std::vec::Vec::push", "core::option::Option::insert"] {
        assert!(
            !path_forwards_mut_borrow(path, true, false, true),
            "{path} is not a projection and must keep advancing the argument"
        );
    }
    // Deleted by the s48 v3 audit: spellings that matched nothing in any
    // corpus, and both `Borrow`/`BorrowMut` projections. A ghost receiver does
    // not bring them back.
    for path in [
        "core::ops::Deref::deref",
        "core::ops::deref::Deref::deref",
        "core::ops::DerefMut::deref_mut",
        "core::ops::deref::DerefMut::deref_mut",
        "core::borrow::Borrow::borrow",
        "std::borrow::Borrow::borrow",
        "core::borrow::BorrowMut::borrow_mut",
        "std::borrow::BorrowMut::borrow_mut",
    ] {
        assert!(
            !path_forwards_mut_borrow(path, true, false, true),
            "{path} was deleted by the s48 v3 allowlist audit and must not match"
        );
    }
}

/// THE soundness criterion for the borrow-forwarding allowlist, pinned
/// structurally: an item may suppress a `&mut` argument's advance only if NO
/// live `&mut` reborrow of that argument is reachable from the call's RESULT.
///
/// The v3 version of this test keyed on the `_mut` suffix, which is the naming
/// convention and not the criterion — it could not flag `Box::new`, which the
/// s48 v4 review turned into two exit-0 false accepts (`*b` and `(**b).push`).
/// The criterion is not decidable from a path string, so this test pins the
/// only configuration that has been AUDITED against it: all four tiers are
/// EMPTY, the known-unsound one included.
///
/// Adding an entry to a sound tier therefore takes a deliberate edit of this
/// test, and what that edit must be accompanied by is: a probe per HANDBACK
/// SHAPE showing the item cannot give a writable borrow back — `*b`, `**b`,
/// `into_inner`, `get_mut`, a field read, an iterator item, not merely the
/// direct `**b = v` assignment, which is the one shape the encoder already
/// catches. The probe set lives in `~/wpcamp/s48/probes4/`. Adding an entry to
/// the QUARANTINE additionally takes a measured price and a `docs/soundness.md`
/// K1 update. (s48 v4 soundness)
#[test]
fn forwarding_allowlist_carries_no_argument_handback_outside_quarantine() {
    assert!(
        FORWARDING_STD_CALLEES.is_empty(),
        "a std constructor hands its argument back out of the container it \
         moved it into (`*b`, `**b`, `Rc::get_mut`), so suppressing the \
         argument's advance drops the caller's write through it: \
         {FORWARDING_STD_CALLEES:?}"
    );
    assert!(
        FORWARDING_SPEC_LIBRARY_SUFFIXES.is_empty(),
        "the ghost identities hand their payload back by value, so a captured \
         `&mut` comes back writable: {FORWARDING_SPEC_LIBRARY_SUFFIXES:?}"
    );
    assert!(
        FORWARDING_SHARED_PROJECTION_TRAIT_PATHS.is_empty(),
        "no shared-projection entry has been shown to suppress anything in any \
         corpus: {FORWARDING_SHARED_PROJECTION_TRAIT_PATHS:?}"
    );

    assert!(
        MUT_REBORROW_PROJECTION_PATHS_KNOWN_UNSOUND.is_empty(),
        "an entry admitted against the criterion is a KNOWN false accept: \
         `<Ghost<T> as DerefMut>::deref_mut` hands `&mut self.0` back and the \
         caller's write through it never reached the receiver; docs/GOAL.md \
         section 3 forbids buying coverage that way: \
         {MUT_REBORROW_PROJECTION_PATHS_KNOWN_UNSOUND:?}"
    );
}

/// The handback shapes this rule must never credit, pinned as paths so a
/// future entry that spells one of them fails here. Each name below is an
/// item that, given a container holding a `&mut`, hands a writable borrow of
/// it back to the caller — which is exactly what the criterion forbids.
/// (s48 v4 soundness)
#[test]
fn forwarding_allowlist_rejects_every_known_handback_spelling() {
    for path in [
        // `*b` / `**b` on a `Box<&mut T>`.
        "std::boxed::Box::new",
        "std::ops::Deref::deref",
        // `Rc::get_mut` / `Arc::get_mut` give back a `&mut &mut T`.
        "std::rc::Rc::new",
        "std::rc::Rc::get_mut",
        "std::sync::Arc::new",
        "std::sync::Arc::get_mut",
        // Unwrapping a container hands the payload back by value.
        "std::boxed::Box::into_inner",
        "std::cell::RefCell::into_inner",
        "trust_wp_std::ghost::Ghost::new",
        "trust_wp_std::ghost::Ghost::into_inner",
        "trust_wp_std::ghost::Snapshot::capture",
        "trust_wp_std::ghost::Snapshot::into_inner",
        // A `&mut` handed back through a projection or an iterator item.
        "std::vec::Vec::as_mut_slice",
        "std::vec::Vec::iter_mut",
        "std::option::Option::as_mut",
        "std::slice::SliceIndex::get_mut",
    ] {
        for (is_std, is_spec_library, ghost_receiver) in [
            (true, false, false),
            (true, false, true),
            (false, true, false),
            (false, true, true),
        ] {
            assert!(
                !path_forwards_mut_borrow(path, is_std, is_spec_library, ghost_receiver),
                "{path} hands a writable borrow of its argument back to the \
                 caller: it can never suppress that argument's advance"
            );
        }
    }
}

// --- closure-capture invariant receiver spelling (D-76) ---

fn capture_inv_for(index: usize, name: &str) -> trust_wp_core::closure::CaptureInvariant {
    trust_wp_core::closure::CaptureInvariant::new(
        index,
        name,
        ExprSort::Datatype(trust_wp_core::formula::intern_sort_name("Zero")),
        "inv_Zero",
    )
}

#[test]
fn capture_receiver_bare_var_takes_the_environment_slot_sort() {
    let ci = capture_inv_for(0, "x");
    let annotated =
        super::super::primary::annotate_capture_receiver(PureExpr::Var("x".into(), None), &ci);
    assert_eq!(
        annotated,
        PureExpr::Var("x".into(), Some(ci.sort().clone()))
    );
}

#[test]
fn capture_receiver_self_env_projection_becomes_the_self_field_the_premise_uses() {
    let ci = capture_inv_for(0, "x");
    let projection = PureExpr::LogicFnCall {
        name: trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(2),
        args: vec![PureExpr::Var("self".into(), None)],
    };
    let annotated = super::super::primary::annotate_capture_receiver(projection, &ci);
    assert_eq!(
        annotated,
        PureExpr::Var("self.2".into(), Some(ci.sort().clone())),
        "the enclosing closure holds `inv(self.N)`; the obligation must be that term"
    );
}

#[test]
fn capture_receiver_leaves_a_constructed_aggregate_alone() {
    // The unfold that discharges a caller-built aggregate (D-65) matches on a
    // tuple CONSTRUCTOR application; rewriting it to a variable would hide it.
    let ci = capture_inv_for(0, "x");
    let built = PureExpr::LogicFnCall {
        name: trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name(2),
        args: vec![PureExpr::Int(0), PureExpr::Int(1)],
    };
    assert_eq!(
        super::super::primary::annotate_capture_receiver(built.clone(), &ci),
        built
    );
}

#[test]
fn capture_receiver_leaves_a_projection_of_something_else_alone() {
    // Only the CURRENT closure's own environment is `self`; a projection of any
    // other term names no capture slot the enclosing body holds `inv` about.
    let ci = capture_inv_for(0, "x");
    let other = PureExpr::LogicFnCall {
        name: trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(1),
        args: vec![PureExpr::Var("p".into(), None)],
    };
    assert_eq!(
        super::super::primary::annotate_capture_receiver(other.clone(), &ci),
        other
    );
}
