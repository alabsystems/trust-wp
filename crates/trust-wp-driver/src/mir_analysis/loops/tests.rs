// Copyright 2026 Andrew Yates
// Author: Andrew Yates
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
use rustc_hir::def_id::DefId;
use rustc_interface::interface::Compiler;
use rustc_middle::{
    mir::{BasicBlock, Body, Local, Place, ProjectionElem, StatementKind, TerminatorKind},
    ty::TyCtxt,
};
use trust_wp_core::formula::{BinOp, ExprSort, PureExpr};
use trust_wp_driver::StdSpec;

use super::{
    condition::switch_target_value_to_i64, detect_loops, extract_loop_body,
    post_loop::find_post_loop_exit_block, CallSpecContext, LoopAnalysis, LoopBodyExpr, LoopInfo,
};
use crate::mir_analysis::{collect_loop_body_call_obligations, LoopBodySpecContext};

mod call_results;

static TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

struct LoopCallbacks {
    fn_name: String,
    arg_names: Vec<String>,
    analysis: Option<LoopAnalysis>,
    loop_body: Option<LoopBodyExpr>,
    ran: bool,
}

impl Callbacks for LoopCallbacks {
    #[allow(clippy::elidable_lifetime_names)] // Matches rustc_driver::Callbacks trait signature
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let suffix = format!("::{}", self.fn_name);

        for local_def_id in tcx.hir_body_owners() {
            let def_path = tcx.def_path_str(local_def_id);
            if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                continue;
            }

            let body = tcx.optimized_mir(local_def_id.to_def_id());
            let analysis = detect_loops(body);
            let user_specs = HashMap::new();
            let trait_specs = HashMap::new();
            let extern_specs = HashMap::new();
            let call_spec_ctx = CallSpecContext {
                tcx,
                user_specs: &user_specs,
                trait_specs: &trait_specs,
                extern_specs: &extern_specs,
            };
            let loop_body = analysis.loops.first().map(|loop_info| {
                extract_loop_body(
                    body,
                    &self.arg_names,
                    loop_info,
                    Some(&analysis.loops),
                    Some(&call_spec_ctx),
                    false,
                )
            });

            self.analysis = Some(analysis);
            self.loop_body = loop_body;
            self.ran = true;
            break;
        }

        Compilation::Stop
    }
}

fn analyze_function(
    source: &str,
    fn_name: &str,
    arg_names: &[&str],
) -> (LoopAnalysis, Option<LoopBodyExpr>) {
    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_loop_analysis_{}_{}",
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
        "trust_wp_loop_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = LoopCallbacks {
        fn_name: fn_name.to_string(),
        arg_names: arg_names.iter().map(|name| (*name).to_string()).collect(),
        analysis: None,
        loop_body: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to locate function `{fn_name}` in rustc callback"
    );

    (
        callbacks
            .analysis
            .expect("loop analysis should be collected"),
        callbacks.loop_body,
    )
}

struct PoisonedExitCallbacks {
    fn_name: String,
    arg_names: Vec<String>,
    loop_body: Option<LoopBodyExpr>,
    ran: bool,
}

impl Callbacks for PoisonedExitCallbacks {
    #[allow(clippy::elidable_lifetime_names)] // Matches rustc_driver::Callbacks trait signature
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let suffix = format!("::{}", self.fn_name);

        for local_def_id in tcx.hir_body_owners() {
            let def_path = tcx.def_path_str(local_def_id);
            if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                continue;
            }

            let body = tcx.optimized_mir(local_def_id.to_def_id());
            let analysis = detect_loops(body);
            let loop_body = analysis.loops.first().map(|loop_info| {
                let mut poisoned_loop = loop_info.clone();
                let cond_block = find_test_cond_block(body, &poisoned_loop);
                let exit_block = find_post_loop_exit_block(body, cond_block, &poisoned_loop)
                    .expect("expected a post-loop exit block");
                poisoned_loop.body_blocks.insert(exit_block);
                extract_loop_body(
                    body,
                    &self.arg_names,
                    &poisoned_loop,
                    Some(&analysis.loops),
                    None,
                    false,
                )
            });

            self.loop_body = loop_body;
            self.ran = true;
            break;
        }

        Compilation::Stop
    }
}

fn find_test_cond_block(body: &Body<'_>, loop_info: &LoopInfo) -> BasicBlock {
    let header_data = &body.basic_blocks[loop_info.header];
    let cond_block = match &header_data.terminator().kind {
        TerminatorKind::SwitchInt { .. } => loop_info.header,
        TerminatorKind::FalseUnwind { real_target, .. } => *real_target,
        TerminatorKind::Call {
            target: Some(switch_bb),
            ..
        } => *switch_bb,
        TerminatorKind::Goto { target } => *target,
        _ => loop_info.header,
    };
    let cond_data = &body.basic_blocks[cond_block];
    match &cond_data.terminator().kind {
        TerminatorKind::Call {
            target: Some(switch_bb),
            ..
        } => *switch_bb,
        _ => cond_block,
    }
}

fn analyze_function_with_poisoned_exit_block(
    source: &str,
    fn_name: &str,
    arg_names: &[&str],
) -> Option<LoopBodyExpr> {
    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_loop_poisoned_exit_{}_{}",
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
        "trust_wp_loop_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = PoisonedExitCallbacks {
        fn_name: fn_name.to_string(),
        arg_names: arg_names.iter().map(|name| (*name).to_string()).collect(),
        loop_body: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to locate function `{fn_name}` in rustc callback"
    );

    callbacks.loop_body
}

struct ProjectedCallDestinationCallbacks {
    fn_name: String,
    arg_names: Vec<String>,
    projected_local_name: String,
    modified_vars: Option<Vec<String>>,
    changed_places_modified: Option<bool>,
    ran: bool,
}

impl Callbacks for ProjectedCallDestinationCallbacks {
    #[allow(clippy::elidable_lifetime_names)] // Matches rustc_driver::Callbacks trait signature
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let suffix = format!("::{}", self.fn_name);

        for local_def_id in tcx.hir_body_owners() {
            let def_path = tcx.def_path_str(local_def_id);
            if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                continue;
            }

            let body = tcx.optimized_mir(local_def_id.to_def_id());
            let analysis = detect_loops(body);
            let loop_info = analysis.loops.first().expect("expected loop body");

            let mut local_to_name: HashMap<Local, String> = self
                .arg_names
                .iter()
                .enumerate()
                .map(|(index, name)| (Local::from_usize(index + 1), name.clone()))
                .collect();

            for var_debug in &body.var_debug_info {
                if let rustc_middle::mir::VarDebugInfoContents::Place(place) = &var_debug.value {
                    if place.projection.is_empty() {
                        local_to_name.insert(place.local, var_debug.name.to_string());
                    }
                }
            }

            let projected_local = local_to_name
                .iter()
                .find_map(|(local, name)| (name == &self.projected_local_name).then_some(*local))
                .expect("expected projected local name to map to a MIR local");

            let mut body = body.clone();
            let mut call_target = None;
            for &bb in &loop_info.body_blocks {
                let bb_data = &mut body.basic_blocks.as_mut_preserves_cfg()[bb];
                if let TerminatorKind::Call {
                    destination,
                    target: Some(target),
                    ..
                } = &mut bb_data.terminator_mut().kind
                {
                    *destination = Place::from(projected_local).project_deeper(
                        &[ProjectionElem::Field(
                            rustc_abi::FieldIdx::from_u32(0),
                            tcx.types.i32,
                        )],
                        tcx,
                    );
                    call_target = Some(*target);
                    break;
                }
            }

            let call_target = call_target.expect("expected loop call terminator");
            body.basic_blocks.as_mut_preserves_cfg()[call_target]
                .statements
                .retain(|stmt| !matches!(stmt.kind, StatementKind::Assign(..)));

            let modified_vars =
                super::changed_places::extract_modified_vars(&body, loop_info, &local_to_name);
            let changed_places =
                super::changed_places::extract_changed_places(&body, loop_info, &local_to_name);

            self.modified_vars = Some(modified_vars);
            self.changed_places_modified =
                Some(changed_places.is_modified(&self.projected_local_name));
            self.ran = true;
            break;
        }

        Compilation::Stop
    }
}

fn analyze_projected_call_destination_loop(
    source: &str,
    fn_name: &str,
    arg_names: &[&str],
    projected_local_name: &str,
) -> (Vec<String>, bool) {
    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_projected_call_destination_{}_{}",
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
        "trust_wp_loop_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = ProjectedCallDestinationCallbacks {
        fn_name: fn_name.to_string(),
        arg_names: arg_names.iter().map(|name| (*name).to_string()).collect(),
        projected_local_name: projected_local_name.to_string(),
        modified_vars: None,
        changed_places_modified: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to locate function `{fn_name}` in rustc callback"
    );

    (
        callbacks
            .modified_vars
            .expect("projected call test should collect modified vars"),
        callbacks
            .changed_places_modified
            .expect("projected call test should collect changed place state"),
    )
}

fn expect_i_plus(expr: &PureExpr, delta: i64) {
    match expr {
        PureExpr::BinOp(lhs, BinOp::Add, rhs) => {
            assert!(
                matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == "i"),
                "expected lhs to be i, got {lhs:?} in {expr:?}"
            );
            assert!(
                matches!(rhs.as_ref(), PureExpr::Int(n) if *n == delta),
                "expected rhs delta {delta}, got {rhs:?} in {expr:?}"
            );
        }
        other => panic!("expected i + {delta} update, got {other:?}"),
    }
}

fn expect_var_plus(expr: &PureExpr, var: &str, delta: i64) {
    match expr {
        PureExpr::BinOp(lhs, BinOp::Add, rhs) => {
            assert!(
                matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == var),
                "expected lhs to be {var}, got {lhs:?} in {expr:?}"
            );
            assert!(
                matches!(rhs.as_ref(), PureExpr::Int(n) if *n == delta),
                "expected rhs delta {delta}, got {rhs:?} in {expr:?}"
            );
        }
        other => panic!("expected {var} + {delta} update, got {other:?}"),
    }
}

fn collect_i_updates(expr: &PureExpr, out: &mut Vec<i64>) {
    match expr {
        PureExpr::Ite(_, then_expr, else_expr) => {
            collect_i_updates(then_expr, out);
            collect_i_updates(else_expr, out);
        }
        leaf => match leaf {
            PureExpr::BinOp(lhs, BinOp::Add, rhs) => {
                assert!(matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == "i"));
                if let PureExpr::Int(delta) = rhs.as_ref() {
                    out.push(*delta);
                } else {
                    panic!("expected integer delta in i update, got {rhs:?}");
                }
            }
            other => panic!("expected update leaf expression, got {other:?}"),
        },
    }
}

fn expr_contains_deref(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Deref(_) => true,
        PureExpr::BinOp(lhs, _, rhs) => expr_contains_deref(lhs) || expr_contains_deref(rhs),
        PureExpr::UnOp(_, inner)
        | PureExpr::Final(inner)
        | PureExpr::Old(inner)
        | PureExpr::View(inner) => expr_contains_deref(inner),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            expr_contains_deref(cond)
                || expr_contains_deref(then_expr)
                || expr_contains_deref(else_expr)
        }
        PureExpr::LogicFnCall { args, .. } => args.iter().any(expr_contains_deref),
        PureExpr::MethodCall { receiver, args, .. } => {
            expr_contains_deref(receiver) || args.iter().any(expr_contains_deref)
        }
        _ => false,
    }
}

fn expr_contains_nested_deref(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Deref(inner) => {
            matches!(inner.as_ref(), PureExpr::Deref(_)) || expr_contains_nested_deref(inner)
        }
        PureExpr::BinOp(lhs, _, rhs) => {
            expr_contains_nested_deref(lhs) || expr_contains_nested_deref(rhs)
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Final(inner)
        | PureExpr::Old(inner)
        | PureExpr::View(inner) => expr_contains_nested_deref(inner),
        PureExpr::Ite(cond, then_expr, else_expr) => {
            expr_contains_nested_deref(cond)
                || expr_contains_nested_deref(then_expr)
                || expr_contains_nested_deref(else_expr)
        }
        PureExpr::LogicFnCall { args, .. } => args.iter().any(expr_contains_nested_deref),
        PureExpr::MethodCall { receiver, args, .. } => {
            expr_contains_nested_deref(receiver) || args.iter().any(expr_contains_nested_deref)
        }
        _ => false,
    }
}

fn is_eq_int(expr: &PureExpr, value: i64) -> bool {
    matches!(
        expr,
        PureExpr::BinOp(_, BinOp::Eq, rhs)
            if matches!(rhs.as_ref(), PureExpr::Int(v) if *v == value)
    )
}

fn is_two_variant_tautology(expr: &PureExpr) -> bool {
    matches!(
        expr,
        PureExpr::BinOp(lhs, BinOp::Or, rhs)
            if (is_eq_int(lhs, 0) && is_eq_int(rhs, 1))
                || (is_eq_int(lhs, 1) && is_eq_int(rhs, 0))
    )
}

#[test]
fn detect_loops_finds_simple_while_loop() {
    let source = r#"
pub fn simple_loop(n: i32) -> i32 {
let mut i = 0;
while i < n {
    i += 1;
}
i
}
"#;

    let (analysis, _) = analyze_function(source, "simple_loop", &["n"]);
    assert!(analysis.has_loops, "expected loop detection in simple_loop");
    assert_eq!(analysis.loops.len(), 1, "expected exactly one loop");
}

#[test]
fn detect_loops_finds_nested_loops() {
    let source = r#"
pub fn nested_loop(n: i32) -> i32 {
let mut i = 0;
let mut j = 0;
while i < n {
    j = 0;
    while j < i {
        j += 1;
    }
    i += 1;
}
i + j
}
"#;

    let (analysis, _) = analyze_function(source, "nested_loop", &["n"]);
    assert!(analysis.has_loops, "expected loop detection in nested_loop");
    assert!(
        analysis.loops.len() >= 2,
        "expected nested-loop detection to report >=2 loops, got {}",
        analysis.loops.len()
    );
}

#[test]
fn extract_body_effects_handles_simple_assignment() {
    let source = r#"
pub fn simple_assignment(n: i32) -> i32 {
let mut i = 0;
while i < n {
    i = i + 1;
}
i
}
"#;

    let (_, loop_body) = analyze_function(source, "simple_assignment", &["n"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    let effect = loop_body
        .body_effects
        .get("i")
        .expect("expected body effect for i");

    match effect {
        PureExpr::BinOp(lhs, BinOp::Add, rhs) => {
            assert!(matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == "i"));
            assert!(matches!(rhs.as_ref(), PureExpr::Int(1)));
        }
        other => panic!("expected i -> i + 1 body effect, got {other:?}"),
    }
}

#[test]
fn extract_modified_vars_includes_call_destinations() {
    let source = r#"
#[inline(never)]
fn inc(x: i32) -> i32 {
x + 1
}

pub fn call_assignment_loop(n: i32) -> i32 {
let mut i = 0;
while i < n {
    i = inc(i);
}
i
}
"#;

    let (_, loop_body) = analyze_function(source, "call_assignment_loop", &["n"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    assert!(
        loop_body.modified_vars.iter().any(|name| name == "i"),
        "call destination local should be tracked as modified: {:?}",
        loop_body.modified_vars
    );
}

#[test]
fn extract_modified_vars_includes_projected_call_destinations() {
    let source = r#"
#[inline(never)]
fn inc(x: i32) -> i32 {
x + 1
}

pub fn projected_call_destination_loop(n: i32) -> i32 {
let mut pair = (0, 0);
while pair.0 < n {
    pair.0 = inc(pair.0);
}
pair.0
}
"#;

    let (modified_vars, changed_places_modified) = analyze_projected_call_destination_loop(
        source,
        "projected_call_destination_loop",
        &["n"],
        "pair",
    );

    assert!(
        changed_places_modified,
        "projected call destination should still be present in changed_places"
    );
    assert!(
        modified_vars.iter().any(|name| name == "pair"),
        "projected call destination local should be tracked as modified: {modified_vars:?}"
    );
}

#[test]
fn extract_changed_places_tracks_index_mut_write_through_temp() {
    // `v[i] = 0` in a loop body lowers to:
    //   _tmp = IndexMut::index_mut(&mut v, i);
    //   *_tmp = 0;
    // The deref-write goes through an unnamed temp, but `v` must still be
    // marked as modified so `infer_parameter_frame_invariants` doesn't try to
    // synthesize a frame invariant for an actually-mutated parameter. (Wave 7A)
    let source = r#"
pub fn index_mut_write(v: &mut Vec<i32>) {
    let mut i = 0;
    while i < 10 {
        v[i] = 0;
        i += 1;
    }
}
"#;

    let (_, loop_body) = analyze_function(source, "index_mut_write", &["v"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    assert!(
        loop_body.modified_vars.iter().any(|name| name == "v"),
        "v should be tracked as modified through index_mut reborrow temp: {:?}",
        loop_body.modified_vars
    );
    assert!(
        loop_body.changed_places.is_modified("v"),
        "changed_places should record v as modified: {:?}",
        loop_body.changed_places
    );
}

#[test]
fn extract_changed_places_tracks_reborrow_chain_to_named_local() {
    // Confirms reborrow chains (`_tmp1 = &mut x; _tmp2 = move _tmp1; *_tmp2 = 0`)
    // are followed back to the named local. (Wave 7A)
    let source = r#"
pub fn reborrow_chain_write(x: &mut i32) {
    let mut i = 0;
    while i < 10 {
        let y: &mut i32 = &mut *x;
        *y = 0;
        i += 1;
    }
}
"#;

    let (_, loop_body) = analyze_function(source, "reborrow_chain_write", &["x"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    assert!(
        loop_body.modified_vars.iter().any(|name| name == "x"),
        "x should be tracked as modified through reborrow chain: {:?}",
        loop_body.modified_vars
    );
    assert!(
        loop_body.changed_places.is_modified("x"),
        "changed_places should record x as modified: {:?}",
        loop_body.changed_places
    );
}

#[test]
fn extract_body_effects_clears_stale_effect_when_call_overwrites_assignment() {
    let source = r#"
#[inline(never)]
fn inc(x: i32) -> i32 {
x + 1
}

pub fn call_overwrites_assignment(n: i32) -> i32 {
let mut i = 0;
while i < n {
    i = i + 1;
    i = inc(i);
}
i
}
"#;

    let (_, loop_body) = analyze_function(source, "call_overwrites_assignment", &["n"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    assert!(
        loop_body.modified_vars.iter().any(|name| name == "i"),
        "call destination local should be tracked as modified: {:?}",
        loop_body.modified_vars
    );
    assert!(
        !loop_body.body_effects.contains_key("i"),
        "call destination should clear stale assignment-derived effect: {:?}",
        loop_body.body_effects
    );
}

#[test]
fn extract_body_effects_handles_compound_ops() {
    let source = r#"
pub fn compound_ops(n: i32, step: i32) -> i32 {
let mut i = 0;
while i < n {
    i += step;
}
i
}
"#;

    let (_, loop_body) = analyze_function(source, "compound_ops", &["n", "step"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    let effect = loop_body
        .body_effects
        .get("i")
        .expect("expected body effect for i");

    match effect {
        PureExpr::BinOp(lhs, BinOp::Add, rhs) => {
            assert!(matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == "i"));
            assert!(matches!(rhs.as_ref(), PureExpr::Var(name, _) if name == "step"));
        }
        other => panic!("expected i -> i + step body effect, got {other:?}"),
    }
}

#[test]
fn extract_body_effects_merges_if_inside_loop_with_ite() {
    let source = r#"
pub fn branch_in_loop(n: i32) -> i32 {
let mut i = 0;
while i < n {
    if i % 2 == 0 {
        i += 1;
    } else {
        i += 2;
    }
}
i
}
"#;

    let (_, loop_body) = analyze_function(source, "branch_in_loop", &["n"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    let effect = loop_body
        .body_effects
        .get("i")
        .expect("expected body effect for i");

    match effect {
        PureExpr::Ite(_, then_expr, else_expr) => {
            expect_i_plus(then_expr, 1);
            expect_i_plus(else_expr, 2);
        }
        other => panic!("expected Ite-merged body effect for i, got {other:?}"),
    }
}

#[test]
fn extract_body_effects_merges_if_without_else_with_identity_fallback() {
    let source = r#"
pub fn branch_without_else(n: i32) -> i32 {
let mut i = 0;
while i < n {
    if i % 2 == 0 {
        i += 1;
    }
}
i
}
"#;

    let (_, loop_body) = analyze_function(source, "branch_without_else", &["n"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    let effect = loop_body
        .body_effects
        .get("i")
        .expect("expected body effect for i");

    match effect {
        PureExpr::Ite(_, then_expr, else_expr) => {
            expect_i_plus(then_expr, 1);
            assert!(
                matches!(else_expr.as_ref(), PureExpr::Var(name, _) if name == "i"),
                "expected else branch to keep i unchanged, got {else_expr:?}"
            );
        }
        other => panic!("expected Ite body effect for i, got {other:?}"),
    }
}

/// A conditional accumulator incremented only in one arm of a guard whose
/// condition reads a `Vec`/`[T]` element through the `Index::index` *call*
/// (not a primitive `Index` projection) must still receive its true merged
/// body effect `count' = ite(t@[i] > 0, count + 1, count)`. Before the
/// index-read modeling, the `Vec::index` call result was havoced, the guard
/// `t[i] > 0` could not be translated, the `if` collapsed to an opaque
/// conservative merge, and the one-branch `count` effect was dropped — leaving
/// `count` havoced during loop preservation. (#filter_positive)
#[test]
fn extract_body_effects_conditional_accumulator_over_vec_index_call() {
    let source = r#"
pub fn count_positive(t: Vec<i32>) -> usize {
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < t.len() {
        if t[i] > 0 {
            count += 1;
        }
        i += 1;
    }
    count
}
"#;

    let (_, loop_body) = analyze_function(source, "count_positive", &["t"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    let effect = loop_body
        .body_effects
        .get("count")
        .expect("expected conditional body effect for count");

    // count' = Ite(guard, count + 1, count)
    let PureExpr::Ite(cond, then_expr, else_expr) = effect else {
        panic!("expected Ite-merged conditional accumulator effect, got {effect:?}");
    };
    // Guard reads the indexed element: `View(Var("t")).index_logic(i) > 0`.
    let PureExpr::BinOp(guard_lhs, BinOp::Gt, guard_rhs) = cond.as_ref() else {
        panic!("expected `t[i] > 0` guard, got {cond:?}");
    };
    assert!(
        matches!(guard_rhs.as_ref(), PureExpr::Int(0)),
        "expected guard compared against 0, got {guard_rhs:?}"
    );
    assert!(
        matches!(
            guard_lhs.as_ref(),
            PureExpr::MethodCall { receiver, method, .. }
                if method == "index_logic"
                    && matches!(
                        receiver.as_ref(),
                        PureExpr::View(inner)
                            if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "t")
                    )
        ),
        "expected guard to read `View(Var(\"t\")).index_logic(..)`, got {guard_lhs:?}"
    );
    // then-arm increments count, else-arm leaves it unchanged.
    expect_var_plus(then_expr, "count", 1);
    assert!(
        matches!(else_expr.as_ref(), PureExpr::Var(name, _) if name == "count"),
        "expected else arm to keep count unchanged, got {else_expr:?}"
    );
}

/// SOUNDNESS: a `HashMap` element read through `Index::index` must NOT be
/// modeled as `self@.index_logic(key)`. A map's `Index::index` spec is
/// `self@.get(key) == Some(result)`, a different accessor — modeling it as the
/// sequence accessor `index_logic` would bind a wrong value and could
/// false-accept. The index-read modeling is restricted to sequence-indexable
/// receivers (`Vec`/`[T]`/`[T; N]`); a map read must leave the result havoced,
/// so the conditional accumulator gets NO body effect (the conservative safe
/// default). (#filter_positive soundness guard)
#[test]
fn extract_body_effects_hashmap_index_read_is_not_modeled() {
    let source = r#"
use std::collections::HashMap;
pub fn count_map(m: HashMap<usize, i32>, keys: Vec<usize>) -> usize {
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < keys.len() {
        if m[&keys[i]] > 0 {
            count += 1;
        }
        i += 1;
    }
    count
}
"#;

    let (_, loop_body) = analyze_function(source, "count_map", &["m", "keys"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    // The map read is not modeled as `index_logic`, so the guard stays opaque
    // and the one-branch `count` accumulator receives no (fabricated) effect.
    // If a `count` effect IS produced, it must not encode the map read as a
    // sequence `index_logic` on `m`.
    if let Some(effect) = loop_body.body_effects.get("count") {
        let mut mentions_map_index_logic = false;
        effect.for_each_recursive(|node| {
            if let PureExpr::MethodCall {
                receiver, method, ..
            } = node
            {
                if method == "index_logic" {
                    receiver.for_each_recursive(|r| {
                        if matches!(r, PureExpr::Var(name, _) if name == "m") {
                            mentions_map_index_logic = true;
                        }
                    });
                }
            }
        });
        assert!(
            !mentions_map_index_logic,
            "HashMap read must not be modeled as `m.index_logic(..)`, got {effect:?}"
        );
    }
}

#[test]
fn extract_body_effects_merges_match_inside_loop_with_ite_chain() {
    let source = r#"
pub fn match_in_loop(n: i32) -> i32 {
let mut i = 0;
while i < n {
    match i % 3 {
        0 => i += 1,
        1 => i += 2,
        _ => i += 3,
    }
}
i
}
"#;

    let (_, loop_body) = analyze_function(source, "match_in_loop", &["n"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    let effect = loop_body
        .body_effects
        .get("i")
        .expect("expected body effect for i");
    assert!(
        matches!(effect, PureExpr::Ite(_, _, _)),
        "expected Ite chain for match body effect, got {effect:?}"
    );

    let mut deltas = Vec::new();
    collect_i_updates(effect, &mut deltas);
    deltas.sort_unstable();
    assert_eq!(
        deltas,
        vec![1, 2, 3],
        "expected updates from all match arms"
    );
}

#[test]
fn extract_body_effects_non_header_switch_preserves_continue_back_edge() {
    let source = r#"
pub fn branch_continue_backedge(n: i32) -> i32 {
let mut i = 0;
while i < n {
    if i < 5 {
        i += 2;
        continue;
    }
    i += 1;
}
i
}
"#;

    let (_, loop_body) = analyze_function(source, "branch_continue_backedge", &["n"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    let effect = loop_body
        .body_effects
        .get("i")
        .expect("expected body effect for i");
    assert!(
        matches!(effect, PureExpr::Ite(_, _, _)),
        "expected branch merge for continue back-edge, got {effect:?}"
    );

    let mut deltas = Vec::new();
    collect_i_updates(effect, &mut deltas);
    deltas.sort_unstable();
    assert_eq!(
        deltas,
        vec![1, 2],
        "expected merged updates from continue and non-continue branches"
    );
}

#[test]
fn extract_body_effects_resolves_temps() {
    let source = r#"
pub fn missing_temp_resolution(n: i32) -> i32 {
let mut i = 0;
while i < n {
    let tmp = i & 1;
    i = tmp;
}
i
}
"#;

    let (_, loop_body) = analyze_function(source, "missing_temp_resolution", &["n"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    // Temp resolution now correctly inlines `i = tmp` → `i = i & 1`.
    // The body effect for `i` should be `BinOp(Var("i"), BitAnd, Int(1))`.
    assert!(
        loop_body.body_effects.contains_key("i"),
        "temp resolution should produce i effect: {:?}",
        loop_body.body_effects
    );
    let i_effect = &loop_body.body_effects["i"];
    assert!(
        matches!(i_effect, PureExpr::BinOp(_, _, _)),
        "i effect should be BinOp (i & 1), got {i_effect:?}"
    );
}

/// Whether `expr` is the cons-payload tail accessor `Deref(__trust_wp_tuple_get_F(..))`
/// applied (possibly through a `Deref` of a reference) to the named scrutinee.
fn is_cons_tail_accessor(expr: &PureExpr, scrutinee: &str, field_idx: usize) -> bool {
    use trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name;
    let PureExpr::Deref(inner) = expr else {
        return false;
    };
    let PureExpr::LogicFnCall { name, args } = inner.as_ref() else {
        return false;
    };
    if *name != tuple_field_logic_fn_name(field_idx) || args.len() != 1 {
        return false;
    }
    // The argument is the scrutinee, viewed as a Datatype value: either the bare
    // var (owned list) or `Deref(Var)` (reference-typed loop variable).
    fn base_var(e: &PureExpr) -> Option<&str> {
        match e {
            PureExpr::Var(name, _) => Some(name.as_str()),
            PureExpr::Deref(i) | PureExpr::View(i) => base_var(i),
            _ => None,
        }
    }
    base_var(&args[0]) == Some(scrutinee)
}

#[test]
fn extract_body_effects_ties_ref_loop_var_to_cons_tail_binary_search_shape() {
    // binary_search_list shape: the loop variable is `&List` and the
    // next-iteration reassignment is `l = &*ls` — lowered to a
    // `Box -> NonNull -> *const List` transmute chain + reborrow. The loop-var
    // body effect must be tied to the cons tail `*cons_1(l)`, not havoced.
    let source = r#"
#[allow(dead_code)]
pub enum List {
    Cons(u32, Box<List>),
    Nil,
}
pub fn bsearch(arr: &List, mut ix: usize) {
    let mut l = arr;
    while let List::Cons(t, ls) = l {
        if ix > 0 {
            l = &*ls;
            ix -= 1;
        } else {
            break;
        }
    }
}
"#;
    let (_, loop_body) = analyze_function(source, "bsearch", &["arr", "ix"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    let effect = loop_body.body_effects.get("l").unwrap_or_else(|| {
        panic!(
            "expected body effect tying `l` to the cons tail: {:?}",
            loop_body.body_effects
        )
    });
    assert!(
        is_cons_tail_accessor(effect, "l", 1),
        "ref loop var should be tied to cons tail `*cons_1(l)`: {effect:?}"
    );
}

#[test]
fn extract_body_effects_ties_mutref_loop_var_to_cons_tail_all_zero_shape() {
    // all_zero_list shape: the loop variable is `&mut List` and the
    // next-iteration reassignment is `loop_l = next` (a `&mut` reborrow of the
    // cons tail). The loop-var body effect must be tied to `*cons_1(loop_l)`.
    let source = r#"
#[allow(dead_code)]
pub enum List {
    Cons(u32, Box<List>),
    Nil,
}
pub fn allzero(l: &mut List) {
    let mut loop_l = l;
    while let List::Cons(value, next) = loop_l {
        *value = 0;
        loop_l = next;
    }
}
"#;
    let (_, loop_body) = analyze_function(source, "allzero", &["l"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    let effect = loop_body.body_effects.get("loop_l").unwrap_or_else(|| {
        panic!(
            "expected body effect tying `loop_l` to the cons tail: {:?}",
            loop_body.body_effects
        )
    });
    assert!(
        is_cons_tail_accessor(effect, "loop_l", 1),
        "mut-ref loop var should be tied to cons tail `*cons_1(loop_l)`: {effect:?}"
    );
}

#[test]
fn extract_body_effects_does_not_tie_nonrecursive_box_ref_reassignment() {
    // SOUNDNESS: a `&mut`-reborrow loop reassignment whose source box payload is
    // NOT the recursive self type must NOT be modeled as the cons tail (it would
    // bind a wrong value). Here the `Other` box wraps `Inner`, not `Tree`.
    let source = r#"
#[allow(dead_code)]
pub enum Inner {
    A,
    B,
}
#[allow(dead_code)]
pub enum Tree {
    Node(u32, Box<Tree>),
    Leaf(Box<Inner>),
}
pub fn walk(t: &Tree) {
    let mut l = t;
    while let Tree::Leaf(b) = l {
        let _ = b;
        // Reassign `l` from a non-recursive (Inner) boxed payload reference is
        // impossible by type, so this body just re-reads `t` to exercise the
        // recognizer's recursive-field gate via the Node variant index reuse.
        l = t;
    }
}
"#;
    let (_, loop_body) = analyze_function(source, "walk", &["t"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    // `l = t` is a plain copy of an arg, not a cons-tail reborrow: it must not
    // be modeled as a cons-tail accessor.
    if let Some(effect) = loop_body.body_effects.get("l") {
        assert!(
            !is_cons_tail_accessor(effect, "l", 1) && !is_cons_tail_accessor(effect, "t", 1),
            "non-cons-tail reassignment must not be modeled as cons tail: {effect:?}"
        );
    }
}

#[test]
fn extract_body_effects_tracks_box_tail_assignment() {
    let source = r#"
#[allow(dead_code)]
pub enum List {
    Nil,
    Cons(i32, Box<List>),
}

pub fn consume_tail(mut l: List) {
    while let List::Cons(_, tl) = l {
        l = *tl;
    }
}
"#;

    let (_, loop_body) = analyze_function(source, "consume_tail", &["l"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    let effect = loop_body
        .body_effects
        .get("l")
        .unwrap_or_else(|| panic!("expected body effect for l: {:?}", loop_body.body_effects));

    assert!(
        !matches!(effect, PureExpr::Var(name, _) if name == "l"),
        "tail assignment should not collapse to identity: {effect:?}"
    );
    assert!(
        expr_contains_deref(effect),
        "tail assignment should preserve Box dereference: {effect:?}"
    );
    assert!(
        !expr_contains_nested_deref(effect),
        "tail assignment should not add nested Box dereferences: {effect:?}"
    );
}

#[test]
fn extract_body_effects_tracks_box_tail_assignment_after_call() {
    let source = r#"
#[allow(dead_code)]
pub enum List {
    Nil,
    Cons((i32, i32), Box<List>),
}

#[inline(never)]
pub fn sink(_: i32, _: i32) {}

pub fn consume_tail_after_call(mut l: List) {
    while let List::Cons((k, v), tl) = l {
        sink(k, v);
        l = *tl;
    }
}
"#;

    let (_, loop_body) = analyze_function(source, "consume_tail_after_call", &["l"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    let effect = loop_body
        .body_effects
        .get("l")
        .unwrap_or_else(|| panic!("expected body effect for l: {:?}", loop_body.body_effects));

    assert!(
        !matches!(effect, PureExpr::Var(name, _) if name == "l"),
        "tail assignment after call should not collapse to identity: {effect:?}"
    );
    assert!(
        expr_contains_deref(effect),
        "tail assignment after call should preserve Box dereference: {effect:?}"
    );
    assert!(
        !expr_contains_nested_deref(effect),
        "tail assignment after call should not add nested Box dereferences: {effect:?}"
    );
}

#[test]
fn extract_body_effects_tracks_box_tail_assignment_after_mut_method_call() {
    let source = r#"
#[allow(dead_code)]
pub enum List {
    Nil,
    Cons((i32, i32), Box<List>),
}

pub struct Sink {
    total: i32,
}

impl Sink {
    #[inline(never)]
    pub fn add(&mut self, k: i32, v: i32) {
        self.total += k + v;
    }
}

pub fn consume_tail_after_mut_method_call(mut l: List, new: &mut Sink) {
    while let List::Cons((k, v), tl) = l {
        new.add(k, v);
        l = *tl;
    }
}
"#;

    let (_, loop_body) =
        analyze_function(source, "consume_tail_after_mut_method_call", &["l", "new"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    let effect = loop_body
        .body_effects
        .get("l")
        .unwrap_or_else(|| panic!("expected body effect for l: {:?}", loop_body.body_effects));

    assert!(
        !matches!(effect, PureExpr::Var(name, _) if name == "l"),
        "tail assignment after mut method call should not collapse to identity: {effect:?}"
    );
    assert!(
        expr_contains_deref(effect),
        "tail assignment after mut method call should preserve Box dereference: {effect:?}"
    );
    assert!(
        !expr_contains_nested_deref(effect),
        "tail assignment after mut method call should not add nested Box dereferences: {effect:?}"
    );
}

#[test]
fn extract_body_effects_tracks_generic_box_tail_assignment_after_mut_method_call() {
    let source = r#"
#[allow(dead_code)]
pub enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

pub struct Sink<T> {
    last: Option<(T, T)>,
}

impl<T: Copy> Sink<T> {
    #[inline(never)]
    pub fn add(&mut self, k: T, v: T) {
        self.last = Some((k, v));
    }
}

pub fn consume_generic_tail_after_mut_method_call<T: Copy>(
    mut l: List<(T, T)>,
    new: &mut Sink<T>,
) {
    while let List::Cons((k, v), tl) = l {
        new.add(k, v);
        l = *tl;
    }
}
"#;

    let (_, loop_body) = analyze_function(
        source,
        "consume_generic_tail_after_mut_method_call",
        &["l", "new"],
    );
    let loop_body = loop_body.expect("expected loop body extraction");
    let effect = loop_body
        .body_effects
        .get("l")
        .unwrap_or_else(|| panic!("expected body effect for l: {:?}", loop_body.body_effects));

    assert!(
        !matches!(effect, PureExpr::Var(name, _) if name == "l"),
        "generic tail assignment after mut method call should not collapse to identity: {effect:?}"
    );
    assert!(
        expr_contains_deref(effect),
        "generic tail assignment after mut method call should preserve Box dereference: {effect:?}"
    );
    assert!(
        !expr_contains_nested_deref(effect),
        "generic tail assignment after mut method call should not add nested Box dereferences: {effect:?}"
    );
}

#[test]
fn extract_body_effects_tracks_noncopy_box_tail_assignment_after_consuming_call() {
    let source = r#"
#[allow(dead_code)]
pub enum List<T> {
    Nil,
    Cons(T, Box<List<T>>),
}

pub struct Sink<T> {
    last: Option<T>,
}

impl<T> Sink<T> {
    #[inline(never)]
    pub fn add(&mut self, value: T) {
        self.last = Some(value);
    }
}

pub fn consume_noncopy_tail_after_consuming_call<T>(
    mut l: List<T>,
    new: &mut Sink<T>,
) {
    while let List::Cons(value, tl) = l {
        new.add(value);
        l = *tl;
    }
}
"#;

    let (_, loop_body) = analyze_function(
        source,
        "consume_noncopy_tail_after_consuming_call",
        &["l", "new"],
    );
    let loop_body = loop_body.expect("expected loop body extraction");
    let effect = loop_body
        .body_effects
        .get("l")
        .unwrap_or_else(|| panic!("expected body effect for l: {:?}", loop_body.body_effects));

    assert!(
        !matches!(effect, PureExpr::Var(name, _) if name == "l"),
        "non-Copy tail assignment should not collapse to identity: {effect:?}"
    );
    assert!(
        expr_contains_deref(effect),
        "non-Copy tail assignment should preserve Box dereference: {effect:?}"
    );
    assert!(
        !expr_contains_nested_deref(effect),
        "non-Copy tail assignment should not add nested Box dereferences: {effect:?}"
    );
}

#[test]
fn extract_pre_loop_assignments_single_var() {
    let source = r#"
pub fn pre_loop_single(n: i32) -> i32 {
let mut i = 5;
while i < n {
    i += 1;
}
i
}
"#;

    let (_, loop_body) = analyze_function(source, "pre_loop_single", &["n"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    assert_eq!(
        loop_body.pre_loop_assignments.get("i").map(|b| &b.value),
        Some(&PureExpr::Int(5))
    );
}

#[test]
fn extract_pre_loop_assignments_multiple_vars() {
    let source = r#"
pub fn pre_loop_multi(n: i32) -> i32 {
let mut i = 0;
let mut sum = 10;
while i < n {
    sum += i;
    i += 1;
}
sum
}
"#;

    let (_, loop_body) = analyze_function(source, "pre_loop_multi", &["n"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    assert_eq!(
        loop_body.pre_loop_assignments.get("i").map(|b| &b.value),
        Some(&PureExpr::Int(0))
    );
    assert_eq!(
        loop_body.pre_loop_assignments.get("sum").map(|b| &b.value),
        Some(&PureExpr::Int(10))
    );
}

#[test]
fn extract_pre_loop_multifield_struct_preserves_native_constructor() {
    let source = r#"
#[derive(Copy, Clone)]
pub struct Point {
    pub x: isize,
    pub y: isize,
}

pub fn struct_before_loop(n: usize, x: isize, y: isize) -> isize {
    let mut p = Point { x, y };
    let mut i = 0usize;
    while i < n {
        p = Point { x: p.x + 1, y: p.y };
        i += 1;
    }
    p.x
}
"#;

    let (_, loop_body) = analyze_function(source, "struct_before_loop", &["n", "x", "y"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    let p = loop_body
        .pre_loop_assignments
        .get("p")
        .map(|binding| &binding.value)
        .expect("pre-loop Point assignment should be captured");
    assert!(
        matches!(p, PureExpr::LogicFnCall { name, args } if name == "Point" && args.len() == 2),
        "multi-field struct aggregate should keep native constructor, got {p:?}"
    );
}

#[test]
fn extract_for_range_condition_from_desugared_mir() {
    let source = r#"
pub fn for_range_condition() -> usize {
let mut acc = 0usize;
for pass in 1usize..5usize {
    acc += pass;
}
acc
}
"#;

    let (_, loop_body) = analyze_function(source, "for_range_condition", &[]);
    let loop_body = loop_body.expect("expected loop body extraction");
    let condition = loop_body
        .condition
        .expect("expected synthesized condition for for-range loop");

    // After #2171, synthesize_for_range_condition returns only the
    // produced-count bound. The element guard (pass >= start && pass < end)
    // is planned but not yet implemented — tracked as part of #2171.
    // The receiver is View(Var("produced")) because the condition synthesis
    // in condition.rs wraps the ghost seq variable in a view projection
    // (commit 7a76c463, #2171 transition-model follow-up).
    let expected = PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::View(Arc::new(PureExpr::Var(
                "produced".to_string(),
                Some(ExprSort::Seq),
            )))),
            method: "len".to_string(),
            args: vec![],
        }),
        BinOp::Lt,
        Arc::new(PureExpr::BinOp(
            Arc::new(PureExpr::Int(5)),
            BinOp::Sub,
            Arc::new(PureExpr::Int(1)),
        )),
    );
    assert_eq!(
        condition, expected,
        "for-range loop should synthesize the produced-count bound"
    );
}

#[test]
fn extract_while_vec_len_condition_resolves_call_result() {
    let source = r#"
pub fn while_vec_len(v: &Vec<i32>) -> usize {
let mut i = 0usize;
while i < v.len() {
    std::hint::black_box(i);
    i += 1;
}
i
}
"#;

    let (_, loop_body) = analyze_function(source, "while_vec_len", &["v"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    let condition = loop_body
        .condition
        .expect("expected while condition extraction");

    let PureExpr::BinOp(lhs, BinOp::Lt, rhs) = condition else {
        panic!("expected i < len condition, got {condition:?}");
    };
    assert!(
        matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == "i"),
        "expected lhs to be loop index i, got {lhs:?}"
    );
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = rhs.as_ref()
    else {
        panic!("expected rhs to be a len call, got {rhs:?}");
    };
    assert_eq!(method, "len");
    assert!(args.is_empty());
    assert!(
        matches!(
            receiver.as_ref(),
            PureExpr::View(inner)
                if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "v")
        ),
        "expected len receiver to be View(v), got {receiver:?}"
    );
}

#[test]
fn extract_while_vec_field_len_condition_resolves_receiver() {
    let source = r#"
pub struct MyMap {
    buckets: Vec<i32>,
}

impl MyMap {
    pub fn resize(&mut self) {
        let mut i = 0usize;
        while i < self.buckets.len() {
            std::hint::black_box(i);
            i += 1;
        }
    }
}
"#;

    let (_, loop_body) = analyze_function(source, "resize", &["self"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    let condition = loop_body
        .condition
        .expect("expected while condition extraction");

    let PureExpr::BinOp(lhs, BinOp::Lt, rhs) = condition else {
        panic!("expected i < len condition, got {condition:?}");
    };
    assert!(
        matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == "i"),
        "expected lhs to be loop index i, got {lhs:?}"
    );
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = rhs.as_ref()
    else {
        panic!("expected rhs to be a len call, got {rhs:?}");
    };
    assert_eq!(method, "len");
    assert!(args.is_empty());
    assert!(
        matches!(
            receiver.as_ref(),
            PureExpr::View(inner)
                if matches!(
                    inner.as_ref(),
                    PureExpr::LogicFnCall { name, args }
                        if name == "__trust_wp_field_buckets"
                            && matches!(args.as_slice(), [PureExpr::Deref(inner)]
                                if matches!(inner.as_ref(), PureExpr::Var(var, _) if var == "self"))
                )
        ),
        "expected len receiver to be View(__trust_wp_field_buckets(*self)), got {receiver:?}"
    );
}

#[test]
fn extract_post_loop_return_expr_tracks_return_local() {
    let source = r#"
pub fn post_loop_return(n: i32) -> i32 {
let mut i = 0;
while i < n {
    i += 1;
}
i
}
"#;

    let (_, loop_body) = analyze_function(source, "post_loop_return", &["n"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    match loop_body.return_expr {
        Some(PureExpr::Var(name, _)) => assert_eq!(name, "i"),
        other => panic!("expected return expr to bind to local i, got {other:?}"),
    }
}

#[test]
fn extract_post_loop_deref_writes_marks_post_loop_mutation() {
    let source = r#"
pub fn post_loop_write(v: &mut i32) -> i32 {
while *v < 10 {
    *v += 1;
}
*v = 42;
*v
}
"#;

    let (_, loop_body) = analyze_function(source, "post_loop_write", &["v"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    assert!(
        loop_body.post_loop_deref_writes.contains("v"),
        "post-loop deref write should mark `v` for borrow-resolution gating"
    );
}

#[test]
fn extract_post_loop_deref_writes_empty_when_no_post_loop_mutation() {
    let source = r#"
pub fn post_loop_read(v: &mut i32) -> i32 {
while *v < 10 {
    *v += 1;
}
*v
}
"#;

    let (_, loop_body) = analyze_function(source, "post_loop_read", &["v"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    assert!(
        loop_body.post_loop_deref_writes.is_empty(),
        "no post-loop deref writes should keep borrow-resolution vars unchanged"
    );
}

#[test]
fn extract_post_loop_deref_writes_tracks_reborrow_alias_write() {
    let source = r#"
pub fn post_loop_alias_write(v: &mut i32) -> i32 {
while *v < 10 {
    *v += 1;
}
let p = &mut *v;
*p = 42;
*p
}
"#;

    let (_, loop_body) = analyze_function(source, "post_loop_alias_write", &["v"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    assert!(
        loop_body.post_loop_deref_writes.contains("v"),
        "post-loop reborrow write should mark `v` for borrow-resolution gating"
    );
}

/// #2085: `extract_post_loop_deref_final_values` should resolve `*v = n`
/// after the loop to `{"v" -> Var("n")}`, providing the final_values needed
/// by `verify_mut_borrow_function_with_modes` when `extract_mut_borrow_body`
/// bails due to loop cycle detection.
#[test]
fn extract_post_loop_deref_final_values_resolves_param_write() {
    let source = r#"
pub fn set_after_loop(v: &mut i32, n: i32) -> i32 {
while *v < 10 {
    *v += 1;
}
*v = n;
*v
}
"#;

    let (_, loop_body) = analyze_function(source, "set_after_loop", &["v", "n"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    assert!(
        !loop_body.post_loop_deref_final_values.is_empty(),
        "post-loop deref final values should be extracted for `*v = n`"
    );
    let v_final = loop_body
        .post_loop_deref_final_values
        .get("v")
        .expect("final value for `v` should be extracted");
    // The final value should reference the parameter `n`.
    // Check by formatting — the expression should contain "n" as a variable.
    let debug_repr = format!("{v_final:?}");
    assert!(
        debug_repr.contains("\"n\""),
        "final value of `v` should reference `n`, got: {debug_repr}"
    );
}

/// #2085: When there are no post-loop deref writes, the final values map
/// should be empty.
#[test]
fn extract_post_loop_deref_final_values_empty_when_no_writes() {
    let source = r#"
pub fn post_loop_read(v: &mut i32) -> i32 {
while *v < 10 {
    *v += 1;
}
*v
}
"#;

    let (_, loop_body) = analyze_function(source, "post_loop_read", &["v"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    assert!(
        loop_body.post_loop_deref_final_values.is_empty(),
        "no post-loop deref writes means no final values to synthesize"
    );
}

/// #2085: When the post-loop CFG branches (SwitchInt), `extract_post_loop_deref_final_values`
/// must conservatively return an empty map. A branching post-loop path means we cannot
/// determine which branch will be taken, so last-write-wins is unsound — different branches
/// might write different values to `*x`. Flagged by P1-83 as over-approximation concern.
#[test]
fn extract_post_loop_deref_final_values_empty_on_branching_post_loop() {
    let source = r#"
pub fn branching_after_loop(v: &mut i32, n: i32, flag: bool) -> i32 {
while *v < 10 {
    *v += 1;
}
if flag {
    *v = n;
} else {
    *v = 0;
}
*v
}
"#;

    let (_, loop_body) = analyze_function(source, "branching_after_loop", &["v", "n", "flag"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    assert!(
        loop_body.post_loop_deref_final_values.is_empty(),
        "branching post-loop CFG should yield empty final_values (soundness guard); \
         got: {:?}",
        loop_body.post_loop_deref_final_values
    );
}

/// Regression test: while-let on a 3-variant enum must generate a condition
/// that only continues for the matched variant, not `discr != first_exit`.
/// Before fix (#1001), the condition was `discr != 0` which incorrectly
/// continued the loop for variant C (discriminant 2). (#1001)
#[test]
fn whilelet_condition_three_variant_enum() {
    let source = r#"
#[allow(dead_code)]
enum Three { A, B, C }

#[allow(dead_code)]
fn match_b(mut x: Three) -> i32 {
let mut count = 0;
while let Three::B = x {
    count += 1;
    x = Three::A;
}
count
}
"#;

    let (analysis, loop_body) = analyze_function(source, "match_b", &["x"]);
    assert!(analysis.has_loops, "expected loop detection");

    let loop_body = loop_body.expect("expected loop body extraction");
    let condition = loop_body
        .condition
        .expect("expected while-let condition extraction");

    // The condition must be `discriminant == 1` (Three::B),
    // NOT `discriminant != 0` (which would also match Three::C).
    // Accept either `discr == 1` directly or `(discr == 1)` wrapped.
    fn condition_accepts_only_variant_b(cond: &PureExpr) -> bool {
        match cond {
            // discr == 1 (equality with the body-continuing variant)
            PureExpr::BinOp(_, BinOp::Eq, rhs) if matches!(rhs.as_ref(), PureExpr::Int(1)) => true,
            // discr == 1 (left-associative, wrapped)
            PureExpr::BinOp(inner, BinOp::Or, _) => {
                condition_accepts_only_variant_b(inner.as_ref())
            }
            _ => false,
        }
    }
    assert!(
        condition_accepts_only_variant_b(&condition),
        "while-let on Three::B must generate `discr == 1`, got: {condition:?}"
    );

    // Negative check: the old buggy condition `discr != 0` must NOT be generated.
    let is_ne_zero = matches!(
        &condition,
        PureExpr::BinOp(_, BinOp::Ne, rhs) if matches!(rhs.as_ref(), PureExpr::Int(0))
    );
    assert!(
        !is_ne_zero,
        "REGRESSION: condition is `discr != 0` which is incorrect for 3-variant enums"
    );
}

/// While-let on a 2-variant enum (Option) should still produce a correct condition.
/// This is a regression guard for the common case. (#1001)
#[test]
fn whilelet_condition_two_variant_option() {
    let source = r#"
pub fn drain_option(mut x: Option<i32>) -> i32 {
let mut sum = 0;
while let Some(v) = x {
    sum += v;
    x = None;
}
sum
}
"#;

    let (analysis, loop_body) = analyze_function(source, "drain_option", &["x"]);
    assert!(analysis.has_loops, "expected loop detection");

    let loop_body = loop_body.expect("expected loop body extraction");
    let condition = loop_body
        .condition
        .expect("expected while-let condition for Option pattern");

    // For 2-variant Option, both `discr != 0` and `discr == 1` are semantically
    // correct. Verify the condition uses one of these forms (not a trivial `true`
    // or an incorrect variant index).
    let is_valid_2variant_condition = matches!(
        &condition,
        PureExpr::BinOp(_, BinOp::Ne, rhs) if matches!(rhs.as_ref(), PureExpr::Int(0))
    ) || matches!(
        &condition,
        PureExpr::BinOp(_, BinOp::Eq, rhs) if matches!(rhs.as_ref(), PureExpr::Int(1))
    );
    assert!(
        is_valid_2variant_condition,
        "expected `discr != 0` or `discr == 1` for 2-variant Option, got: {condition:?}"
    );
}

#[test]
fn switch_target_value_to_i64_none_discr_ty_large_value_returns_none() {
    let value = (i64::MAX as u128) + 1;
    assert_eq!(switch_target_value_to_i64(value, None), None);
}

#[test]
fn extract_body_effects_opaque_condition_preserves_common_effects() {
    // When a loop body branches on an opaque Call result (e.g., `check(i)`),
    // the discriminant can't be translated. The conservative merge should
    // still capture effects that occur on ALL branches (like `i += 1`).
    // This pattern matches `if v.len() > i { v[i] = 0; } i += 1;` in
    // the inferred_invariants/y test. (#1295)
    let source = r#"
fn check(x: i32) -> bool { x > 0 }

pub fn opaque_branch_common_effect(n: i32) -> i32 {
let mut i = 0;
while i < n {
    if check(i) {
        // Side-effecting branch — but i is not modified here
    }
    i += 1;
}
i
}
"#;

    let (_, loop_body) = analyze_function(source, "opaque_branch_common_effect", &["n"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    let effect = loop_body
        .body_effects
        .get("i")
        .expect("expected body effect for i despite opaque branch condition");
    expect_i_plus(effect, 1);
}
