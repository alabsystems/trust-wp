// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ---- Call-result modeling tests (#1463) ----

/// Spec entry: maps a callee function name to a StdSpec with ensures clauses.
struct SpecEntry {
    callee_name: String,
    spec: StdSpec,
}

fn is_int_or_view_int(expr: &PureExpr, value: i64) -> bool {
    match expr {
        PureExpr::Int(n) => *n == value,
        PureExpr::View(inner) => is_int_or_view_int(inner.as_ref(), value),
        _ => false,
    }
}

fn is_len_of_var(expr: &PureExpr, var: &str) -> bool {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = expr
    else {
        return false;
    };
    if method != "len" || !args.is_empty() {
        return false;
    }

    match receiver.as_ref() {
        PureExpr::Var(name, _) => name == var,
        PureExpr::View(inner) => matches!(inner.as_ref(), PureExpr::Var(name, _) if name == var),
        _ => false,
    }
}

fn is_len_eq_int(expr: &PureExpr, var: &str, value: i64) -> bool {
    match expr {
        PureExpr::BinOp(lhs, BinOp::Eq, rhs) => {
            (is_len_of_var(lhs, var) && is_int_or_view_int(rhs, value))
                || (is_int_or_view_int(lhs, value) && is_len_of_var(rhs, var))
        }
        _ => false,
    }
}

struct SpecLoopCallbacks {
    fn_name: String,
    arg_names: Vec<String>,
    spec_entries: Vec<SpecEntry>,
    analysis: Option<LoopAnalysis>,
    loop_body: Option<LoopBodyExpr>,
    loop_bodies: Vec<LoopBodyExpr>,
    ran: bool,
}

impl Callbacks for SpecLoopCallbacks {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let suffix = format!("::{}", self.fn_name);

        // Build DefId → StdSpec map by resolving callee names.
        let mut user_specs: HashMap<DefId, StdSpec> = HashMap::new();
        for entry in &self.spec_entries {
            let callee_suffix = format!("::{}", entry.callee_name);
            for local_def_id in tcx.hir_body_owners() {
                let def_path = tcx.def_path_str(local_def_id);
                if def_path == entry.callee_name || def_path.ends_with(&callee_suffix) {
                    user_specs.insert(local_def_id.to_def_id(), entry.spec.clone());
                    break;
                }
            }
        }

        let trait_specs: HashMap<DefId, StdSpec> = HashMap::new();

        for local_def_id in tcx.hir_body_owners() {
            let def_path = tcx.def_path_str(local_def_id);
            if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                continue;
            }

            let body = tcx.optimized_mir(local_def_id.to_def_id());
            let analysis = detect_loops(body);
            let extern_specs = std::collections::HashMap::new();
            let call_spec_ctx = CallSpecContext {
                tcx,
                user_specs: &user_specs,
                trait_specs: &trait_specs,
                extern_specs: &extern_specs,
            };
            let loop_bodies: Vec<LoopBodyExpr> = analysis
                .loops
                .iter()
                .map(|loop_info| {
                    extract_loop_body(
                        body,
                        &self.arg_names,
                        loop_info,
                        Some(&analysis.loops),
                        Some(&call_spec_ctx),
                    )
                })
                .collect();
            let loop_body = loop_bodies.first().cloned();

            self.analysis = Some(analysis);
            self.loop_body = loop_body;
            self.loop_bodies = loop_bodies;
            self.ran = true;
            break;
        }

        Compilation::Stop
    }
}

fn analyze_function_with_specs(
    source: &str,
    fn_name: &str,
    arg_names: &[&str],
    spec_entries: Vec<SpecEntry>,
) -> (LoopAnalysis, Option<LoopBodyExpr>) {
    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_loop_spec_{}_{}",
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

    let mut callbacks = SpecLoopCallbacks {
        fn_name: fn_name.to_string(),
        arg_names: arg_names.iter().map(|name| (*name).to_string()).collect(),
        spec_entries,
        analysis: None,
        loop_body: None,
        loop_bodies: Vec::new(),
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

fn analyze_all_loops_with_specs(
    source: &str,
    fn_name: &str,
    arg_names: &[&str],
    spec_entries: Vec<SpecEntry>,
) -> (LoopAnalysis, Vec<LoopBodyExpr>) {
    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_loop_spec_all_{}_{}",
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

    let mut callbacks = SpecLoopCallbacks {
        fn_name: fn_name.to_string(),
        arg_names: arg_names.iter().map(|name| (*name).to_string()).collect(),
        spec_entries,
        analysis: None,
        loop_body: None,
        loop_bodies: Vec::new(),
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
        callbacks.loop_bodies,
    )
}

struct RangeBoundsCallbacks {
    fn_name: String,
    arg_names: Vec<String>,
    range_bounds: Option<(PureExpr, PureExpr)>,
    ran: bool,
}

impl Callbacks for RangeBoundsCallbacks {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let suffix = format!("::{}", self.fn_name);

        for local_def_id in tcx.hir_body_owners() {
            let def_path = tcx.def_path_str(local_def_id);
            if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                continue;
            }

            let body = tcx.optimized_mir(local_def_id.to_def_id());
            let analysis = detect_loops(body);
            let preds = super::super::detection::predecessor_map(body);
            let user_specs: HashMap<DefId, StdSpec> = HashMap::new();
            let trait_specs: HashMap<DefId, StdSpec> = HashMap::new();
            let extern_specs: HashMap<String, StdSpec> = HashMap::new();
            let spec_ctx = CallSpecContext {
                tcx,
                user_specs: &user_specs,
                trait_specs: &trait_specs,
                extern_specs: &extern_specs,
            };

            for loop_info in &analysis.loops {
                let Some((call_block, _)) =
                    super::super::for_loop_iter::resolve_for_loop_next_call(body, loop_info)
                else {
                    continue;
                };
                let header_data = &body.basic_blocks[call_block];
                let TerminatorKind::Call { args, .. } = &header_data.terminator().kind else {
                    continue;
                };
                let Some(next_arg) = args.first() else {
                    continue;
                };
                let Some(iterator_local) =
                    super::super::for_loop_iter::resolve_iterator_local_from_next_arg(
                        next_arg,
                        &header_data.statements,
                    )
                else {
                    continue;
                };

                let mut local_exprs: HashMap<Local, PureExpr> = HashMap::new();
                let mut local_to_name: HashMap<Local, String> = HashMap::new();
                let param_locals: std::collections::HashSet<Local> = (0..self.arg_names.len())
                    .map(|i| Local::from_usize(i + 1))
                    .collect();

                for (i, name) in self.arg_names.iter().enumerate() {
                    let local = Local::from_usize(i + 1);
                    local_exprs.insert(local, PureExpr::Var(name.clone(), None));
                    local_to_name.insert(local, name.clone());
                }

                for var_debug in &body.var_debug_info {
                    if let rustc_middle::mir::VarDebugInfoContents::Place(place) = &var_debug.value
                    {
                        if place.projection.is_empty() && !param_locals.contains(&place.local) {
                            let name = var_debug.name.to_string();
                            local_exprs.insert(place.local, PureExpr::Var(name.clone(), None));
                            local_to_name.insert(place.local, name);
                        }
                    }
                }

                let (_, unresolved_pre_loop_calls, _, ref_source_locals) =
                    super::super::pre_loop_extract::extract_pre_loop_assignments(
                        body,
                        &self.arg_names,
                        loop_info,
                        Some(tcx),
                    );
                for (local, expr) in
                    super::super::pre_loop_resolve::resolve_pre_loop_call_locals_with_spec_ctx(
                        &spec_ctx,
                        &unresolved_pre_loop_calls,
                        &ref_source_locals,
                    )
                {
                    local_exprs.insert(local, expr);
                }
                super::super::populate_pre_loop_temps(
                    body,
                    loop_info,
                    &local_to_name,
                    &mut local_exprs,
                );

                let recovered = super::super::for_range::recover_range_bounds(
                    body,
                    loop_info,
                    call_block,
                    iterator_local,
                    &local_exprs,
                    &preds,
                );
                if let Some(range_bounds) = recovered {
                    self.range_bounds = Some(range_bounds);
                    break;
                }
            }

            self.ran = true;
            break;
        }

        Compilation::Stop
    }
}

fn recover_range_bounds_with_rustc_args(
    source: &str,
    fn_name: &str,
    arg_names: &[&str],
    extra_rustc_args: &[&str],
) -> Option<(PureExpr, PureExpr)> {
    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_loop_range_{}_{}",
        std::process::id(),
        unique
    ));
    fs::create_dir_all(&temp_dir).expect("create test temp dir");

    let source_path = temp_dir.join("test.rs");
    fs::write(&source_path, source).expect("write test source");

    let mut args = vec![
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
    args.extend(extra_rustc_args.iter().map(|arg| (*arg).to_string()));

    let mut callbacks = RangeBoundsCallbacks {
        fn_name: fn_name.to_string(),
        arg_names: arg_names.iter().map(|name| (*name).to_string()).collect(),
        range_bounds: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to locate function `{fn_name}` in rustc callback"
    );

    callbacks.range_bounds
}

struct LoopObligationCallbacks {
    fn_name: String,
    arg_names: Vec<String>,
    spec_entries: Vec<SpecEntry>,
    obligation_groups: Option<Vec<Vec<PureExpr>>>,
    ran: bool,
}

impl Callbacks for LoopObligationCallbacks {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let suffix = format!("::{}", self.fn_name);

        let mut user_specs: HashMap<DefId, StdSpec> = HashMap::new();
        for entry in &self.spec_entries {
            let callee_suffix = format!("::{}", entry.callee_name);
            for local_def_id in tcx.hir_body_owners() {
                let def_path = tcx.def_path_str(local_def_id);
                if def_path == entry.callee_name || def_path.ends_with(&callee_suffix) {
                    user_specs.insert(local_def_id.to_def_id(), entry.spec.clone());
                    break;
                }
            }
        }

        let trait_specs: HashMap<DefId, StdSpec> = HashMap::new();
        let extern_specs = HashMap::new();

        for local_def_id in tcx.hir_body_owners() {
            let def_path = tcx.def_path_str(local_def_id);
            if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                continue;
            }

            let body = tcx.optimized_mir(local_def_id.to_def_id());
            let analysis = detect_loops(body);
            let groups = analysis
                .loops
                .iter()
                .map(|loop_info| {
                    let mut exclusive_blocks = loop_info.body_blocks.clone();
                    for other in &analysis.loops {
                        if other.header != loop_info.header
                            && loop_info.body_blocks.contains(&other.header)
                        {
                            for bb in &other.body_blocks {
                                if *bb != other.header {
                                    exclusive_blocks.remove(bb);
                                }
                            }
                        }
                    }
                    let name_restore_blocks = {
                        let mut blocks = loop_info.body_blocks.clone();
                        for other in &analysis.loops {
                            if other.header != loop_info.header
                                && other.body_blocks.contains(&loop_info.header)
                            {
                                blocks.extend(other.body_blocks.iter().copied());
                            }
                        }
                        blocks
                    };
                    {
                        let loop_spec_ctx = LoopBodySpecContext {
                            user_specs: &user_specs,
                            trait_specs: &trait_specs,
                            extern_specs: &extern_specs,
                            body_blocks: &exclusive_blocks,
                            name_restore_blocks: Some(&name_restore_blocks),
                            arithmetic: None,
                            all_loops: Some(&analysis.loops),
                            condition_switch: None,
                        };
                        collect_loop_body_call_obligations(
                            tcx,
                            body,
                            &self.arg_names,
                            loop_info.header,
                            &loop_spec_ctx,
                        )
                    }
                })
                .collect();

            self.obligation_groups = Some(groups);
            self.ran = true;
            break;
        }

        Compilation::Stop
    }
}

fn collect_loop_obligation_groups_with_specs(
    source: &str,
    fn_name: &str,
    arg_names: &[&str],
    spec_entries: Vec<SpecEntry>,
) -> Vec<Vec<PureExpr>> {
    let unique = TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_loop_obligations_{}_{}",
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
        "trust_wp_loop_obligation_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = LoopObligationCallbacks {
        fn_name: fn_name.to_string(),
        arg_names: arg_names.iter().map(|name| (*name).to_string()).collect(),
        spec_entries,
        obligation_groups: None,
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
        .obligation_groups
        .expect("loop obligation groups should be collected")
}

/// When a spec provides `result == x + 1`, the call destination should be
/// modeled as `x + 1` instead of being havoced. (#1463)
#[test]
fn call_result_modeled_with_ensures_spec() {
    let source = r#"
#[inline(never)]
fn inc(x: i32) -> i32 {
x + 1
}

pub fn loop_with_specced_call(n: i32) -> i32 {
let mut i = 0;
while i < n {
    i = inc(i);
}
i
}
"#;
    let spec = StdSpec {
        capture_inv_requires: Vec::new(),
        inv_requires: Vec::new(),
        requires: vec![],
        ensures: vec!["result == x + 1".to_string()],
        param_names: Some(vec!["x".to_string()]),
    };

    let (_, loop_body) = analyze_function_with_specs(
        source,
        "loop_with_specced_call",
        &["n"],
        vec![SpecEntry {
            callee_name: "inc".to_string(),
            spec,
        }],
    );
    let loop_body = loop_body.expect("expected loop body extraction");
    let effect = loop_body
        .body_effects
        .get("i")
        .expect("call result should be modeled, not havoced");

    // The effect should be i + 1 (postcondition applied with i substituted for x).
    expect_i_plus(effect, 1);
}

#[test]
fn pre_loop_call_predicate_postcondition_becomes_init_fact() {
    let source = r#"
#[inline(never)]
fn make_vec(count: usize) -> Vec<i32> {
    let _ = count;
    Vec::new()
}

pub fn loop_with_pre_loop_vec_len_spec() {
    let mut door_open: Vec<i32> = make_vec(100);
    for pass in 1usize..101usize {
        if pass == 0 {
            door_open.push(1);
        }
    }
}
"#;
    let spec = StdSpec {
        capture_inv_requires: Vec::new(),
        inv_requires: Vec::new(),
        requires: vec![],
        ensures: vec!["result@.len() == count@".to_string()],
        param_names: Some(vec!["count".to_string()]),
    };

    let (_, loop_body) = analyze_function_with_specs(
        source,
        "loop_with_pre_loop_vec_len_spec",
        &[],
        vec![SpecEntry {
            callee_name: "make_vec".to_string(),
            spec,
        }],
    );
    let loop_body = loop_body.expect("expected loop body extraction");

    assert!(
        loop_body
            .pre_loop_init_facts
            .iter()
            .any(|fact| is_len_eq_int(fact, "door_open", 100)),
        "expected door_open@.len() == 100 init fact, got {:?}",
        loop_body.pre_loop_init_facts
    );
}

#[test]
fn for_loop_over_call_result_carries_source_postconditions_to_init_facts() {
    let source = r#"
#[inline(never)]
fn moves() -> Vec<(i32, i32)> {
    Vec::new()
}

#[inline(never)]
fn require_move(_m: (i32, i32)) {}

pub fn loop_over_moves() {
    for m in moves() {
        require_move(m);
    }
}
"#;
    let moves_spec = StdSpec {
        capture_inv_requires: Vec::new(),
        inv_requires: Vec::new(),
        requires: vec![],
        ensures: vec![
            "result@.len() == 8".to_string(),
            "forall<i> 0 <= i && i < 8 ==> 0 <= result[i].0@".to_string(),
        ],
        param_names: Some(vec![]),
    };

    let (_, loop_body) = analyze_function_with_specs(
        source,
        "loop_over_moves",
        &[],
        vec![SpecEntry {
            callee_name: "moves".to_string(),
            spec: moves_spec,
        }],
    );
    let loop_body = loop_body.expect("expected loop body extraction");
    let init_debug = format!("{:?}", loop_body.pre_loop_init_facts);

    assert!(
        init_debug.contains("len") && init_debug.contains("Int(8)"),
        "moves() result length postcondition should become a loop init fact, got {init_debug}"
    );
    assert!(
        init_debug.contains("Forall") && init_debug.contains("index_logic"),
        "moves() quantified element postcondition should become a loop init fact, got {init_debug}"
    );
    assert!(
        loop_body.for_loop_state.is_some(),
        "for-loop state should be available for the moves() iterator"
    );
}

#[test]
fn for_loop_over_named_call_result_still_carries_source_postconditions() {
    let source = r#"
#[inline(never)]
fn moves() -> Vec<(i32, i32)> {
    Vec::new()
}

#[inline(never)]
fn require_move(_m: (i32, i32)) {}

pub fn loop_over_named_moves() {
    let iter = moves();
    for m in iter {
        require_move(m);
    }
}
"#;
    let moves_spec = StdSpec {
        capture_inv_requires: Vec::new(),
        inv_requires: Vec::new(),
        requires: vec![],
        ensures: vec![
            "result@.len() == 8".to_string(),
            "forall<i> 0 <= i && i < 8 ==> 0 <= result[i].0@".to_string(),
        ],
        param_names: Some(vec![]),
    };

    let (_, loop_body) = analyze_function_with_specs(
        source,
        "loop_over_named_moves",
        &[],
        vec![SpecEntry {
            callee_name: "moves".to_string(),
            spec: moves_spec,
        }],
    );
    let loop_body = loop_body.expect("expected loop body extraction");
    let init_debug = format!("{:?}", loop_body.pre_loop_init_facts);

    assert!(
        init_debug.contains("len") && init_debug.contains("Int(8)"),
        "named moves() result length postcondition should become a loop init fact, got {init_debug}"
    );
    assert!(
        init_debug.contains("Forall") && init_debug.contains("index_logic"),
        "named moves() quantified element postcondition should become a loop init fact, got {init_debug}"
    );
}

#[test]
fn nested_for_loop_over_call_result_carries_source_postconditions_to_inner_loop() {
    let source = r#"
#[inline(never)]
fn moves() -> Vec<(i32, i32)> {
    Vec::new()
}

#[inline(never)]
fn require_move(_m: (i32, i32)) {}

pub fn nested_loop_over_moves(n: usize) {
    for _step in 0..n {
        for m in moves() {
            require_move(m);
        }
    }
}
"#;
    let moves_spec = StdSpec {
        capture_inv_requires: Vec::new(),
        inv_requires: Vec::new(),
        requires: vec![],
        ensures: vec![
            "result@.len() == 8".to_string(),
            "forall<i> 0 <= i && i < 8 ==> 0 <= result[i].0@".to_string(),
        ],
        param_names: Some(vec![]),
    };

    let (_, loop_bodies) = analyze_all_loops_with_specs(
        source,
        "nested_loop_over_moves",
        &["n"],
        vec![SpecEntry {
            callee_name: "moves".to_string(),
            spec: moves_spec,
        }],
    );
    let inner_moves_loop = loop_bodies
        .iter()
        .find(|loop_body| {
            matches!(
                loop_body.for_loop_state.as_ref().map(|state| &state.loop_elem),
                Some(PureExpr::Var(name, _)) if name == "m"
            )
        })
        .expect("expected inner for m in moves() loop body");
    let init_debug = format!("{:?}", inner_moves_loop.pre_loop_init_facts);

    assert!(
        init_debug.contains("len") && init_debug.contains("Int(8)"),
        "nested moves() result length postcondition should reach the inner loop, got {init_debug}"
    );
    assert!(
        init_debug.contains("Forall") && init_debug.contains("index_logic"),
        "nested moves() quantified element postcondition should reach the inner loop, got {init_debug}"
    );
}

#[test]
fn deref_write_ite_alias_split_preserves_typed_current_branch_values() {
    let source = r#"
#[inline(never)]
fn take_max<'a>(ma: &'a mut u32, mb: &'a mut u32) -> &'a mut u32 {
    if *ma >= *mb { ma } else { mb }
}

pub fn loop_updates_max(n: u32, mut a: u32, mut b: u32) -> u32 {
    let mut i = 0;
    while i < n {
        let mc = take_max(&mut a, &mut b);
        *mc += 1;
        i += 1;
    }
    a + b
}
"#;
    let spec = StdSpec {
        capture_inv_requires: Vec::new(),
        inv_requires: Vec::new(),
        requires: vec![],
        ensures: vec![
            "if *ma >= *mb { *mb == ^mb && result == ma } else { *ma == ^ma && result == mb }"
                .to_string(),
        ],
        param_names: Some(vec!["ma".to_string(), "mb".to_string()]),
    };

    let (_, loop_body) = analyze_function_with_specs(
        source,
        "loop_updates_max",
        &["n", "a", "b"],
        vec![SpecEntry {
            callee_name: "take_max".to_string(),
            spec,
        }],
    );
    let loop_body = loop_body.expect("expected loop body extraction");

    let a_effect = loop_body
        .body_effects
        .get("a")
        .expect("conditional deref write should update a");
    let b_effect = loop_body
        .body_effects
        .get("b")
        .expect("conditional deref write should update b");

    match a_effect {
        PureExpr::Ite(_, then_expr, else_expr) => {
            assert!(
                matches!(
                    then_expr.as_ref(),
                    PureExpr::BinOp(lhs, BinOp::Add, rhs)
                        if matches!(lhs.as_ref(), PureExpr::Var(name, Some(ExprSort::Int)) if name == "a")
                            && matches!(rhs.as_ref(), PureExpr::Int(1))
                ),
                "then branch should increment typed a, got {then_expr:?}"
            );
            assert!(
                matches!(
                    else_expr.as_ref(),
                    PureExpr::Var(name, Some(ExprSort::Int)) if name == "a"
                ),
                "else branch should keep typed a, got {else_expr:?}"
            );
        }
        other => panic!("expected conditional a effect, got {other:?}"),
    }

    match b_effect {
        PureExpr::Ite(_, then_expr, else_expr) => {
            assert!(
                matches!(
                    then_expr.as_ref(),
                    PureExpr::Var(name, Some(ExprSort::Int)) if name == "b"
                ),
                "then branch should keep typed b, got {then_expr:?}"
            );
            assert!(
                matches!(
                    else_expr.as_ref(),
                    PureExpr::BinOp(lhs, BinOp::Add, rhs)
                        if matches!(lhs.as_ref(), PureExpr::Var(name, Some(ExprSort::Int)) if name == "b")
                            && matches!(rhs.as_ref(), PureExpr::Int(1))
                ),
                "else branch should increment typed b, got {else_expr:?}"
            );
        }
        other => panic!("expected conditional b effect, got {other:?}"),
    }
}

#[test]
fn nested_loop_obligations_use_exclusive_body_blocks() {
    let source = r#"
#[inline(never)]
fn require_outer(_i: i32, _n: i32) {}

#[inline(never)]
fn require_inner(_j: i32, _m: i32) {}

pub fn nested_loop_obligations(n: i32, m: i32) {
    let mut i = 0;
    while i < n {
        require_outer(i, n);
        let mut j = 0;
        while j < m {
            require_inner(j, m);
            j += 1;
        }
        i += 1;
    }
}
"#;

    let groups = collect_loop_obligation_groups_with_specs(
        source,
        "nested_loop_obligations",
        &["n", "m"],
        vec![
            SpecEntry {
                callee_name: "require_outer".to_string(),
                spec: StdSpec {
                    capture_inv_requires: Vec::new(),
                    inv_requires: Vec::new(),
                    requires: vec!["i < n".to_string()],
                    ensures: vec![],
                    param_names: Some(vec!["i".to_string(), "n".to_string()]),
                },
            },
            SpecEntry {
                callee_name: "require_inner".to_string(),
                spec: StdSpec {
                    capture_inv_requires: Vec::new(),
                    inv_requires: Vec::new(),
                    requires: vec!["j < m".to_string()],
                    ensures: vec![],
                    param_names: Some(vec!["j".to_string(), "m".to_string()]),
                },
            },
        ],
    );

    let expected_outer_guard = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), Some(ExprSort::Int))),
        BinOp::Lt,
        Arc::new(PureExpr::Var("n".to_string(), Some(ExprSort::Int))),
    );
    let expected_inner_guard = PureExpr::BinOp(
        Arc::new(PureExpr::Var("j".to_string(), Some(ExprSort::Int))),
        BinOp::Lt,
        Arc::new(PureExpr::Var("m".to_string(), Some(ExprSort::Int))),
    );
    let expected_outer_atom = PureExpr::BinOp(
        Arc::new(PureExpr::Var("i".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Var("n".to_string(), None)),
    );
    let expected_inner_atom = PureExpr::BinOp(
        Arc::new(PureExpr::Var("j".to_string(), None)),
        BinOp::Lt,
        Arc::new(PureExpr::Var("m".to_string(), None)),
    );
    let expected_outer = vec![PureExpr::BinOp(
        Arc::new(expected_outer_guard),
        BinOp::Implies,
        Arc::new(expected_outer_atom),
    )];
    let expected_inner = vec![PureExpr::BinOp(
        Arc::new(expected_inner_guard),
        BinOp::Implies,
        Arc::new(expected_inner_atom),
    )];

    assert_eq!(
        groups.len(),
        2,
        "expected exactly outer and inner loop obligation groups, got {groups:?}"
    );
    assert!(
        groups.iter().all(|group| group.len() == 1),
        "exclusive body blocks should keep each loop's obligations isolated, got {groups:?}"
    );
    assert!(
        groups.iter().any(|group| group == &expected_outer),
        "outer loop should keep only its own obligation, got {groups:?}"
    );
    assert!(
        groups.iter().any(|group| group == &expected_inner),
        "inner loop should keep only its own obligation, got {groups:?}"
    );
}

#[test]
fn nested_loop_obligations_restore_enclosing_loop_carried_names() {
    let source = r#"
#[derive(Copy, Clone)]
pub struct Point {
    pub x: i32,
    pub y: i32,
}

#[inline(never)]
fn require_point(p: Point) {
    let _ = p;
}

pub fn nested_loop_carries_point(n: i32) {
    let mut p = Point { x: 0, y: 0 };
    let mut outer = 0;
    while outer < n {
        let mut inner = 0;
        while inner < n {
            require_point(p);
            inner += 1;
        }
        p = Point { x: outer, y: inner };
        outer += 1;
    }
}
"#;

    let groups = collect_loop_obligation_groups_with_specs(
        source,
        "nested_loop_carries_point",
        &["n"],
        vec![SpecEntry {
            callee_name: "require_point".to_string(),
            spec: StdSpec {
                capture_inv_requires: Vec::new(),
                inv_requires: Vec::new(),
                requires: vec!["p == p".to_string()],
                ensures: vec![],
                param_names: Some(vec!["p".to_string()]),
            },
        }],
    );

    let obligations: Vec<&PureExpr> = groups.iter().flatten().collect();
    assert_eq!(
        obligations.len(),
        1,
        "expected one inner-loop call obligation, got {groups:?}"
    );

    let obligation_debug = format!("{:?}", obligations[0]);
    assert!(
        obligation_debug.contains("Var(\"p\""),
        "inner-loop obligation should use symbolic outer-loop-carried `p`, got {obligation_debug}"
    );
    assert!(
        !obligation_debug.contains("name: \"Point\""),
        "inner-loop obligation should not use pre-outer-loop Point initializer, got {obligation_debug}"
    );
}

#[test]
fn loop_obligations_restore_loop_carried_names_for_call_destinations() {
    let source = r#"
#[inline(never)]
fn passthrough(x: i32) -> i32 {
    x
}

#[inline(never)]
fn require_lt(j: i32, n: i32) {
    let _ = (j, n);
}

pub fn loop_carries_call_assigned_local(i: i32, n: i32) {
    let mut j = i;
    while j < n {
        require_lt(j, n);
        j = passthrough(j);
    }
}
"#;

    let groups = collect_loop_obligation_groups_with_specs(
        source,
        "loop_carries_call_assigned_local",
        &["i", "n"],
        vec![SpecEntry {
            callee_name: "require_lt".to_string(),
            spec: StdSpec {
                capture_inv_requires: Vec::new(),
                inv_requires: Vec::new(),
                requires: vec!["j < n".to_string()],
                ensures: vec![],
                param_names: Some(vec!["j".to_string(), "n".to_string()]),
            },
        }],
    );

    assert_eq!(groups.len(), 1, "expected a single loop obligation group");
    assert_eq!(
        groups[0].len(),
        1,
        "expected one obligation, got {groups:?}"
    );
    match &groups[0][0] {
        PureExpr::BinOp(guard, BinOp::Implies, obligation) => {
            assert!(
                matches!(
                    guard.as_ref(),
                    PureExpr::BinOp(lhs, BinOp::Lt, rhs)
                        if matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == "j")
                            && matches!(rhs.as_ref(), PureExpr::Var(name, _) if name == "n")
                ),
                "loop guard should stay `j < n`, got {guard:?}"
            );
            let PureExpr::BinOp(lhs, BinOp::Lt, rhs) = obligation.as_ref() else {
                panic!("expected guarded `j < n` obligation, got {obligation:?}");
            };
            assert!(
                matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == "j"),
                "loop-carried local should stay symbolic as j, got {lhs:?}"
            );
            assert!(
                matches!(rhs.as_ref(), PureExpr::Var(name, _) if name == "n"),
                "obligation should keep n on the rhs, got {rhs:?}"
            );
        }
        other => panic!("expected guarded `j < n` obligation, got {other:?}"),
    }
}

/// `collect_guarded_obligations` models specced call-destination results.
/// When `j = inc(j); require_positive(j);` compiles to MIR where the call
/// writes directly to j's local, the obligation for `require_positive`
/// must use the postcondition-derived result `j + 1`.
#[test]
fn loop_obligations_use_specced_call_results_for_later_calls() {
    let source = r#"
#[inline(never)]
fn inc(x: i32) -> i32 {
    x + 1
}

#[inline(never)]
fn require_positive(x: i32) {
    let _ = x;
}

pub fn loop_call_result_feeds_next_obligation(n: i32) {
    let mut j = 0;
    while j < n {
        j = inc(j);
        require_positive(j);
    }
}
"#;

    let groups = collect_loop_obligation_groups_with_specs(
        source,
        "loop_call_result_feeds_next_obligation",
        &["n"],
        vec![
            SpecEntry {
                callee_name: "inc".to_string(),
                spec: StdSpec {
                    capture_inv_requires: Vec::new(),
                    inv_requires: Vec::new(),
                    requires: vec![],
                    ensures: vec!["result == x + 1".to_string()],
                    param_names: Some(vec!["x".to_string()]),
                },
            },
            SpecEntry {
                callee_name: "require_positive".to_string(),
                spec: StdSpec {
                    capture_inv_requires: Vec::new(),
                    inv_requires: Vec::new(),
                    requires: vec!["x > 0".to_string()],
                    ensures: vec![],
                    param_names: Some(vec!["x".to_string()]),
                },
            },
        ],
    );

    assert_eq!(groups.len(), 1, "expected a single loop obligation group");
    assert_eq!(
        groups[0].len(),
        1,
        "expected one obligation, got {groups:?}"
    );
    match &groups[0][0] {
        PureExpr::BinOp(guard, BinOp::Implies, obligation) => {
            let guard_debug = format!("{guard:?}");
            assert!(
                guard_debug.contains("Lt")
                    && guard_debug.contains("\"j\"")
                    && guard_debug.contains("\"n\""),
                "loop guard should stay `j < n`, got {guard:?}"
            );
            let PureExpr::BinOp(lhs, BinOp::Gt, rhs) = obligation.as_ref() else {
                panic!("expected guarded positive obligation, got {obligation:?}");
            };
            assert!(
                matches!(rhs.as_ref(), PureExpr::Int(0)),
                "positive obligation should compare against 0, got {rhs:?}"
            );
            assert!(
                matches!(
                    lhs.as_ref(),
                    PureExpr::BinOp(base, BinOp::Add, delta)
                        if matches!(base.as_ref(), PureExpr::Var(name, _) if name == "j")
                            && matches!(delta.as_ref(), PureExpr::Int(1))
                ),
                "obligation lhs should use specced call result `j + 1`; got {lhs:?}"
            );
        }
        other => panic!("expected guarded `j > 0` obligation, got {other:?}"),
    }
}

#[test]
fn loop_obligations_carry_bool_call_postcondition_to_guarded_later_call() {
    let source = r#"
#[inline(never)]
fn available(p: i32) -> bool {
    p > 0
}

#[inline(never)]
fn require_positive(x: i32) {
    let _ = x;
}

pub fn guarded_call_uses_available_postcondition(n: i32) {
    let mut i = 0;
    while i < n {
        let adj = i;
        if available(adj) {
            require_positive(adj);
        }
        i += 1;
    }
}
"#;

    let groups = collect_loop_obligation_groups_with_specs(
        source,
        "guarded_call_uses_available_postcondition",
        &["n"],
        vec![
            SpecEntry {
                callee_name: "available".to_string(),
                spec: StdSpec {
                    capture_inv_requires: Vec::new(),
                    inv_requires: Vec::new(),
                    requires: vec![],
                    ensures: vec!["result ==> p > 0".to_string()],
                    param_names: Some(vec!["p".to_string()]),
                },
            },
            SpecEntry {
                callee_name: "require_positive".to_string(),
                spec: StdSpec {
                    capture_inv_requires: Vec::new(),
                    inv_requires: Vec::new(),
                    requires: vec!["x > 0".to_string()],
                    ensures: vec![],
                    param_names: Some(vec!["x".to_string()]),
                },
            },
        ],
    );

    assert_eq!(groups.len(), 1, "expected a single loop obligation group");
    assert_eq!(
        groups[0].len(),
        1,
        "expected only the guarded require_positive obligation, got {groups:?}"
    );

    let obligation = &groups[0][0];
    let debug = format!("{obligation:?}");
    assert!(
        debug.contains("Implies") && debug.contains("call_") && debug.contains("Gt"),
        "guard should include available result and its postcondition, got {obligation:?}"
    );
}

#[test]
fn loop_obligations_carry_call_postconditions_into_later_guarded_obligations() {
    let source = r#"
#[derive(Copy, Clone)]
pub struct Board;

#[derive(Copy, Clone)]
pub struct Point;

#[inline(never)]
fn available(b: Board, p: Point) -> bool {
    let _ = (b, p);
    true
}

#[inline(never)]
fn count_degree(b: Board, p: Point) {
    let _ = (b, p);
}

pub fn loop_available_guards_count_degree(n: i32, board: Board, adj: Point) {
    let mut i = 0;
    while i < n {
        if available(board, adj) {
            count_degree(board, adj);
        }
        i += 1;
    }
}
"#;

    let groups = collect_loop_obligation_groups_with_specs(
        source,
        "loop_available_guards_count_degree",
        &["n", "board", "adj"],
        vec![
            SpecEntry {
                callee_name: "available".to_string(),
                spec: StdSpec {
                    capture_inv_requires: Vec::new(),
                    inv_requires: Vec::new(),
                    requires: vec![],
                    ensures: vec!["result ==> b.in_bounds(p)".to_string()],
                    param_names: Some(vec!["b".to_string(), "p".to_string()]),
                },
            },
            SpecEntry {
                callee_name: "count_degree".to_string(),
                spec: StdSpec {
                    capture_inv_requires: Vec::new(),
                    inv_requires: Vec::new(),
                    requires: vec!["b.in_bounds(p)".to_string()],
                    ensures: vec![],
                    param_names: Some(vec!["b".to_string(), "p".to_string()]),
                },
            },
        ],
    );

    assert_eq!(groups.len(), 1, "expected a single loop obligation group");
    assert_eq!(
        groups[0].len(),
        1,
        "expected count_degree precondition obligation, got {groups:?}"
    );

    let PureExpr::BinOp(guard, BinOp::Implies, obligation) = &groups[0][0] else {
        panic!(
            "expected guarded count_degree obligation, got {:?}",
            groups[0][0]
        );
    };
    assert!(
        contains_board_in_bounds(guard),
        "guard should carry available's postcondition assumption, got {guard:?}"
    );
    assert!(
        contains_board_in_bounds(obligation),
        "obligation should be count_degree's in_bounds precondition, got {obligation:?}"
    );
}

fn contains_board_in_bounds(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            method == "in_bounds"
                && (matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "board")
                    || matches!(receiver.as_ref(), PureExpr::Var(name, _)
                        if name.starts_with("$fallback_arg0_")))
                && (matches!(args.first(), Some(PureExpr::Var(name, _)) if name == "adj")
                    || matches!(args.first(), Some(PureExpr::Var(name, _))
                        if name.starts_with("$fallback_arg1_")))
        }
        PureExpr::BinOp(lhs, _, rhs) => {
            contains_board_in_bounds(lhs) || contains_board_in_bounds(rhs)
        }
        PureExpr::UnOp(_, inner)
        | PureExpr::Deref(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => contains_board_in_bounds(inner),
        PureExpr::Let { value, body, .. } => {
            contains_board_in_bounds(value) || contains_board_in_bounds(body)
        }
        PureExpr::LetAssume { assumption, body } => {
            contains_board_in_bounds(assumption) || contains_board_in_bounds(body)
        }
        PureExpr::LetObligation { obligation, body } => {
            contains_board_in_bounds(obligation) || contains_board_in_bounds(body)
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            contains_board_in_bounds(cond)
                || contains_board_in_bounds(then_expr)
                || contains_board_in_bounds(else_expr)
        }
        PureExpr::Forall { body, triggers, .. } | PureExpr::Exists { body, triggers, .. } => {
            contains_board_in_bounds(body)
                || triggers.iter().flatten().any(contains_board_in_bounds)
        }
        PureExpr::LogicFnCall { args, .. } => args.iter().any(contains_board_in_bounds),
        PureExpr::Closure { body, .. } => contains_board_in_bounds(body),
        _ => false,
    }
}

/// Without a spec, the call destination is havoced (no body effect for i).
/// This is the baseline behavior before #1463. (#1463)
#[test]
fn call_result_havoced_without_spec() {
    let source = r#"
#[inline(never)]
fn inc(x: i32) -> i32 {
x + 1
}

pub fn loop_with_unspecced_call(n: i32) -> i32 {
let mut i = 0;
while i < n {
    i = inc(i);
}
i
}
"#;

    // No spec entries — the call result should be havoced.
    let (_, loop_body) =
        analyze_function_with_specs(source, "loop_with_unspecced_call", &["n"], vec![]);
    let loop_body = loop_body.expect("expected loop body extraction");
    assert!(
        !loop_body.body_effects.contains_key("i"),
        "without spec, call destination should be havoced (no body effect for i): {:?}",
        loop_body.body_effects
    );
}

fn assert_for_loop_produced_effect_shape(effect: &PureExpr) {
    match effect {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            assert_eq!(method, "push_back");
            assert!(
                matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "produced"),
                "produced effect receiver should be Var(\"produced\"), got {receiver:?}"
            );
            assert_eq!(args.len(), 1);
            assert!(
                matches!(&args[0], PureExpr::Var(name, _) if name == "x"),
                "produced effect arg should be loop variable x, got {:?}",
                args[0]
            );
        }
        other => panic!("expected produced push_back effect, got {other:?}"),
    }
}

fn assert_result_push_front_effect_shape(effect: &PureExpr) {
    match effect {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } => {
            assert_eq!(
                method, "push_front",
                "After 7e0c9177, push_front_ghost body effect uses push_front directly \
                 (matching R4 axiom trigger) instead of seq(x).concat(self)"
            );
            assert_eq!(args.len(), 1);
            assert!(
                matches!(&args[0], PureExpr::Var(name, _) if name == "x"),
                "push_front arg should be loop variable x, got {:?}",
                args[0]
            );
            assert!(
                matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "result"),
                "push_front receiver should be Var(\"result\"), got {receiver:?}"
            );
        }
        other => panic!("expected result push_front effect, got {other:?}"),
    }
}

#[test]
fn for_loop_seq_ghost_mutation_synthesizes_produced_without_debug_name() {
    let source = r#"
#[derive(Clone)]
pub struct Seq {
inner: Vec<i32>,
}

impl Seq {
fn push_front_ghost(&mut self, x: i32) {
    self.inner.insert(0, x);
}
}

pub fn reverse_like(input: Vec<i32>) -> Seq {
let mut result = Seq { inner: Vec::new() };
for x in input {
    result.push_front_ghost(x);
}
result
}
"#;

    let (_, loop_body) = analyze_function_with_specs(source, "reverse_like", &["input"], vec![]);
    let loop_body = loop_body.expect("expected loop body extraction");

    let produced_effect = loop_body
        .body_effects
        .get("produced")
        .expect("for-loop with ghost seq mutation should synthesize produced effect");
    assert_for_loop_produced_effect_shape(produced_effect);
    assert!(
        loop_body
            .modified_vars
            .iter()
            .any(|name| name == "produced"),
        "synthesized produced effect should extend modified_vars: {:?}",
        loop_body.modified_vars
    );
    assert!(
        loop_body.for_loop_state.is_some(),
        "for-loop ghost state should be extracted for structural invariant synthesis"
    );
    let state = loop_body
        .for_loop_state
        .as_ref()
        .expect("for-loop ghost state should be available for transition modeling");
    let iter_state_name = match &state.iter_state {
        PureExpr::Var(name, _) => name.as_str(),
        other => panic!("synthetic iterator state should be a variable, got {other:?}"),
    };
    assert!(
        loop_body
            .modified_vars
            .iter()
            .any(|name| name == iter_state_name),
        "synthetic iterator state should be treated as modified: {:?}",
        loop_body.modified_vars
    );
    assert_eq!(
        loop_body.body_effects.get(iter_state_name),
        Some(&state.iter_state_next),
        "synthetic iterator state should advance to the step witness"
    );

    let result_effect = loop_body
        .body_effects
        .get("result")
        .expect("push_front_ghost call should produce receiver update effect");
    assert_result_push_front_effect_shape(result_effect);
}

#[test]
fn for_loop_ghost_seq_into_inner_extracts_structural_state() {
    let source = r#"
pub struct Ghost<T>(T);

impl<T> Ghost<T> {
fn into_inner(self) -> T {
    self.0
}
}

#[derive(Clone)]
pub struct Seq {
inner: Vec<i32>,
}

impl Seq {
fn new() -> Self {
    Self { inner: Vec::new() }
}

fn push_front_ghost(&mut self, x: i32) {
    self.inner.insert(0, x);
}
}

impl IntoIterator for Seq {
type Item = i32;
type IntoIter = std::vec::IntoIter<i32>;

fn into_iter(self) -> Self::IntoIter {
    self.inner.into_iter()
}
}

pub fn reverse_like(input: Ghost<Seq>) -> Seq {
let mut result = Seq::new();
for x in input.into_inner() {
    result.push_front_ghost(x);
}
result
}
"#;

    let into_inner_spec = StdSpec {
        capture_inv_requires: Vec::new(),
        inv_requires: Vec::new(),
        requires: vec![],
        ensures: vec!["result == self".to_string()],
        param_names: Some(vec!["self".to_string()]),
    };

    let (_, loop_body) = analyze_function_with_specs(
        source,
        "reverse_like",
        &["input"],
        vec![SpecEntry {
            callee_name: "into_inner".to_string(),
            spec: into_inner_spec,
        }],
    );
    let loop_body = loop_body.expect("expected loop body extraction");
    let state = loop_body
        .for_loop_state
        .as_ref()
        .expect("for-loop ghost state should be recovered for Ghost<Seq>::into_inner()");

    assert!(
        matches!(
            &state.iter_state_binding,
            PureExpr::MethodCall { receiver, method, args }
                if method == "into_iter"
                    && args.is_empty()
                    && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "input")
        ),
        "iterator binding should preserve the recovered into_iter(input) expression, got {:?}",
        state.iter_state_binding
    );
    assert!(
        matches!(
            state.iterable.as_ref(),
            Some(PureExpr::Var(name, _)) if name == "input"
        ),
        "iterable payload should still resolve through into_inner() to the original input, got {:?}",
        state.iterable
    );

    let iter_state_name = match &state.iter_state {
        PureExpr::Var(name, _) => name.as_str(),
        other => panic!("synthetic iterator state should be a variable, got {other:?}"),
    };
    assert!(
        loop_body
            .modified_vars
            .iter()
            .any(|name| name == iter_state_name),
        "synthetic iterator state should still be treated as modified: {:?}",
        loop_body.modified_vars
    );
    assert_eq!(
        loop_body.body_effects.get(iter_state_name),
        Some(&state.iter_state_next),
        "synthetic iterator state should still advance to the step witness"
    );
}

/// For-loop discriminant condition extraction must not produce tautologies.
///
/// When SwitchInt has two targets (Some / None) and loop-body detection
/// over-approximates both as body blocks, the old whilelet path would produce
/// `(discr == 0) || (discr == 1)` which is always true. The new
/// `for_loop_discriminant_condition` classifies targets by whether they extract
/// the loop variable from the Option local, producing a non-tautological
/// condition. (#1581)
#[test]
fn for_loop_condition_not_tautological() {
    let source = r#"
pub fn sum_vec(input: Vec<i32>) -> i32 {
let mut total = 0;
for x in input {
    total += x;
}
total
}
"#;

    let (_, loop_body) = analyze_function_with_specs(source, "sum_vec", &["input"], vec![]);
    let loop_body = loop_body.expect("expected loop body extraction");
    let condition = loop_body
        .condition
        .as_ref()
        .expect("for-loop should extract an iterator continuation condition");

    // Regression guard: iterator discriminant condition must not collapse to the
    // two-variant tautology `(discr == 0) || (discr == 1)`.
    fn is_eq_int(expr: &PureExpr, val: i64) -> bool {
        matches!(expr, PureExpr::BinOp(_, BinOp::Eq, rhs) if matches!(rhs.as_ref(), PureExpr::Int(v) if *v == val))
    }
    let is_two_variant_tautology = matches!(
        condition,
        PureExpr::BinOp(lhs, BinOp::Or, rhs)
        if (is_eq_int(lhs, 0) && is_eq_int(rhs, 1))
        || (is_eq_int(lhs, 1) && is_eq_int(rhs, 0))
    );
    assert!(
        !is_two_variant_tautology,
        "for-loop condition must not be a tautology, got: {condition:?}"
    );
}

#[test]
#[allow(clippy::too_many_lines)]
fn for_range_loop_extracts_structural_state_without_iterable_payload() {
    let source = r#"
#[allow(unused_variables, unused_assignments)]
pub fn count_range(n: isize) -> isize {
let mut i = 0;
for _ in 0..n {
    i += 1;
}
i
}
"#;

    let (_, loop_body) = analyze_function_with_specs(source, "count_range", &["n"], vec![]);
    let loop_body = loop_body.expect("expected loop body extraction");
    let condition = loop_body
        .condition
        .as_ref()
        .expect("range for-loop should synthesize a continuation condition");
    let state = loop_body
        .for_loop_state
        .as_ref()
        .expect("range for-loop should still extract structural state");

    assert_eq!(state.produced_name, "produced");
    assert!(
        matches!(
            state.iter_state,
            PureExpr::Var(_, Some(ExprSort::Datatype(_)))
        ),
        "range for-loop synthetic iterator state should use the underlying iterator sort, got {:?}",
        state.iter_state
    );
    assert!(
        loop_body.body_effects.contains_key("produced"),
        "range for-loop should synthesize produced progression: {:?}",
        loop_body.body_effects
    );
    assert!(
        matches!(
            &state.loop_elem,
            PureExpr::MethodCall { receiver, method, args }
                if method == "start_log"
                    && args.is_empty()
                    && receiver.as_ref() == &state.iter_state
        ),
        "discarded-element range loops should recover the current step as iter_state.start_log(), got {:?}",
        state.loop_elem
    );
    assert_eq!(
        loop_body.body_effects.get("produced"),
        Some(&PureExpr::MethodCall {
            receiver: Arc::new(PureExpr::Var("produced".to_string(), Some(ExprSort::Seq))),
            method: "push_back".to_string(),
            args: vec![state.loop_elem.clone()],
        }),
        "range for-loop produced effect should append the recovered current step"
    );
    let i_effect = loop_body
        .body_effects
        .get("i")
        .expect("range for-loop should keep the counter body effect");
    expect_i_plus(i_effect, 1);
    assert!(
        loop_body
            .modified_vars
            .iter()
            .any(|name| name == "produced"),
        "range for-loop should mark produced as modified: {:?}",
        loop_body.modified_vars
    );
    let iter_state_name = match &state.iter_state {
        PureExpr::Var(name, _) => name.as_str(),
        other => {
            panic!("range for-loop synthetic iterator state should be a variable, got {other:?}")
        }
    };
    assert!(
        loop_body
            .modified_vars
            .iter()
            .any(|name| name == iter_state_name),
        "range for-loop should mark synthetic iterator state as modified: {:?}",
        loop_body.modified_vars
    );
    assert_eq!(
        loop_body.body_effects.get(iter_state_name),
        Some(&state.iter_state_next),
        "range for-loop should advance synthetic iterator state to the next-step witness"
    );
    assert!(
        state.iterable.is_none(),
        "range for-loop should not require a sequence-valued iterable payload"
    );
    match loop_body.return_expr.as_ref() {
        Some(PureExpr::Var(name, _)) => assert_eq!(name, "i"),
        other => panic!("range for-loop should return local i after loop exit, got {other:?}"),
    }
    assert!(
        matches!(
            condition,
            PureExpr::BinOp(lhs, BinOp::Lt, _)
                if matches!(lhs.as_ref(), PureExpr::MethodCall { method, .. } if method == "len")
        ),
        "range for-loop should synthesize a produced-length continuation guard, got: {condition:?}"
    );
    let free_vars = condition.free_vars();
    assert!(
        !free_vars
            .iter()
            .any(|name| name.starts_with("$for_iter_elem_")),
        "range for-loop condition should not depend on a synthetic loop element: {condition:?}"
    );
}

#[test]
fn for_range_loop_recovers_dynamic_len_end_bounds() {
    let source = r#"
pub fn zero_by_index(v: &mut Vec<u32>) {
for i in 0..v.len() {
    v[i] = 0;
}
}
"#;

    let (_, loop_body) = analyze_function_with_specs(source, "zero_by_index", &["v"], vec![]);
    let loop_body = loop_body.expect("expected loop body extraction");
    let state = loop_body
        .for_loop_state
        .as_ref()
        .expect("range for-loop should extract structural state");
    let (start, end) = state
        .range_bounds
        .as_ref()
        .expect("dynamic range end should recover range bounds");

    assert_eq!(start, &PureExpr::Int(0));
    assert!(
        matches!(&state.loop_elem, PureExpr::Var(name, Some(ExprSort::Int)) if name == "i"),
        "range loop element should be the named index variable, got {:?}",
        state.loop_elem
    );
    assert!(
        matches!(end, PureExpr::MethodCall { method, args, .. }
            if method == "len" && args.is_empty() && end.free_vars().contains("v")),
        "dynamic range end should recover v.len(), got {end:?}"
    );
    let indexed_effect = loop_body.deref_body_effects.get("v").unwrap_or_else(|| {
        panic!(
            "v[i] = 0 should synthesize a loop deref effect for v, got {:?}",
            loop_body.deref_body_effects
        )
    });
    assert!(
        matches!(
            indexed_effect,
            PureExpr::MethodCall { receiver, method, args }
                if method == "set"
                    && args == &vec![state.loop_elem.clone(), PureExpr::Int(0)]
                    && matches!(
                        receiver.as_ref(),
                        PureExpr::View(inner)
                            if matches!(
                                inner.as_ref(),
                                PureExpr::Deref(base)
                                    if matches!(base.as_ref(), PureExpr::Var(name, _) if name == "v")
                            )
                    )
        ),
        "indexed loop write should update v through a sequence set effect, got {indexed_effect:?}"
    );
}

#[test]
fn for_range_inclusive_loop_recovers_literal_start_and_produced_effect() {
    let source = r#"
pub fn sum_first_n(n: u32) -> u32 {
    let mut sum = 0;
    for i in 1..=n {
        sum += i;
    }
    sum
}
"#;

    let (_, loop_body) = analyze_function_with_specs(source, "sum_first_n", &["n"], vec![]);
    let loop_body = loop_body.expect("expected loop body extraction");
    let state = loop_body
        .for_loop_state
        .as_ref()
        .expect("inclusive range for-loop should extract structural state");
    let PureExpr::Var(_, Some(ExprSort::Datatype(sort_id))) = &state.iter_state else {
        panic!(
            "inclusive range iterator state should carry a datatype sort, got {:?}",
            state.iter_state
        );
    };
    assert!(
        trust_wp_core::formula::resolve_sort_name(*sort_id).contains("RangeInclusive"),
        "sum_first_n should retain RangeInclusive sort, got {:?}",
        state.iter_state
    );

    let (start, end) = state
        .range_bounds
        .as_ref()
        .expect("inclusive range should recover range bounds");
    assert_eq!(start, &PureExpr::Int(1));
    assert!(
        end.free_vars().contains("n"),
        "inclusive range end should recover n, got {end:?}"
    );
    assert!(
        loop_body.body_effects.contains_key(&state.produced_name),
        "for-loop should synthesize produced.push_back(i), got {:?}",
        loop_body.body_effects
    );
}

#[test]
fn for_range_loop_recovers_dynamic_len_end_bounds_through_ref_temp_chain() {
    let source = r#"
pub fn zero_by_index(v: &mut Vec<u32>) {
for i in 0..v.len() {
    v[i] = 0;
}
}
"#;

    let (start, end) = recover_range_bounds_with_rustc_args(
        source,
        "zero_by_index",
        &["v"],
        &["-Zmir-opt-level=0"],
    )
    .expect("ref-temp Iterator::next lowering should still recover range bounds");

    assert_eq!(start, PureExpr::Int(0));
    assert!(
        matches!(&end, PureExpr::MethodCall { method, args, .. }
            if method == "len" && args.is_empty() && end.free_vars().contains("v")),
        "dynamic range end should recover v.len() through ref temporaries, got {end:?}"
    );
}

#[test]
fn poisoned_exit_block_still_extracts_post_loop_return_expr_for_range_loop() {
    let source = r#"
pub fn count_range(n: isize) -> isize {
let mut i = 0;
for _ in 0..n {
    i += 1;
}
i
}
"#;

    let loop_body = analyze_function_with_poisoned_exit_block(source, "count_range", &["n"])
        .expect("expected loop body extraction");

    match loop_body.return_expr.as_ref() {
        Some(PureExpr::Var(name, _)) => assert_eq!(name, "i"),
        other => panic!(
            "post-loop return extraction should survive a poisoned exit block, got {other:?}"
        ),
    }
}

#[test]
fn poisoned_exit_block_still_extracts_post_loop_deref_write_for_range_loop() {
    let source = r#"
pub fn range_then_write(v: &mut i32, n: i32) -> i32 {
for _ in 0usize..3usize {
    *v += 1;
}
*v = n;
*v
}
"#;

    let loop_body =
        analyze_function_with_poisoned_exit_block(source, "range_then_write", &["v", "n"])
            .expect("expected loop body extraction");

    assert!(
        loop_body.post_loop_deref_writes.contains("v"),
        "post-loop deref write extraction should survive a poisoned exit block"
    );
}

#[test]
fn poisoned_exit_block_still_extracts_post_loop_deref_final_values_for_range_loop() {
    let source = r#"
pub fn range_then_write(v: &mut i32, n: i32) -> i32 {
for _ in 0usize..3usize {
    *v += 1;
}
*v = n;
*v
}
"#;

    let loop_body =
        analyze_function_with_poisoned_exit_block(source, "range_then_write", &["v", "n"])
            .expect("expected loop body extraction");
    let v_final = loop_body
        .post_loop_deref_final_values
        .get("v")
        .expect("final value for `v` should be extracted");
    let debug_repr = format!("{v_final:?}");
    assert!(
        debug_repr.contains("\"n\""),
        "final value of `v` should reference `n`, got: {debug_repr}"
    );
}

/// A spec with ensures but no `result == <expr>` pattern (only `result > 0`)
/// names the call's result with a symbol and states the clause about it as a
/// call fact; a havoced result would let the loop VC pick `i' <= 0`, which the
/// program rules out (loop_body_call_postcondition_premise_control).
#[test]
fn call_result_named_with_predicate_only_spec() {
    let source = r#"
#[inline(never)]
fn positive(x: i32) -> i32 {
if x > 0 { x } else { 1 }
}

pub fn loop_with_predicate_spec(n: i32) -> i32 {
let mut i = 1;
while i < n {
    i = positive(i);
}
i
}
"#;
    let spec = StdSpec {
        capture_inv_requires: Vec::new(),
        inv_requires: Vec::new(),
        requires: vec![],
        ensures: vec!["result > 0".to_string()],
        param_names: Some(vec!["x".to_string()]),
    };

    let (_, loop_body) = analyze_function_with_specs(
        source,
        "loop_with_predicate_spec",
        &["n"],
        vec![SpecEntry {
            callee_name: "positive".to_string(),
            spec,
        }],
    );
    let loop_body = loop_body.expect("expected loop body extraction");
    let Some(PureExpr::Var(symbol, _)) = loop_body.body_effects.get("i") else {
        panic!(
            "predicate-only spec should name the call result: {:?}",
            loop_body.body_effects
        );
    };
    assert!(
        symbol.starts_with("__trust_wp_loop_call_result_"),
        "unexpected result name {symbol}"
    );
    let states_positive = |fact: &PureExpr| {
        matches!(fact, PureExpr::BinOp(lhs, BinOp::Gt, rhs)
            if matches!(lhs.as_ref(), PureExpr::Var(name, _) if name == symbol)
                && matches!(rhs.as_ref(), PureExpr::Int(0)))
    };
    assert!(
        loop_body.call_facts.iter().any(states_positive),
        "the clause `result > 0` should be stated at the result: {:?}",
        loop_body.call_facts
    );
    assert!(
        loop_body.dropped_premises.is_empty(),
        "nothing should be dropped: {:?}",
        loop_body.dropped_premises
    );
}

/// Pre-loop call with view-based spec should not disrupt body extraction.
/// `n = get_len(v)` is called before the loop; `i = i + 1` is inside the
/// loop body. The pre-loop call goes through `unresolved_pre_loop_calls`,
/// not `try_model_call_result`. This test verifies body effects survive. (#1463)
#[test]
fn pre_loop_view_spec_call_preserves_body_effects() {
    let source = r#"
#[inline(never)]
fn get_len(v: &[i32]) -> usize {
v.len()
}

pub fn loop_with_len_call(v: &[i32]) -> usize {
let mut i: usize = 0;
let n = get_len(v);
while i < n {
    i = i + 1;
}
i
}
"#;
    let spec = StdSpec {
        capture_inv_requires: Vec::new(),
        inv_requires: Vec::new(),
        requires: vec![],
        ensures: vec!["result@ == self@.len()".to_string()],
        param_names: Some(vec!["self".to_string()]),
    };

    let (_, loop_body) = analyze_function_with_specs(
        source,
        "loop_with_len_call",
        &["v"],
        vec![SpecEntry {
            callee_name: "get_len".to_string(),
            spec,
        }],
    );
    let loop_body = loop_body.expect("expected loop body extraction");
    let effect = loop_body.body_effects.get("i");
    assert!(
        effect.is_some(),
        "body effect for `i` should exist (pre-loop call must not disrupt): {:?}",
        loop_body.body_effects
    );
}

/// In-loop call with view-based spec (`result@ == self@.len()`) should be
/// modeled via `try_model_call_result`. The `@` (view operator) on result
/// is transparent for primitives. (#1463)
#[test]
fn call_result_modeled_with_view_spec_in_loop() {
    let source = r#"
#[inline(never)]
fn get_len(v: &[i32]) -> usize {
v.len()
}

pub fn loop_with_in_body_len_call(v: &[i32]) -> usize {
let mut i: usize = 0;
while i < 10 {
    let n = get_len(v);
    let _ = n;
    i = i + 1;
}
i
}
"#;
    let spec = StdSpec {
        capture_inv_requires: Vec::new(),
        inv_requires: Vec::new(),
        requires: vec![],
        ensures: vec!["result@ == self@.len()".to_string()],
        param_names: Some(vec!["self".to_string()]),
    };

    let (_, loop_body) = analyze_function_with_specs(
        source,
        "loop_with_in_body_len_call",
        &["v"],
        vec![SpecEntry {
            callee_name: "get_len".to_string(),
            spec,
        }],
    );
    let loop_body = loop_body.expect("expected loop body extraction");
    // `i` should have body effect from `i = i + 1`
    let i_effect = loop_body.body_effects.get("i");
    assert!(
        i_effect.is_some(),
        "body effect for `i` should exist: {:?}",
        loop_body.body_effects
    );
}

/// Header-condition loops (`while cond { body }`) should set
/// `condition_is_body_break = false` because the condition is checked
/// BEFORE the body executes. (#1541)
#[test]
fn header_condition_loop_sets_condition_is_body_break_false() {
    let source = r#"
pub fn header_cond(n: i32) -> i32 {
let mut i = 0;
while i < n {
    i += 1;
}
i
}
"#;
    let (_, loop_body) = analyze_function(source, "header_cond", &["n"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    assert!(
        loop_body.condition.is_some(),
        "header condition should be extracted"
    );
    assert!(
        !loop_body.condition_is_body_break,
        "while-loop header condition must have condition_is_body_break == false"
    );
}

/// Body-break loops (`loop { body; if cond { break; } }`) should set
/// `condition_is_body_break = true` because the condition is checked
/// AFTER the body effects execute. Preservation must apply the condition
/// to primed (post-body) variables. (#1295, #1541)
#[test]
fn body_break_loop_sets_condition_is_body_break_true() {
    let source = r#"
pub fn body_break_loop(n: i32) -> i32 {
let mut i = 0;
loop {
    i += 1;
    if i >= n {
        break;
    }
}
i
}
"#;
    let (_, loop_body) = analyze_function(source, "body_break_loop", &["n"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    assert!(
        loop_body.condition.is_some(),
        "body-break condition should be extracted from `if cond {{ break; }}`"
    );
    assert!(
        loop_body.condition_is_body_break,
        "loop {{ ...; if cond {{ break; }} }} must have condition_is_body_break == true"
    );
}

/// A `loop { }` with no break condition at all should have no condition
/// and `condition_is_body_break = false` (the default). (#1541)
#[test]
fn infinite_loop_no_condition_body_break_false() {
    let source = r#"
pub fn infinite_loop() -> ! {
let mut _i = 0;
loop {
    _i += 1;
}
}
"#;
    let (_, loop_body) = analyze_function(source, "infinite_loop", &[]);
    let loop_body = loop_body.expect("expected loop body extraction");
    assert!(
        loop_body.condition.is_none(),
        "infinite loop without break should have no condition"
    );
    assert!(
        !loop_body.condition_is_body_break,
        "no condition means condition_is_body_break defaults to false"
    );
}

#[test]
fn pre_loop_written_params_empty_for_stable_params() {
    // Parameters not reassigned before the loop should NOT appear in pre_loop_written_params.
    let source = r#"
pub fn stable_param(n: i32) -> i32 {
let mut i = 0;
while i < n {
    i += 1;
}
i
}
"#;
    let (_, loop_body) = analyze_function(source, "stable_param", &["n"]);
    let loop_body = loop_body.expect("expected loop body extraction");
    assert!(
        loop_body.pre_loop_written_params.is_empty(),
        "stable parameter n should not appear in pre_loop_written_params: {:?}",
        loop_body.pre_loop_written_params
    );
}

#[test]
fn while_let_vec_pop_is_not_classified_as_for_loop() {
    let source = r#"
pub fn drain(mut x: Vec<u32>) {
    while let Some(_) = x.pop() {}
}
"#;
    let (_, loop_body) = analyze_function_with_specs(source, "drain", &["x"], vec![]);
    let loop_body = loop_body.expect("expected loop body extraction");

    assert!(
        loop_body.for_loop_state.is_none(),
        "Vec::pop while-let loop must not synthesize for-loop ghost state: {:?}",
        loop_body.for_loop_state
    );
    assert!(
        !loop_body.body_effects.contains_key("produced"),
        "Vec::pop while-let loop must not synthesize a produced effect: {:?}",
        loop_body.body_effects
    );
}

/// Regression test for #2323: for-loop variant of take_max ITE alias split.
///
/// Verifies that the MIR extraction produces correct body effects for a
/// for-loop over `0..n` with `take_max` call, which has different MIR
/// structure (Iterator::next call, Option destructuring) than the while-loop
/// variant tested in `deref_write_ite_alias_split_preserves_typed_current_branch_values`.
#[test]
#[allow(clippy::too_many_lines)]
fn for_loop_take_max_ite_alias_split_body_effects() {
    let source = r#"
#[inline(never)]
fn take_max<'a>(ma: &'a mut u32, mb: &'a mut u32) -> &'a mut u32 {
    if *ma >= *mb { ma } else { mb }
}

pub fn inc_max_repeat(mut a: u32, mut b: u32, n: u32) {
    for _ in 0..n {
        let mc = take_max(&mut a, &mut b);
        *mc += 1;
    }
}
"#;
    let spec = StdSpec {
        capture_inv_requires: Vec::new(),
        inv_requires: Vec::new(),
        requires: vec![],
        ensures: vec![
            "if *ma >= *mb { *mb == ^mb && result == ma } else { *ma == ^ma && result == mb }"
                .to_string(),
        ],
        param_names: Some(vec!["ma".to_string(), "mb".to_string()]),
    };

    let (_, loop_body) = analyze_function_with_specs(
        source,
        "inc_max_repeat",
        &["a", "b", "n"],
        vec![SpecEntry {
            callee_name: "take_max".to_string(),
            spec,
        }],
    );
    let loop_body = loop_body.expect("expected loop body extraction");
    let condition = loop_body
        .condition
        .as_ref()
        .expect("range for-loop should extract a continuation condition");
    let state = loop_body
        .for_loop_state
        .as_ref()
        .expect("range for-loop should retain structural state");

    assert!(
        matches!(
            state.iter_state,
            PureExpr::Var(_, Some(ExprSort::Datatype(_)))
        ),
        "inc_max_repeat range iterator state should use the underlying iterator sort, got {:?}",
        state.iter_state
    );
    assert!(
        matches!(
            state.iter_old,
            PureExpr::Var(_, Some(ExprSort::Datatype(_)))
        ),
        "inc_max_repeat range iterator snapshot should use the underlying iterator sort, got {:?}",
        state.iter_old
    );
    assert!(
        !is_two_variant_tautology(condition),
        "range for-loop condition must not collapse to the iterator discriminant tautology: {condition:?}"
    );
    let fallback_guard = PureExpr::BinOp(
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(state.iter_state.clone()),
            method: "start_log".to_string(),
            args: vec![],
        }),
        BinOp::Lt,
        Arc::new(PureExpr::MethodCall {
            receiver: Arc::new(state.iter_old.clone()),
            method: "end_log".to_string(),
            args: vec![],
        }),
    );
    let preferred_produced_guard = matches!(
        condition,
        PureExpr::BinOp(lhs, BinOp::Lt, _)
            if matches!(lhs.as_ref(), PureExpr::MethodCall { receiver, method, args }
                if method == "len"
                    && args.is_empty()
                    && matches!(
                        receiver.as_ref(),
                        PureExpr::View(inner)
                            if matches!(inner.as_ref(), PureExpr::Var(name, Some(ExprSort::Seq)) if name == "produced")
                    ))
    );
    assert!(
        condition == &fallback_guard || preferred_produced_guard,
        "range for-loop condition should use either the preferred produced-length guard or the structural fallback guard, got: {condition:?}"
    );

    let a_effect = loop_body.body_effects.get("a");
    let b_effect = loop_body.body_effects.get("b");

    assert!(
        a_effect.is_some(),
        "for-loop with take_max should produce a body effect for 'a', \
         but only found effects for: {:?}",
        loop_body.body_effects.keys().collect::<Vec<_>>()
    );
    assert!(
        b_effect.is_some(),
        "for-loop with take_max should produce a body effect for 'b', \
         but only found effects for: {:?}",
        loop_body.body_effects.keys().collect::<Vec<_>>()
    );

    match a_effect.unwrap() {
        PureExpr::Ite(_, then_expr, else_expr) => {
            assert!(
                matches!(then_expr.as_ref(),
                    PureExpr::BinOp(lhs, BinOp::Add, rhs)
                    if matches!(lhs.as_ref(), PureExpr::Var(n, _) if n == "a")
                    && matches!(rhs.as_ref(), PureExpr::Int(1))
                ),
                "a then-branch should be a + 1, got {then_expr:?}"
            );
            assert!(
                matches!(else_expr.as_ref(), PureExpr::Var(n, _) if n == "a"),
                "a else-branch should be a, got {else_expr:?}"
            );
        }
        other => panic!("expected ITE body effect for a, got {other:?}"),
    }

    match b_effect.unwrap() {
        PureExpr::Ite(_, then_expr, else_expr) => {
            assert!(
                matches!(then_expr.as_ref(), PureExpr::Var(n, _) if n == "b"),
                "b then-branch should keep b, got {then_expr:?}"
            );
            assert!(
                matches!(else_expr.as_ref(),
                    PureExpr::BinOp(lhs, BinOp::Add, rhs)
                    if matches!(lhs.as_ref(), PureExpr::Var(n, _) if n == "b")
                    && matches!(rhs.as_ref(), PureExpr::Int(1))
                ),
                "b else-branch should be b + 1, got {else_expr:?}"
            );
        }
        other => panic!("expected ITE body effect for b, got {other:?}"),
    }
}

#[test]
fn loop_index_mut_obligation_uses_typed_field_receiver() {
    let source = r#"
pub struct MyMap {
    buckets: Vec<i32>,
}

fn touch_slot(_: &mut i32) {}

impl MyMap {
    pub fn resize(&mut self) {
        let mut i = 0usize;
        while i < self.buckets.len() {
            touch_slot(&mut self.buckets[i]);
            i += 1;
        }
    }
}
"#;

    let groups = collect_loop_obligation_groups_with_specs(source, "resize", &["self"], vec![]);

    assert_eq!(groups.len(), 1, "expected one loop obligation group");
    let obligation = groups[0]
        .iter()
        .find_map(|obligation| match obligation {
            PureExpr::BinOp(_, BinOp::Implies, rhs) => Some(rhs.as_ref()),
            other => Some(other),
        })
        .expect("expected an IndexMut in-bounds obligation");

    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = obligation
    else {
        panic!("expected in_bounds obligation, got {obligation:?}");
    };
    assert_eq!(method, "in_bounds");
    assert!(
        matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "i"),
        "expected index receiver i, got {receiver:?}"
    );
    assert!(
        matches!(
            args.as_slice(),
            [PureExpr::View(inner)]
                if matches!(
                    inner.as_ref(),
                    PureExpr::LogicFnCall { name, args }
                        if name == "__trust_wp_field_buckets"
                            && matches!(args.as_slice(), [PureExpr::Deref(base)]
                                if matches!(base.as_ref(), PureExpr::Var(name, _) if name == "self"))
                )
        ),
        "IndexMut sequence argument should be self.buckets@, got {args:?}"
    );
}

// ---- &mut self post-state deref-effect modeling (loop-mut-self-postcondition) ----

/// `View(Deref(Var(name)))` — the OLD pointee view `(*v)@` / `v@` for a `&mut`
/// receiver, against which a recorded mut-self deref effect is expressed.
fn is_old_view_of(expr: &PureExpr, name: &str) -> bool {
    matches!(
        expr,
        PureExpr::View(inner)
            if matches!(inner.as_ref(), PureExpr::Deref(base)
                if matches!(base.as_ref(), PureExpr::Var(n, _) if n == name))
    )
}

#[test]
fn loop_body_mut_self_push_records_pushback_deref_effect() {
    // A loop body calling a specced `&mut self` mutator with an equational
    // `(^self)@ == self@.push_back(value)` postcondition must record a deref
    // effect `deref_effects[v] = (*v)@.push_back(value)` instead of havocing v.
    let source = r#"
#[inline(never)]
fn push_one(v: &mut Vec<i32>, value: i32) {
    v.push(value);
}

pub fn loop_pushes(v: &mut Vec<i32>, n: i32) {
    let mut i = 0;
    while i < n {
        push_one(v, i);
        i += 1;
    }
}
"#;
    let spec = StdSpec {
        capture_inv_requires: Vec::new(),
        inv_requires: Vec::new(),
        requires: vec![],
        ensures: vec!["(^self)@ == self@.push_back(value)".to_string()],
        param_names: Some(vec!["self".to_string(), "value".to_string()]),
    };

    let (_, loop_body) = analyze_function_with_specs(
        source,
        "loop_pushes",
        &["v", "n"],
        vec![SpecEntry {
            callee_name: "push_one".to_string(),
            spec,
        }],
    );
    let loop_body = loop_body.expect("expected loop body extraction");

    let effect = loop_body
        .deref_body_effects
        .get("v")
        .expect("mut-self push should record a deref effect on v, not havoc it");

    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = effect
    else {
        panic!("expected push_back method call deref effect, got {effect:?}");
    };
    assert_eq!(method, "push_back", "deref effect should be push_back");
    assert!(
        is_old_view_of(receiver.as_ref(), "v"),
        "push_back receiver should be the old view (*v)@, got {receiver:?}"
    );
    assert_eq!(args.len(), 1, "push_back takes one value, got {args:?}");
}

#[test]
fn loop_body_mut_self_swap_records_transposition_deref_effect() {
    // A loop body calling a specced `&mut self` swap with the predicate
    // `(^self)@.exchange(self@, a@, b@)` postcondition must record the
    // closed-form transposition deref effect
    //   (*v)@.set(a, (*v)@.index_logic(b)).set(b, (*v)@.index_logic(a))
    // so the swap->exchange->permutation bridge reaches the loop VC.
    let source = r#"
#[inline(never)]
fn swap_two(v: &mut Vec<i32>, a: usize, b: usize) {
    v.swap(a, b);
}

pub fn loop_swaps(v: &mut Vec<i32>, n: usize) {
    let mut i = 0;
    while i < n {
        swap_two(v, i, i);
        i += 1;
    }
}
"#;
    let spec = StdSpec {
        capture_inv_requires: Vec::new(),
        inv_requires: Vec::new(),
        requires: vec![],
        ensures: vec!["(^self)@.exchange(self@, a@, b@)".to_string()],
        param_names: Some(vec!["self".to_string(), "a".to_string(), "b".to_string()]),
    };

    let (_, loop_body) = analyze_function_with_specs(
        source,
        "loop_swaps",
        &["v", "n"],
        vec![SpecEntry {
            callee_name: "swap_two".to_string(),
            spec,
        }],
    );
    let loop_body = loop_body.expect("expected loop body extraction");

    let effect = loop_body
        .deref_body_effects
        .get("v")
        .expect("mut-self swap should record a deref effect on v, not havoc it");

    // Outer: set(_, b, (*v)@.index_logic(a))
    let PureExpr::MethodCall {
        receiver: outer_recv,
        method: outer_method,
        args: outer_args,
    } = effect
    else {
        panic!("expected outer set method call, got {effect:?}");
    };
    assert_eq!(outer_method, "set", "outer transposition op should be set");
    assert_eq!(outer_args.len(), 2);
    // Inner: (*v)@.set(a, (*v)@.index_logic(b))
    let PureExpr::MethodCall {
        receiver: inner_recv,
        method: inner_method,
        args: _inner_args,
    } = outer_recv.as_ref()
    else {
        panic!("expected inner set method call, got {outer_recv:?}");
    };
    assert_eq!(inner_method, "set", "inner transposition op should be set");
    assert!(
        is_old_view_of(inner_recv.as_ref(), "v"),
        "inner set receiver should be old view (*v)@, got {inner_recv:?}"
    );
    // Outer value is the cross index_logic read (*v)@.index_logic(a).
    assert!(
        matches!(
            &outer_args[1],
            PureExpr::MethodCall { receiver, method, .. }
                if method == "index_logic" && is_old_view_of(receiver.as_ref(), "v")
        ),
        "outer set value should be (*v)@.index_logic(..), got {:?}",
        outer_args[1]
    );
}

#[test]
fn loop_body_shared_self_call_does_not_record_deref_effect() {
    // A `&self` (shared) call must NOT be modeled as an in-place transition: it
    // cannot mutate the caller-visible state, so no deref effect is recorded.
    let source = r#"
#[inline(never)]
fn read_one(v: &Vec<i32>) -> usize {
    v.len()
}

pub fn loop_reads(v: &Vec<i32>, n: usize) -> usize {
    let mut acc = 0;
    let mut i = 0;
    while i < n {
        acc += read_one(v);
        i += 1;
    }
    acc
}
"#;
    let spec = StdSpec {
        capture_inv_requires: Vec::new(),
        inv_requires: Vec::new(),
        requires: vec![],
        // A (deliberately mis-shaped) final-self clause: even if present, a
        // `&self` receiver must be ignored by the mut-self modeler.
        ensures: vec!["result@ == self@.len()".to_string()],
        param_names: Some(vec!["self".to_string()]),
    };

    let (_, loop_body) = analyze_function_with_specs(
        source,
        "loop_reads",
        &["v", "n"],
        vec![SpecEntry {
            callee_name: "read_one".to_string(),
            spec,
        }],
    );
    let loop_body = loop_body.expect("expected loop body extraction");

    assert!(
        !loop_body.deref_body_effects.contains_key("v"),
        "shared &self call must not record a deref effect on v, got {:?}",
        loop_body.deref_body_effects
    );
}
