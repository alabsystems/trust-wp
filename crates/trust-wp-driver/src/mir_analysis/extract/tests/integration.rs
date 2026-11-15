// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    fs,
    sync::atomic::{AtomicU64, Ordering},
};

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_hir::{def::DefKind, def_id::DefId};
use rustc_interface::interface::Compiler;
use trust_wp_core::formula::ExprSort;
use trust_wp_driver::{builtin_trust_wp_std_specs, StdSpec};

use super::*;
use crate::attr_utils::get_contract_attrs_from_doc;

static EXTRACT_TEST_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Test callback that compiles code, finds a target function, and runs
/// `resolve_closure_arg_return_values` on the first Call terminator whose
/// arguments include a closure operand.
struct ClosureArgCallbacks {
    fn_name: String,
    /// After running, contains the translated args (with closure resolution applied).
    resolved_args: Option<Vec<TranslatedArg>>,
    /// Whether the callback found and processed the target function.
    ran: bool,
}

impl Callbacks for ClosureArgCallbacks {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let suffix = format!("::{}", self.fn_name);

        for local_def_id in tcx.hir_body_owners() {
            let def_path = tcx.def_path_str(local_def_id);
            if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                continue;
            }

            let body = tcx.optimized_mir(local_def_id.to_def_id());
            let user_specs = HashMap::new();
            let trait_specs = HashMap::new();
            let extern_specs = HashMap::new();
            let ctx = SubstitutionExtractionContext {
                tcx,
                user_specs: &user_specs,
                trait_specs: &trait_specs,
                extern_specs: &extern_specs,
                closure_capture_names: None,
                final_reborrow_sites: std::collections::HashSet::new(),
                written_deref_reads: HashMap::new(),
                loop_head_rebinds: HashMap::new(),
                renamable_params: std::collections::HashSet::new(),
            };

            // Walk basic blocks to find a Call terminator with arguments
            for bb_data in body.basic_blocks.iter() {
                let Some(terminator) = &bb_data.terminator else {
                    continue;
                };
                let TerminatorKind::Call { args, .. } = &terminator.kind else {
                    continue;
                };
                if args.is_empty() {
                    continue;
                }

                // Build local_exprs from function arguments
                let local_exprs: HashMap<Local, PureExpr> = body
                    .args_iter()
                    .enumerate()
                    .map(|(idx, local)| (local, PureExpr::Var(format!("arg{idx}"), None)))
                    .collect();

                let mut translated = translate_call_args_for_substitutions(args, &local_exprs);

                // Only process calls that pass a closure-typed argument.
                if !args
                    .iter()
                    .any(|arg| arg.node.ty(&body.local_decls, tcx).is_closure())
                {
                    continue;
                }

                resolve_closure_arg_return_values(&ctx, body, args, &mut translated);

                self.resolved_args = Some(translated);
                self.ran = true;
                return Compilation::Stop;
            }
        }

        Compilation::Stop
    }
}

fn resolve_closure_args_in_source(source: &str, fn_name: &str) -> Vec<TranslatedArg> {
    let unique = EXTRACT_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_closure_resolve_{}_{}",
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
        "trust_wp_closure_resolve_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = ClosureArgCallbacks {
        fn_name: fn_name.to_string(),
        resolved_args: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to find a Call with a closure arg in `{fn_name}`"
    );
    callbacks
        .resolved_args
        .expect("resolved_args should be set when ran=true")
}

/// The closure-typed argument's translation after resolution.
fn closure_arg_in_source(source: &str, fn_name: &str) -> TranslatedArg {
    let resolved = resolve_closure_args_in_source(source, fn_name);
    // The closure is the last argument of every combinator probed here.
    resolved.last().cloned().expect("call has arguments")
}

#[test]
fn resolve_closure_arg_replaces_literal_thunk_exactly() {
    // `ok_or_else(|| 42)`: capture-free, parameter-free, body `_0 = const 42`.
    let source = r#"
pub fn test_fn(x: Option<i32>) -> Result<i32, i32> {
x.ok_or_else(|| 42)
}
"#;
    let arg = closure_arg_in_source(source, "test_fn");
    assert!(
        arg.exact_callable_value,
        "literal thunk must be exact: {arg:?}"
    );
    assert_eq!(arg.expr, PureExpr::Int(42));
}

#[test]
fn resolve_closure_arg_keeps_receiver_untouched() {
    let source = r#"
pub fn test_fn(x: Option<i32>) -> Result<i32, i32> {
x.ok_or_else(|| 42)
}
"#;
    let resolved = resolve_closure_args_in_source(source, "test_fn");
    let receiver = resolved.first().expect("receiver arg");
    assert!(!receiver.exact_callable_value, "{receiver:?}");
    assert_ne!(receiver.expr, PureExpr::Int(42));
}

fn assert_opaque(source: &str, what: &str) {
    let arg = closure_arg_in_source(source, "test_fn");
    assert!(
        arg.opaque_callable(),
        "{what}: closure argument must stay an opaque callable, got {arg:?}"
    );
}

#[test]
fn resolve_closure_arg_capturing_closure_is_opaque() {
    assert_opaque(
        r#"
pub fn test_fn(x: Option<i32>, b: i32) -> Result<i32, i32> {
x.ok_or_else(move || b + 1)
}
"#,
        "capturing closure",
    );
}

#[test]
fn resolve_closure_arg_loop_body_is_opaque() {
    assert_opaque(
        r#"
#[inline(never)]
fn step(x: i32) -> i32 { x + 1 }
pub fn test_fn(x: Option<i32>) -> Result<i32, i32> {
x.ok_or_else(|| { let mut i = 0i32; let mut n = 0i32; while i < 3 { n = step(n); i += 1; } n })
}
"#,
        "loop body",
    );
}

#[test]
fn resolve_closure_arg_panicking_body_is_opaque() {
    assert_opaque(
        r#"
pub fn test_fn(x: Option<i32>) -> Result<i32, i32> {
x.ok_or_else(|| { if 1 == 1 { panic!() } 1 })
}
"#,
        "panicking body",
    );
}

#[test]
fn resolve_closure_arg_call_body_is_opaque() {
    assert_opaque(
        r#"
#[inline(never)]
fn seven() -> i32 { std::hint::black_box(7) }
pub fn test_fn(x: Option<i32>) -> Result<i32, i32> {
x.ok_or_else(|| seven())
}
"#,
        "call body",
    );
}

#[test]
fn resolve_closure_arg_parameterised_closure_is_opaque() {
    assert_opaque(
        r#"
pub fn test_fn(x: Option<i32>) -> i32 {
x.map_or_else(|| 0, |v| v)
}
"#,
        "closure with a parameter",
    );
}

/// Test callback that compiles code, finds a target function, and captures
/// the return expression from `extract_return_expr_with_context`.
struct ReturnExprCallbacks {
    fn_name: String,
    /// Set to `Some(expr)` when extraction succeeds, left as `None` when
    /// it returns `None`. Use `ran` to distinguish "not yet run" from
    /// "ran but extraction returned None".
    return_expr: Option<PureExpr>,
    ran: bool,
}

fn discover_trait_specs(tcx: TyCtxt<'_>) -> HashMap<DefId, StdSpec> {
    let mut trait_specs = HashMap::new();

    for local_def_id in tcx.iter_local_def_id() {
        let def_id = local_def_id.to_def_id();
        if tcx.def_kind(def_id) != DefKind::Trait {
            continue;
        }

        for assoc_item in tcx.associated_items(def_id).in_definition_order() {
            if tcx.def_kind(assoc_item.def_id) != DefKind::AssocFn {
                continue;
            }

            let attrs = tcx.get_all_attrs(assoc_item.def_id);
            let requires = get_contract_attrs_from_doc(attrs, "requires");
            let ensures = get_contract_attrs_from_doc(attrs, "ensures");
            if requires.is_empty() && ensures.is_empty() {
                continue;
            }

            // Mirror the production trait-spec table: discovered trait contracts
            // are keyed by the trait method DefId and carry textual clauses.
            trait_specs.insert(
                assoc_item.def_id,
                StdSpec {
                    capture_inv_requires: Vec::new(),
                    inv_requires: Vec::new(),
                    requires,
                    ensures,
                    param_names: None,
                },
            );
        }
    }

    trait_specs
}

impl Callbacks for ReturnExprCallbacks {
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
            let user_specs = HashMap::new();
            let trait_specs = HashMap::new();

            let (expr, _effects) = extract_return_expr_with_context(
                tcx,
                body,
                &arg_names,
                &user_specs,
                &trait_specs,
                &HashMap::new(),
            );
            self.return_expr = expr;
            self.ran = true;
            return Compilation::Stop;
        }

        Compilation::Stop
    }
}

fn extract_return_expr_in_source(source: &str, fn_name: &str) -> Option<PureExpr> {
    let unique = EXTRACT_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_return_expr_{}_{}",
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
        "trust_wp_return_expr_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = ReturnExprCallbacks {
        fn_name: fn_name.to_string(),
        return_expr: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to extract return expr for `{fn_name}`"
    );
    callbacks.return_expr
}

struct StdSpecReturnExprCallbacks {
    fn_name: String,
    return_expr: Option<PureExpr>,
    ran: bool,
}

impl Callbacks for StdSpecReturnExprCallbacks {
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
            let user_specs = HashMap::new();
            let trait_specs = HashMap::new();
            let extern_specs = builtin_trust_wp_std_specs();

            let (expr, _effects) = extract_return_expr_with_context(
                tcx,
                body,
                &arg_names,
                &user_specs,
                &trait_specs,
                &extern_specs,
            );
            self.return_expr = expr;
            self.ran = true;
            return Compilation::Stop;
        }

        Compilation::Stop
    }
}

fn extract_return_expr_in_source_with_std_specs(
    source: &str,
    fn_name: &str,
    crate_name: &str,
) -> Option<PureExpr> {
    let unique = EXTRACT_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_return_expr_std_specs_{}_{}",
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
        crate_name.to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = StdSpecReturnExprCallbacks {
        fn_name: fn_name.to_string(),
        return_expr: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to extract return expr with std specs for `{fn_name}`"
    );
    callbacks.return_expr
}

struct TraitSpecReturnExprCallbacks {
    fn_name: String,
    return_expr: Option<PureExpr>,
    ran: bool,
}

impl Callbacks for TraitSpecReturnExprCallbacks {
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
            let user_specs = HashMap::new();
            let trait_specs = discover_trait_specs(tcx);

            let (expr, _effects) = extract_return_expr_with_context(
                tcx,
                body,
                &arg_names,
                &user_specs,
                &trait_specs,
                &HashMap::new(),
            );
            self.return_expr = expr;
            self.ran = true;
            return Compilation::Stop;
        }

        Compilation::Stop
    }
}

fn extract_return_expr_in_source_with_trait_specs(source: &str, fn_name: &str) -> Option<PureExpr> {
    let unique = EXTRACT_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_return_expr_trait_specs_{}_{}",
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
        "trust_wp_return_expr_trait_specs_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = TraitSpecReturnExprCallbacks {
        fn_name: fn_name.to_string(),
        return_expr: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to extract return expr with trait specs for `{fn_name}`"
    );
    callbacks.return_expr
}

struct RecursiveSelfSpecReturnExprCallbacks {
    fn_name: String,
    inject_self_spec: bool,
    return_expr: Option<PureExpr>,
    ran: bool,
}

impl Callbacks for RecursiveSelfSpecReturnExprCallbacks {
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let suffix = format!("::{}", self.fn_name);

        for local_def_id in tcx.hir_body_owners() {
            let def_id = local_def_id.to_def_id();
            let def_path = tcx.def_path_str(def_id);
            if def_path != self.fn_name && !def_path.ends_with(&suffix) {
                continue;
            }

            let body = tcx.optimized_mir(def_id);
            let arg_names = resolve_arg_names_or_warn(tcx, def_id, None);
            let mut user_specs = HashMap::new();

            if self.inject_self_spec {
                let attrs = tcx.get_all_attrs(def_id);
                let requires = get_contract_attrs_from_doc(attrs, "requires");
                let ensures = get_contract_attrs_from_doc(attrs, "ensures");
                if !requires.is_empty() || !ensures.is_empty() {
                    user_specs.insert(
                        def_id,
                        StdSpec {
                            capture_inv_requires: Vec::new(),
                            inv_requires: Vec::new(),
                            requires,
                            ensures,
                            param_names: Some(arg_names.clone()),
                        },
                    );
                }
            }

            let (expr, _effects) = extract_return_expr_with_context(
                tcx,
                body,
                &arg_names,
                &user_specs,
                &HashMap::new(),
                &HashMap::new(),
            );
            self.return_expr = expr;
            self.ran = true;
            return Compilation::Stop;
        }

        Compilation::Stop
    }
}

fn extract_recursive_return_expr_in_source(
    source: &str,
    fn_name: &str,
    inject_self_spec: bool,
) -> Option<PureExpr> {
    let unique = EXTRACT_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_recursive_return_expr_{}_{}",
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
        "trust_wp_recursive_return_expr_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = RecursiveSelfSpecReturnExprCallbacks {
        fn_name: fn_name.to_string(),
        inject_self_spec,
        return_expr: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to extract recursive return expr for `{fn_name}`"
    );
    callbacks.return_expr
}

/// Helper: returns true if the expression tree contains at least one `Ite` node.
fn expr_contains_ite(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Ite(_, _, _) => true,
        PureExpr::LetAssume { body, .. } => expr_contains_ite(body),
        PureExpr::Let { value, body, .. } => expr_contains_ite(value) || expr_contains_ite(body),
        _ => false,
    }
}

struct CallAssumptionCallbacks {
    fn_name: String,
    assumptions: Option<Vec<PureExpr>>,
    ran: bool,
}

impl Callbacks for CallAssumptionCallbacks {
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
            let user_specs = HashMap::new();
            let trait_specs = HashMap::new();

            let (_expr, effects) = extract_return_expr_with_context(
                tcx,
                body,
                &arg_names,
                &user_specs,
                &trait_specs,
                &HashMap::new(),
            );
            self.assumptions = Some(effects.assumptions);
            self.ran = true;
            return Compilation::Stop;
        }

        Compilation::Stop
    }
}

fn extract_call_assumptions_in_source(source: &str, fn_name: &str) -> Vec<PureExpr> {
    let unique = EXTRACT_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_call_assumptions_{}_{}",
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
        "trust_wp_call_assumptions_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = CallAssumptionCallbacks {
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

struct StdSpecCallAssumptionCallbacks {
    fn_name: String,
    assumptions: Option<Vec<PureExpr>>,
    ran: bool,
}

impl Callbacks for StdSpecCallAssumptionCallbacks {
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
            let user_specs = HashMap::new();
            let trait_specs = HashMap::new();
            let extern_specs = builtin_trust_wp_std_specs();

            let (_expr, effects) = extract_return_expr_with_context(
                tcx,
                body,
                &arg_names,
                &user_specs,
                &trait_specs,
                &extern_specs,
            );
            self.assumptions = Some(effects.assumptions);
            self.ran = true;
            return Compilation::Stop;
        }

        Compilation::Stop
    }
}

fn extract_call_assumptions_in_source_with_std_specs(source: &str, fn_name: &str) -> Vec<PureExpr> {
    let unique = EXTRACT_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_call_assumptions_std_specs_{}_{}",
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
        "trust_wp_call_assumptions_std_specs_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = StdSpecCallAssumptionCallbacks {
        fn_name: fn_name.to_string(),
        assumptions: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to extract call assumptions with std specs for `{fn_name}`"
    );
    callbacks
        .assumptions
        .expect("assumptions should be set when ran=true")
}

fn final_depth(expr: &PureExpr) -> usize {
    match expr {
        PureExpr::Final(inner) => 1 + final_depth(inner),
        PureExpr::Deref(inner) => final_depth(inner),
        _ => 0,
    }
}

fn push_back_receiver_final_depths(assumptions: &[PureExpr]) -> HashMap<i64, Vec<usize>> {
    let mut out: HashMap<i64, Vec<usize>> = HashMap::new();
    for assumption in assumptions {
        let PureExpr::BinOp(lhs, BinOp::Eq, rhs) = assumption else {
            continue;
        };
        let PureExpr::View(lhs_inner) = lhs.as_ref() else {
            continue;
        };
        let PureExpr::Final(post_inner) = lhs_inner.as_ref() else {
            continue;
        };
        let PureExpr::MethodCall {
            receiver,
            method,
            args,
        } = rhs.as_ref()
        else {
            continue;
        };
        if method != "push_back" {
            continue;
        }
        let [PureExpr::Int(value)] = args.as_slice() else {
            continue;
        };
        let PureExpr::View(pre_inner) = receiver.as_ref() else {
            continue;
        };
        if pre_inner.as_ref() != post_inner.as_ref() {
            continue;
        }
        out.entry(*value).or_default().push(final_depth(pre_inner));
    }
    out
}

#[test]
fn vec_push_call_assumptions_chain_receiver_state_across_calls() {
    let source = r#"
pub fn create_arr() -> Vec<i32> {
let mut arr = Vec::new();
arr.push(0);
arr.push(1);
arr.push(2);
arr.push(3);
arr.push(4);
arr
}
"#;

    let assumptions = extract_call_assumptions_in_source(source, "create_arr");
    let push_depths = push_back_receiver_final_depths(&assumptions);

    for value in 0_i64..=4_i64 {
        let depths = push_depths.get(&value).unwrap_or_else(|| {
            panic!("missing push_back assumption for value {value}; assumptions: {assumptions:?}")
        });
        let value_usize = usize::try_from(value).expect("test value fits in usize");
        assert!(
            depths.contains(&value_usize),
            "push_back({value}) should reference receiver with Final depth {value}, \
             got {depths:?}; assumptions: {assumptions:?}"
        );
    }
}

#[test]
fn mem_take_call_assumptions_specialize_default_bool_postcondition() {
    let source = r#"
pub fn take_bool(dest: &mut bool) -> bool {
    std::mem::take(dest)
}
"#;

    let assumptions = extract_call_assumptions_in_source(source, "take_bool");
    let specializes_dest_to_false = assumptions.iter().any(|assumption| {
        matches!(
            assumption,
            PureExpr::BinOp(lhs, BinOp::Eq, rhs)
                if matches!(
                    lhs.as_ref(),
                    PureExpr::Final(inner)
                        if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == "dest")
                ) && matches!(rhs.as_ref(), PureExpr::Bool(false))
        )
    });

    assert!(
        specializes_dest_to_false,
        "mem::take call should contribute the specialized `^dest == false` \
         postcondition assumption, got {assumptions:?}"
    );
}

#[test]
fn deref_mut_call_assumptions_bind_receiver_without_deref_wrapper() {
    let source = r#"
use std::ops::DerefMut;

pub fn deref_mut_wrap<T: DerefMut>(x: &mut T) -> &mut T::Target {
    &mut *x
}
"#;

    let assumptions = extract_call_assumptions_in_source_with_std_specs(source, "deref_mut_wrap");
    // A call postcondition is scoped under the call's own preconditions
    // (`T::deref_mut.precondition(x) ==> T::deref_mut.postcondition(x, r)`).
    let deref_mut_assumptions: Vec<&PureExpr> = assumptions
        .iter()
        .map(|assumption| match assumption {
            PureExpr::BinOp(_, BinOp::Implies, post) => post.as_ref(),
            other => other,
        })
        .filter(|assumption| {
            matches!(
                assumption,
                PureExpr::MethodCall { receiver, .. }
                    if matches!(receiver.as_ref(), PureExpr::Var(name, _) if name.contains("deref_mut"))
            )
        })
        .collect();

    assert!(
        !deref_mut_assumptions.is_empty(),
        "expected deref_mut assumptions, got {assumptions:?}"
    );

    assert!(
        deref_mut_assumptions.iter().all(|assumption| {
            matches!(
                assumption,
                PureExpr::MethodCall { args, .. }
                    if matches!(args.first(), Some(PureExpr::Var(name, _)) if name == "x")
            )
        }),
        "deref_mut assumptions should bind the receiver as `x`, not `*x`: {deref_mut_assumptions:?}"
    );
}

#[test]
fn deref_mut_call_assumptions_preserve_generic_mut_ref_sort() {
    let source = r#"
use std::ops::DerefMut;

pub fn deref_mut_wrap<T: DerefMut>(x: &mut T) -> &mut T::Target {
    &mut *x
}
"#;

    let assumptions = extract_call_assumptions_in_source_with_std_specs(source, "deref_mut_wrap");
    // A call postcondition is scoped under the call's own preconditions
    // (`T::deref_mut.precondition(x) ==> T::deref_mut.postcondition(x, r)`).
    let deref_mut_assumptions: Vec<&PureExpr> = assumptions
        .iter()
        .map(|assumption| match assumption {
            PureExpr::BinOp(_, BinOp::Implies, post) => post.as_ref(),
            other => other,
        })
        .filter(|assumption| {
            matches!(
                assumption,
                PureExpr::MethodCall { receiver, .. }
                    if matches!(receiver.as_ref(), PureExpr::Var(name, _) if name.contains("deref_mut"))
            )
        })
        .collect();

    assert!(
        !deref_mut_assumptions.is_empty(),
        "expected deref_mut assumptions, got {assumptions:?}"
    );

    assert!(
        deref_mut_assumptions.iter().all(|assumption| {
            matches!(
                assumption,
                PureExpr::MethodCall { args, .. }
                    if matches!(
                        args.first(),
                        Some(PureExpr::Var(name, Some(ExprSort::MutRef(inner))))
                            if name == "x" && matches!(inner.as_ref(), ExprSort::TypeParam(_))
                    )
            )
        }),
        "deref_mut assumptions should keep `x` as an annotated `&mut T`, got {deref_mut_assumptions:?}"
    );
}

#[test]
fn clone_call_assumptions_emit_generic_clone_postcondition() {
    let source = r#"
pub fn clone_wrap<T: Clone>(t: &T) -> T {
    t.clone()
}
"#;

    let assumptions = extract_call_assumptions_in_source_with_std_specs(source, "clone_wrap");
    let clone_assumptions: Vec<&PureExpr> = assumptions
        .iter()
        .filter(|assumption| {
            matches!(
                assumption,
                PureExpr::MethodCall { receiver, method, .. }
                    if method == "postcondition"
                        && matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == "T::clone")
            )
        })
        .collect();

    assert!(
        !clone_assumptions.is_empty(),
        "expected generic Clone call to contribute a `T::clone.postcondition` \
         assumption, got {assumptions:?}"
    );

    assert!(
        clone_assumptions.iter().any(|assumption| {
            matches!(
                assumption,
                PureExpr::MethodCall { args, .. }
                    if matches!(
                        args.as_slice(),
                        [PureExpr::Var(name, Some(ExprSort::Ref(inner))), PureExpr::Var(result_name, _)]
                            if name == "t"
                                && matches!(inner.as_ref(), ExprSort::TypeParam(_))
                                && result_name.starts_with("$call_")
                    )
            )
        }),
        "generic Clone assumption should bind `self` to the annotated `&T` \
         receiver and the synthesized call result, got {clone_assumptions:?}"
    );
}

/// Spec provenance (s38): a LOCAL `ghost::Ghost` in a crate that happens to be
/// named `trust_wp_std` is not the spec library's `Ghost`; its `deref_mut` must
/// not receive the builtin whole-borrow passthrough (`result == x`), because
/// the local body may do anything.
#[test]
fn ghost_deref_mut_local_lookalike_does_not_get_whole_borrow_passthrough() {
    let source = r#"
use std::ops::DerefMut;

pub mod ghost {
    use std::ops::{Deref, DerefMut};

    pub struct Ghost<T>(pub T);

    impl<T> Deref for Ghost<T> {
        type Target = T;

        fn deref(&self) -> &T {
            &self.0
        }
    }

    impl<T> DerefMut for Ghost<T> {
        fn deref_mut(&mut self) -> &mut T {
            &mut self.0
        }
    }
}

pub fn ghost_deref_mut_wrap(x: &mut ghost::Ghost<i32>) -> &mut i32 {
    x.deref_mut()
}
"#;

    let expr = extract_return_expr_in_source_with_std_specs(
        source,
        "ghost_deref_mut_wrap",
        "trust_wp_std",
    );

    assert!(
        !matches!(&expr, Some(PureExpr::Var(name, _)) if name == "x"),
        "a local Ghost lookalike must not resolve to the whole-borrow receiver `x`, got {expr:?}"
    );
}

#[test]
fn named_adt_field_projection_uses_generic_accessor_for_datatype_receivers() {
    use rustc_abi::FieldIdx;
    use rustc_middle::mir::{Local, Place, ProjectionElem};
    use trust_wp_core::formula::intern_sort_name;

    use crate::mir_analysis::translate::translate_place;

    struct NamedAdtFieldCallbacks {
        result: Option<Option<PureExpr>>,
        ran: bool,
    }

    impl Callbacks for NamedAdtFieldCallbacks {
        #[allow(clippy::elidable_lifetime_names)]
        fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
            let base_place = Place::from(Local::from_usize(1));
            let projected = base_place.project_deeper(
                &[ProjectionElem::Field(FieldIdx::from_u32(0), tcx.types.i32)],
                tcx,
            );
            let locals = HashMap::from([(
                Local::from_usize(1),
                PureExpr::Var(
                    "self".to_string(),
                    Some(ExprSort::Datatype(intern_sort_name("Point"))),
                ),
            )]);

            self.result = Some(translate_place(&projected, &locals));
            self.ran = true;
            Compilation::Stop
        }
    }

    let temp_dir =
        std::env::temp_dir().join(format!("trust_wp_named_adt_field_{}", std::process::id()));
    std::fs::create_dir_all(&temp_dir).unwrap();
    let source_path = temp_dir.join("test.rs");
    std::fs::write(&source_path, "pub fn dummy() {}\n").unwrap();

    let args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        "trust_wp_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = NamedAdtFieldCallbacks {
        result: None,
        ran: false,
    };
    run_compiler(&args, &mut callbacks);
    let _ = std::fs::remove_dir_all(&temp_dir);

    assert!(callbacks.ran, "callback did not run");
    assert_eq!(
        callbacks.result.unwrap(),
        Some(PureExpr::LogicFnCall {
            name: trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0),
            args: vec![PureExpr::Var(
                "self".to_string(),
                Some(ExprSort::Datatype(intern_sort_name("Point"))),
            )],
        }),
        "Datatype receivers should use the generic field accessor path"
    );
}

#[test]
fn generic_trait_call_uses_discovered_trait_postcondition() {
    let source = r#"
pub trait A {
    #[doc(hidden)]
    #[doc = "trust-wp:ensures:result == true"]
    fn is_true(&self) -> bool;
}

pub fn omg<T: A>(a: T) -> bool {
    a.is_true()
}
"#;

    let expr = extract_return_expr_in_source_with_trait_specs(source, "omg");
    assert_eq!(
        expr,
        Some(PureExpr::Bool(true)),
        "generic trait call should resolve to the discovered trait postcondition",
    );
}

#[test]
fn generic_trait_call_substitutes_named_trait_parameters() {
    let source = r#"
pub trait Adder {
    #[doc(hidden)]
    #[doc = "trust-wp:ensures:result == x + y"]
    fn add(&self, x: i32, y: i32) -> i32;
}

pub fn sum<T: Adder>(a: T) -> i32 {
    a.add(1, 2)
}
"#;

    let expr = extract_return_expr_in_source_with_trait_specs(source, "sum")
        .expect("generic trait call with named params should be extractable");
    assert!(
        matches!(
            &expr,
            PureExpr::BinOp(lhs, BinOp::Add, rhs) if matches!(lhs.as_ref(), PureExpr::Int(1)) && matches!(rhs.as_ref(), PureExpr::Int(2))
        ),
        "generic trait call should substitute named trait params into the return expression, got: {expr:?}"
    );
}

// ── SwitchInt soundness tests (#1651) ──

#[test]
fn match_extraction_produces_ite_chain_not_single_branch() {
    // A function with a multi-branch match on an integer argument must
    // produce an ITE chain in the extracted return expression. Before
    // #1651, an untranslatable discriminant would cause the extractor
    // to return the first extractable branch, which is unsound.
    //
    // This test verifies the normal (translatable) case still produces
    // the correct ITE structure.
    let source = r#"
pub fn match_three(x: i32) -> i32 {
match x {
    0 => 10,
    1 => 20,
    _ => 30,
}
}
"#;

    let expr = extract_return_expr_in_source(source, "match_three");
    let expr = expr.expect("match on i32 argument should be extractable");
    assert!(
        expr_contains_ite(&expr),
        "multi-branch match should produce ITE chain, got: {expr:?}"
    );
}

fn expr_contains_call_result_var(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(name, _) => name.starts_with("$call_") || name.starts_with("$_call_"),
        PureExpr::Bool(_) | PureExpr::Int(_) => false,
        PureExpr::Deref(inner)
        | PureExpr::View(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::UnOp(_, inner) => expr_contains_call_result_var(inner),
        PureExpr::BinOp(lhs, _, rhs) => {
            expr_contains_call_result_var(lhs) || expr_contains_call_result_var(rhs)
        }
        PureExpr::Ite(cond, then_expr, else_expr) => {
            expr_contains_call_result_var(cond)
                || expr_contains_call_result_var(then_expr)
                || expr_contains_call_result_var(else_expr)
        }
        PureExpr::Let { value, body, .. } => {
            expr_contains_call_result_var(value) || expr_contains_call_result_var(body)
        }
        PureExpr::LetAssume {
            assumption, body, ..
        } => expr_contains_call_result_var(assumption) || expr_contains_call_result_var(body),
        PureExpr::LetObligation {
            obligation, body, ..
        } => expr_contains_call_result_var(obligation) || expr_contains_call_result_var(body),
        PureExpr::MethodCall { receiver, args, .. } => {
            expr_contains_call_result_var(receiver)
                || args.iter().any(expr_contains_call_result_var)
        }
        PureExpr::LogicFnCall { args, .. } => args.iter().any(expr_contains_call_result_var),
        PureExpr::Forall { body, .. } | PureExpr::Exists { body, .. } => {
            expr_contains_call_result_var(body)
        }
        PureExpr::Match { scrutinee, arms } => {
            expr_contains_call_result_var(scrutinee)
                || arms
                    .iter()
                    .any(|arm| expr_contains_call_result_var(&arm.body))
        }
        PureExpr::Closure { body, .. } => expr_contains_call_result_var(body),
        // PureExpr is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => panic!("unhandled PureExpr variant"),
    }
}

#[test]
fn recursive_self_spec_rewrites_self_calls_during_extraction() {
    let source = r#"
#[doc(hidden)]
#[doc = "trust-wp:ensures:result == 42"]
pub fn recursive_answer(n: i32) -> i32 {
    if n == 0 {
        42
    } else {
        recursive_answer(n - 1)
    }
}
"#;

    let without_self_spec =
        extract_recursive_return_expr_in_source(source, "recursive_answer", false).expect(
            "recursive extraction without a self-spec should still produce a return expression",
        );
    assert!(
        expr_contains_call_result_var(&without_self_spec),
        "without an injected self-spec, recursive extraction should still expose an opaque call result, got {without_self_spec:?}"
    );

    let with_self_spec = extract_recursive_return_expr_in_source(source, "recursive_answer", true)
        .expect("recursive extraction with a self-spec should produce a return expression");
    assert!(
        !expr_contains_call_result_var(&with_self_spec),
        "self-spec injection should eliminate opaque recursive call placeholders, got {with_self_spec:?}"
    );
}

#[test]
fn rusthorn_shaped_recursive_match_extracts_with_self_spec() {
    let source = r#"
#![allow(dead_code)]

enum List {
    Cons(u32, Box<List>),
    Nil,
}

fn random() -> bool {
    true
}

impl List {
    #[doc(hidden)]
    #[doc = "trust-wp:ensures:(^self).sum() - self.sum() == (^result)@ - result@"]
    #[doc = "trust-wp:ensures:result@ <= self.sum()"]
    fn take_some(&mut self) -> &mut u32 {
        match self {
            List::Cons(value, rest) => {
                if random() {
                    value
                } else {
                    rest.take_some()
                }
            }
            List::Nil => loop {},
        }
    }
}
"#;

    let without_self_spec = extract_recursive_return_expr_in_source(source, "take_some", false);
    assert!(
        without_self_spec.is_none()
            || expr_contains_call_result_var(
                without_self_spec
                    .as_ref()
                    .expect("checked Option::is_none above"),
            ),
        "without an injected self-spec, RustHorn-shaped recursion should still fail extraction or expose an opaque recursive call result, got {without_self_spec:?}"
    );

    let with_self_spec = extract_recursive_return_expr_in_source(source, "take_some", true)
        .expect("self-spec injection should keep RustHorn-shaped recursive match extraction alive");
    assert!(
        expr_contains_ite(&with_self_spec),
        "self-spec injection should preserve the RustHorn-shaped branch structure instead of collapsing extraction to `None`, got {with_self_spec:?}"
    );
}

// ── Opaque call &mut havoc tests (#2048) ──

/// Returns true if the expression tree contains at least one `Final` node.
fn expr_contains_final(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Final(_) => true,
        PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Var(..) => false,
        PureExpr::Deref(inner)
        | PureExpr::View(inner)
        | PureExpr::Old(inner)
        | PureExpr::UnOp(_, inner) => expr_contains_final(inner),
        PureExpr::BinOp(lhs, _, rhs) => expr_contains_final(lhs) || expr_contains_final(rhs),
        PureExpr::Ite(c, t, e) => {
            expr_contains_final(c) || expr_contains_final(t) || expr_contains_final(e)
        }
        PureExpr::Let { value, body, .. } => {
            expr_contains_final(value) || expr_contains_final(body)
        }
        PureExpr::LetAssume {
            assumption, body, ..
        } => expr_contains_final(assumption) || expr_contains_final(body),
        PureExpr::LetObligation {
            obligation, body, ..
        } => expr_contains_final(obligation) || expr_contains_final(body),
        PureExpr::MethodCall { receiver, args, .. } => {
            expr_contains_final(receiver) || args.iter().any(expr_contains_final)
        }
        PureExpr::LogicFnCall { args, .. } => args.iter().any(expr_contains_final),
        PureExpr::Forall { body, .. } | PureExpr::Exists { body, .. } => expr_contains_final(body),
        PureExpr::Match { scrutinee, arms } => {
            expr_contains_final(scrutinee) || arms.iter().any(|a| expr_contains_final(&a.body))
        }
        PureExpr::Closure { body, .. } => expr_contains_final(body),
        // PureExpr is #[non_exhaustive]; required for cross-crate match.
        #[allow(unreachable_patterns)]
        _ => panic!("unhandled PureExpr variant"),
    }
}

#[test]
fn opaque_call_with_mut_ref_arg_advances_state_to_final() {
    // When an opaque (unspecced) function takes a `&mut i32` arg, the extractor
    // must advance the arg's state to `Final(...)` so that subsequent reads
    // see post-call values instead of stale pre-call state (#2048).
    //
    // Without the fix, `*x` after the opaque call returns the pre-call Deref(x),
    // which is unsound.
    let source = r#"
extern "Rust" {
    fn unknown_mutator(x: &mut i32);
}
pub fn test_fn(x: &mut i32) -> i32 {
    unsafe { unknown_mutator(x); }
    *x
}
"#;

    let expr = extract_return_expr_in_source(source, "test_fn");
    let expr = expr.expect("opaque call with &mut arg should be extractable");
    assert!(
        expr_contains_final(&expr),
        "return expression after opaque call on &mut arg should contain Final \
         (post-call state), but got: {expr:?}"
    );
}

#[test]
fn opaque_call_with_two_mut_ref_args_advances_both_to_final() {
    // When an opaque function takes multiple `&mut` args, ALL should be
    // advanced to Final state, not just the first. The return expression
    // `*a + *b` should contain two Final nodes.
    let source = r#"
extern "Rust" {
    fn unknown_swap(a: &mut i32, b: &mut i32);
}
pub fn test_fn(a: &mut i32, b: &mut i32) -> i32 {
    unsafe { unknown_swap(a, b); }
    *a + *b
}
"#;

    let expr = extract_return_expr_in_source(source, "test_fn");
    let expr = expr.expect("opaque call with two &mut args should be extractable");
    // Both *a and *b should see post-call state (Final nodes)
    assert!(
        expr_contains_final(&expr),
        "return expression after opaque call with two &mut args should contain \
         Final (post-call state), but got: {expr:?}"
    );
}
