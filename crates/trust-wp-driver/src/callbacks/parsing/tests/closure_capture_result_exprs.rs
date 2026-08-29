// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

#[derive(Default)]
struct ClosureCaptureResultExprProbe {
    ran: bool,
    result_expr: Option<PureExpr>,
    spanned_result_expr: Option<PureExpr>,
}

impl Callbacks for ClosureCaptureResultExprProbe {
    fn config(&mut self, config: &mut Config) {
        install_mir_borrowck_cache(config);
    }

    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let contracts = find_contract_functions(tcx);
        let Some(contract) = contracts
            .iter()
            .find(|contract| tcx.def_kind(contract.def_id) == DefKind::Closure)
        else {
            return Compilation::Stop;
        };
        let user_specs = HashMap::new();
        let trait_specs = HashMap::new();
        let extern_specs = HashMap::new();
        let extraction_ctx =
            ExtractionContext::new(&user_specs, &trait_specs, &extern_specs, false, false);

        let parsed = parse_and_extract_contract(tcx, contract, &HashSet::new(), &extraction_ctx)
            .expect("closure contract should parse and extract");

        self.result_expr = parsed.result_expr.clone();
        self.spanned_result_expr = parsed.result_expr_spanned.map(|sp| sp.expr);
        self.ran = true;
        Compilation::Stop
    }
}

fn collect_closure_capture_result_exprs(source: &str) -> (Option<PureExpr>, Option<PureExpr>) {
    let unique = PARSING_TEST_COUNTER.fetch_add(1, Ordering::Relaxed);
    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_parsing_closure_capture_{}_{}",
        std::process::id(),
        unique,
    ));
    fs::create_dir_all(&temp_dir).expect("create parsing test temp dir");

    let source_path = temp_dir.join("test.rs");
    fs::write(&source_path, source).expect("write parsing test source");

    let args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        "trust_wp_parsing_closure_capture_test".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = ClosureCaptureResultExprProbe::default();
    clear_caches();
    run_compiler(&args, &mut callbacks);
    clear_caches();

    let _ = fs::remove_dir_all(&temp_dir);

    assert!(
        callbacks.ran,
        "failed to inspect closure capture result expression extraction"
    );
    (callbacks.result_expr, callbacks.spanned_result_expr)
}

#[test]
fn parse_and_extract_contract_rewrites_closure_result_expr_to_self_fields() {
    let source = r#"
#![feature(stmt_expr_attributes)]
#![allow(unused_doc_comments)]

pub struct Zero(u32);

pub fn host(x: Zero) {
    let clos = #[doc = "trust-wp:ensures:result == 0"] || { (*&x).0 };
    let _ = clos();
}
"#;

    let (result_expr, spanned_result_expr) = collect_closure_capture_result_exprs(source);
    let result_expr = result_expr.expect("closure contract should extract a result expression");
    let spanned_result_expr =
        spanned_result_expr.expect("closure contract should extract a spanned result expression");

    assert!(
        !result_expr
            .any_recursive(|node| matches!(node, PureExpr::Var(name, _) if name == "self.0.0")),
        "closure result expr should not retain dotted self capture field vars, got {result_expr:?}"
    );
    assert!(
        result_expr.any_recursive(|node| {
            matches!(
                node,
                PureExpr::LogicFnCall { name, args }
                    if name == &tuple_field_logic_fn_name(0)
                        && args.len() == 1
                        && matches!(&args[0], PureExpr::Var(base, _) if base == "self.0")
            )
        }),
        "closure result expr should lower projected self fields to tuple-get selectors, got {result_expr:?}"
    );
    assert!(
        !result_expr.any_recursive(|node| matches!(node, PureExpr::Var(name, _) if name == "x")),
        "closure result expr should not retain the free capture name x, got {result_expr:?}"
    );
    assert!(
        !spanned_result_expr
            .any_recursive(|node| matches!(node, PureExpr::Var(name, _) if name == "self.0.0")),
        "spanned closure result expr should not retain dotted self capture field vars, got {spanned_result_expr:?}"
    );
    assert!(
        spanned_result_expr.any_recursive(|node| {
            matches!(
                node,
                PureExpr::LogicFnCall { name, args }
                    if name == &tuple_field_logic_fn_name(0)
                        && args.len() == 1
                        && matches!(&args[0], PureExpr::Var(base, _) if base == "self.0")
            )
        }),
        "spanned closure result expr should lower projected self fields to tuple-get selectors, got {spanned_result_expr:?}"
    );
    assert!(
        !spanned_result_expr.any_recursive(|node| matches!(node, PureExpr::Var(name, _) if name == "x")),
        "spanned closure result expr should not retain the free capture name x, got {spanned_result_expr:?}"
    );
}
