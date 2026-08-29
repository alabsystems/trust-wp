// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::logic::{LogicFnDef, LogicMode};

use super::*;

/// A logic function declared with a non-reserved `ExprSort::Datatype`
/// parameter should retain that uninterpreted family instead of defaulting to
/// Int. (#1943)
#[test]
#[timeout(30000)]
fn test_declare_logic_fn_with_datatype_param_sort_hint() {
    use trust_wp_core::formula::{intern_sort_name, ExprSort};

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Build a LogicFnDef with an explicit Datatype param sort, simulating the
    // path: ParamSortHint::Datatype("UserOption") → ExprSort::Datatype(id).
    let dt_id = intern_sort_name("UserOption");
    let logic_fn = LogicFnDef::new(
        "unwrap_option".to_string(),
        "test::unwrap_option".to_string(),
        vec!["opt".to_string()],
        // Body: just return 0 — the sort of the parameter is what we test.
        int(0),
    )
    .with_param_sorts(vec![Some(ExprSort::Datatype(dt_id))])
    .with_mode(LogicMode::Open);

    encoder
        .register_logic_fn(&logic_fn)
        .expect("Logic fn with Datatype param sort should register");

    let smt_name = trust_wp_core::logic::logic_fn_smt_name("unwrap_option");
    let func_decl = encoder
        .decls()
        .get_logic_func(&smt_name)
        .expect("unwrap_option should be declared");

    // The custom domain sort should remain uninterpreted, not default to Int.
    let domain = func_decl.domain();
    assert_eq!(domain.len(), 1, "Expected 1 parameter");
    assert_eq!(
        domain[0],
        Sort::Uninterpreted("UserOption".to_string()),
        "custom datatype hint should produce Sort::Uninterpreted(\"UserOption\"), got {:?}",
        domain[0]
    );
}

/// Reserved standard datatype hints use the canonical native AY datatype.
#[test]
#[timeout(30000)]
fn test_declare_logic_fn_with_reserved_option_param_sort_hint() {
    use trust_wp_core::formula::{intern_sort_name, ExprSort};

    let mut encoder = AYEncoder::new_with_quantifiers();
    let logic_fn = LogicFnDef::new(
        "unwrap_standard_option".to_string(),
        "test::unwrap_standard_option".to_string(),
        vec!["opt".to_string()],
        int(0),
    )
    .with_param_sorts(vec![Some(ExprSort::Datatype(intern_sort_name(
        "OptionInt",
    )))])
    .with_mode(LogicMode::Open);

    encoder
        .register_logic_fn(&logic_fn)
        .expect("logic function with OptionInt parameter should register");

    let smt_name = trust_wp_core::logic::logic_fn_smt_name("unwrap_standard_option");
    let domain = encoder
        .decls()
        .get_logic_func(&smt_name)
        .expect("unwrap_standard_option should be declared")
        .domain();
    assert!(
        matches!(&domain[0], Sort::Datatype(dt) if dt.name == "OptionInt"),
        "reserved OptionInt parameter must use the native datatype: {:?}",
        domain[0]
    );
}
