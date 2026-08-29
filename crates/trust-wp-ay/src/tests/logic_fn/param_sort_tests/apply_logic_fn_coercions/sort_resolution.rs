// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// Test that sort_from_expr_sort resolves ExprSort::Datatype to the
/// native ay Sort::Datatype when the datatype has been declared. (#2002)
///
/// Uses "Tree" because it is unambiguously a user-defined ADT,
/// not a collection model type. (List was removed from
/// is_seq_model_type in #2231.)
#[test]
#[timeout(30000)]
fn test_sort_from_expr_sort_uses_declared_datatype() {
    use ay_dpll::api::DatatypeSort;
    use trust_wp_core::formula::{intern_sort_name, ExprSort};

    let mut encoder = AYEncoder::new_with_quantifiers();

    // Before declaring the datatype, ExprSort::Datatype("Tree") should
    // fall back to Uninterpreted
    let sort_before = encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("Tree")));
    assert!(
        matches!(sort_before, Sort::Uninterpreted(ref s) if s == "Tree"),
        "Before declaration, should be Uninterpreted: {sort_before:?}"
    );

    // Declare the Tree datatype (as would happen from match encoding)
    let dt = DatatypeSort {
        name: "Tree".to_string(),
        constructors: vec![
            ay_dpll::api::DatatypeConstructor {
                name: "Node".to_string(),
                fields: vec![
                    ay_dpll::api::DatatypeField {
                        name: "tree_node_0".to_string(),
                        sort: Sort::Int,
                    },
                    ay_dpll::api::DatatypeField {
                        name: "tree_node_1".to_string(),
                        sort: Sort::Int,
                    },
                ],
            },
            ay_dpll::api::DatatypeConstructor {
                name: "Leaf".to_string(),
                fields: vec![],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);

    // After declaring, ExprSort::Datatype("Tree") should resolve to
    // Sort::Datatype(dt)
    let sort_after = encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("Tree")));
    assert!(
        matches!(sort_after, Sort::Datatype(_)),
        "After declaration, should be Datatype: {sort_after:?}"
    );

    // Also test with qualified name (driver produces "module::Tree")
    let sort_qualified =
        encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("inc_some_tree::Tree")));
    assert!(
        matches!(sort_qualified, Sort::Datatype(_)),
        "Qualified name should also resolve to Datatype: {sort_qualified:?}"
    );
}

/// Registered logic function whose body calls another logic function that
/// returns Seq should get Seq return sort when a Seq sort hint is present.
/// Before #994 fix, only Bool hints overrode the Int default from
/// `infer_expr_sort(body)`. (#994)
#[test]
#[timeout(30000)]
fn test_declare_logic_fn_seq_return_from_hint() {
    let mut encoder = AYEncoder::new_with_quantifiers();

    // Pre-register a Seq sort hint for the function. This simulates what
    // the prescan does when the function appears in a Seq-producing context.
    let smt_name = trust_wp_core::logic::logic_fn_smt_name("get_items");
    encoder.record_sort_hint(smt_name.clone(), trust_wp_core::formula::ExprSort::Seq);

    // The body calls another logic function (which defaults to Int in
    // infer_expr_sort). The Seq hint should override this.
    let logic_fn = LogicFnDef::new(
        "get_items".to_string(),
        "test::get_items".to_string(),
        vec!["x".to_string()],
        logic_fn_call("inner_get", vec![var("x")]),
    )
    .with_mode(LogicMode::Open);

    encoder
        .register_logic_fn(&logic_fn)
        .expect("Seq-returning logic fn should register without error");

    // The declared function's return sort should be Seq.
    let func_decl = encoder
        .decls()
        .get_logic_func(&smt_name)
        .expect("get_items should be declared");
    let return_sort = func_decl.range();
    assert!(
        return_sort.is_seq(),
        "Logic fn with Seq hint should have Seq return sort, got {return_sort:?}"
    );
}
