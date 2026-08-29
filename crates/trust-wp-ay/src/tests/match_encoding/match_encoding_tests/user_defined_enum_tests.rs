// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Match expression encoding tests for trust-wp-ay.

use trust_wp_core::formula::Pattern;

use super::*;

// =========================================================================
// User-defined enum tests (#1578 — SwitchTarget::UserDefined)
// =========================================================================

/// User-defined enum with two constructors: `Leaf(v)` and `Node(v)`.
/// Before #1578, this fell through to `None` from `MatchDatatypeKind::from_arms`
/// and used only UF tester fallback. Now it declares a native ay datatype.
#[test]
#[timeout(30000)]
fn test_encode_match_user_defined_enum() {
    let mut encoder = AYEncoder::new();

    // match tree { Leaf(v) => v, Node(v) => v + 1 }
    let expr = match_expr(
        var("tree"),
        vec![
            (
                Pattern::Constructor {
                    name: "Leaf".into(),
                    inner: Some(Box::new(Pattern::Binding("v".into()))),
                },
                var("v"),
            ),
            (
                Pattern::Constructor {
                    name: "Node".into(),
                    inner: Some(Box::new(Pattern::Binding("w".into()))),
                },
                add(var("w"), int(1)),
            ),
        ],
    );

    let match_term = encoder
        .encode_pure(&expr)
        .expect("User-defined enum should encode without error");

    // A user-defined ADT should be declared (not OptionInt/ResultIntInt)
    assert!(
        !encoder.decls().datatypes_is_empty(),
        "User-defined enum should declare a datatype"
    );
    assert!(
        !encoder.decls().has_datatype("OptionInt"),
        "Should not declare OptionInt for user-defined enum"
    );
    assert!(
        !encoder.decls().has_datatype("ResultIntInt"),
        "Should not declare ResultIntInt for user-defined enum"
    );

    // The declared datatype should have Leaf and Node constructors
    let dt_name = encoder
        .decls()
        .datatype_names()
        .next()
        .expect("exactly one datatype declared")
        .clone();
    let dt = encoder.decls().get_datatype(&dt_name).unwrap().clone();
    let ctor_names: Vec<&str> = dt.constructors.iter().map(|c| c.name.as_str()).collect();
    assert!(
        ctor_names.contains(&"Leaf"),
        "Datatype should contain Leaf constructor, got: {ctor_names:?}"
    );
    assert!(
        ctor_names.contains(&"Node"),
        "Datatype should contain Node constructor, got: {ctor_names:?}"
    );

    // Semantic: when tree is Leaf(42), the first arm matches and result == 42.
    let tree = *encoder.vars_for_test().get("tree").unwrap();
    let is_leaf = encoder.solver.datatype_tester("Leaf", tree);
    let leaf_field = &dt
        .constructors
        .iter()
        .find(|c| c.name == "Leaf")
        .unwrap()
        .fields[0]
        .name;
    let payload = encoder
        .solver
        .datatype_selector(leaf_field, tree, Sort::Int);
    let forty_two = encoder.solver.int_const(42);
    let payload_eq_42 = encoder.solver.eq(payload, forty_two);
    let match_eq_42 = encoder.solver.eq(match_term, forty_two);
    let match_neq_42 = encoder.solver.not(match_eq_42);
    encoder.solver.assert_term(is_leaf);
    encoder.solver.assert_term(payload_eq_42);
    encoder.solver.assert_term(match_neq_42);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "When tree is Leaf(42), match should return 42 (UNSAT expected)"
    );
}

/// User-defined enum with qualified constructor paths: `Color::Red`, `Color::Blue`.
/// Tests that `SwitchTarget::infer_adt_name` extracts `"Color"` from qualified paths.
#[test]
#[timeout(30000)]
fn test_encode_match_user_defined_enum_qualified_paths() {
    let mut encoder = AYEncoder::new();

    // match c { Color::Red => 0, Color::Blue => 1 }
    let expr = match_expr(
        var("c"),
        vec![
            (
                Pattern::Constructor {
                    name: "Color::Red".into(),
                    inner: None,
                },
                int(0),
            ),
            (
                Pattern::Constructor {
                    name: "Color::Blue".into(),
                    inner: None,
                },
                int(1),
            ),
        ],
    );

    let match_term = encoder
        .encode_pure(&expr)
        .expect("Qualified constructor paths should encode without error");

    // ADT name should be "Color" (extracted from qualified paths)
    assert!(
        encoder.decls().has_datatype("Color"),
        "ADT name should be 'Color', got: {:?}",
        encoder.decls().datatype_names().collect::<Vec<_>>()
    );

    let dt = encoder.decls().get_datatype("Color").unwrap().clone();
    assert_eq!(dt.constructors.len(), 2, "Color should have 2 constructors");
    let ctor_names: Vec<&str> = dt.constructors.iter().map(|c| c.name.as_str()).collect();
    assert!(
        ctor_names.contains(&"Red") && ctor_names.contains(&"Blue"),
        "Constructors should be Red and Blue, got: {ctor_names:?}"
    );

    // Both constructors should be nullary (no fields)
    for ctor in &dt.constructors {
        assert!(
            ctor.fields.is_empty(),
            "Constructor {} should be nullary, has {} fields",
            ctor.name,
            ctor.fields.len()
        );
    }

    // Semantic: when c is Red, result should be 0
    let c = *encoder.vars_for_test().get("c").unwrap();
    let red_term = encoder.solver.datatype_constructor(&dt, "Red", &[]);
    let c_eq_red = encoder.solver.eq(c, red_term);
    let zero = encoder.solver.int_const(0);
    let match_eq_0 = encoder.solver.eq(match_term, zero);
    let match_neq_0 = encoder.solver.not(match_eq_0);
    encoder.solver.assert_term(c_eq_red);
    encoder.solver.assert_term(match_neq_0);
    assert!(
        matches!(encoder.check_sat(), SolveResult::Unsat(_)),
        "When c is Color::Red, match should return 0 (UNSAT expected)"
    );
}

/// Unit test for `SwitchTarget::from_arms` classification logic.
#[test]
#[timeout(30000)]
#[allow(clippy::too_many_lines)]
fn test_switch_target_from_arms_classification() {
    use ay_dpll::api::Sort;

    use crate::encoder::match_enc::SwitchTarget;

    // Option arms → OptionInt
    let option_arms = vec![
        MatchArm {
            pattern: Pattern::Constructor {
                name: "Some".into(),
                inner: Some(Box::new(Pattern::Binding("v".into()))),
            },
            body: PureExpr::Int(1),
        },
        MatchArm {
            pattern: Pattern::Constructor {
                name: "None".into(),
                inner: None,
            },
            body: PureExpr::Int(0),
        },
    ];
    assert_eq!(
        SwitchTarget::from_arms(&option_arms),
        Some(SwitchTarget::OptionInt),
        "Some/None arms should classify as OptionInt"
    );

    // Result arms → ResultIntInt
    let result_arms = vec![
        MatchArm {
            pattern: Pattern::Constructor {
                name: "Ok".into(),
                inner: Some(Box::new(Pattern::Binding("v".into()))),
            },
            body: PureExpr::Int(1),
        },
        MatchArm {
            pattern: Pattern::Constructor {
                name: "Err".into(),
                inner: Some(Box::new(Pattern::Binding("e".into()))),
            },
            body: PureExpr::Int(0),
        },
    ];
    assert_eq!(
        SwitchTarget::from_arms(&result_arms),
        Some(SwitchTarget::ResultIntInt),
        "Ok/Err arms should classify as ResultIntInt"
    );

    // User-defined arms → UserDefined
    let custom_arms = vec![
        MatchArm {
            pattern: Pattern::Constructor {
                name: "Leaf".into(),
                inner: Some(Box::new(Pattern::Binding("v".into()))),
            },
            body: PureExpr::Int(1),
        },
        MatchArm {
            pattern: Pattern::Constructor {
                name: "Branch".into(),
                inner: None,
            },
            body: PureExpr::Int(0),
        },
    ];
    let target = SwitchTarget::from_arms(&custom_arms);
    assert!(
        matches!(target, Some(SwitchTarget::UserDefined { .. })),
        "Custom constructors should classify as UserDefined, got: {target:?}"
    );
    if let Some(SwitchTarget::UserDefined {
        adt_name,
        constructors,
    }) = &target
    {
        assert_eq!(adt_name, "Adt_Branch_Leaf");
        assert_eq!(constructors.len(), 2);
        assert_eq!(constructors[0], ("Leaf".to_string(), vec![Sort::Int]));
        assert_eq!(constructors[1], ("Branch".to_string(), vec![]));
    }

    // No constructors → None
    let no_ctor_arms = vec![MatchArm {
        pattern: Pattern::Wildcard,
        body: PureExpr::Int(0),
    }];
    assert_eq!(
        SwitchTarget::from_arms(&no_ctor_arms),
        None,
        "Arms without constructors should return None"
    );

    // Mixed Option + Result constructors → None (not a valid ADT)
    let mixed_known_arms = vec![
        MatchArm {
            pattern: Pattern::Constructor {
                name: "Some".into(),
                inner: Some(Box::new(Pattern::Binding("x".into()))),
            },
            body: PureExpr::Int(1),
        },
        MatchArm {
            pattern: Pattern::Constructor {
                name: "Err".into(),
                inner: Some(Box::new(Pattern::Binding("e".into()))),
            },
            body: PureExpr::Int(0),
        },
    ];
    assert_eq!(
        SwitchTarget::from_arms(&mixed_known_arms),
        None,
        "Mixed Option + Result constructors should return None"
    );

    // Mixed known + custom constructors → None (ambiguous)
    let mixed_known_custom_arms = vec![
        MatchArm {
            pattern: Pattern::Constructor {
                name: "Ok".into(),
                inner: Some(Box::new(Pattern::Binding("v".into()))),
            },
            body: PureExpr::Int(1),
        },
        MatchArm {
            pattern: Pattern::Constructor {
                name: "Custom".into(),
                inner: None,
            },
            body: PureExpr::Int(0),
        },
    ];
    assert_eq!(
        SwitchTarget::from_arms(&mixed_known_custom_arms),
        None,
        "Mixed known + custom constructors should return None"
    );
}
