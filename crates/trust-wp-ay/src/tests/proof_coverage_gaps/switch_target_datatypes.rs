// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::Sort;
use ntest::timeout;

use super::*;
use crate::{MatchArm, Pattern};

// =============================================================================
// 2. SwitchTarget::datatype — UserDefined branch
// =============================================================================

/// Verify that `SwitchTarget::datatype()` for UserDefined produces correct
/// DatatypeSort structure with proper field naming.
///
/// Re: #901 — UserDefined branch of SwitchTarget::datatype has zero direct tests
#[test]
#[timeout(30000)]
fn test_switch_target_user_defined_datatype_structure() {
    let target = SwitchTarget::UserDefined {
        adt_name: "Color".to_string(),
        constructors: vec![
            ("Color::Red".to_string(), vec![]),
            ("Color::Green".to_string(), vec![Sort::Int]),
            ("Color::Blue".to_string(), vec![Sort::Int, Sort::Int]),
        ],
    };

    let dt = target.datatype();

    assert_eq!(dt.name, "Color", "ADT name should be 'Color'");
    assert_eq!(
        dt.constructors.len(),
        3,
        "should have 3 constructors: Red, Green, Blue"
    );

    // Red: 0 fields
    assert_eq!(dt.constructors[0].name, "Red");
    assert_eq!(
        dt.constructors[0].fields.len(),
        0,
        "Red should have 0 fields"
    );

    // Green: 1 field
    assert_eq!(dt.constructors[1].name, "Green");
    assert_eq!(
        dt.constructors[1].fields.len(),
        1,
        "Green should have 1 field"
    );
    assert_eq!(
        dt.constructors[1].fields[0].name, "color_green_0",
        "field name format: {{adt_lowercase}}_{{ctor_lowercase}}_{{index}}"
    );
    assert_eq!(
        dt.constructors[1].fields[0].sort,
        Sort::Int,
        "UserDefined fields default to Sort::Int"
    );

    // Blue: 2 fields
    assert_eq!(dt.constructors[2].name, "Blue");
    assert_eq!(
        dt.constructors[2].fields.len(),
        2,
        "Blue should have 2 fields"
    );
    assert_eq!(dt.constructors[2].fields[0].name, "color_blue_0");
    assert_eq!(dt.constructors[2].fields[1].name, "color_blue_1");
}

/// Verify that `SwitchTarget::from_arms()` assigns all fields as Sort::Int
/// for user-defined ADTs, including recursive ones like cons-lists.
///
/// Pattern nodes carry no type information, so all field sorts default to Int.
/// The unsound recursive ADT heuristic was removed in #2189.
///
/// Re: #2155 sub-problem 2, #2189
#[test]
#[timeout(30000)]
fn test_switch_target_recursive_adt_self_referential_field_sort() {
    use trust_wp_core::formula::{MatchArm, Pattern, PureExpr};

    // List::Cons(head, tail) + List::Nil — classic recursive cons-list
    let arms = vec![
        MatchArm {
            pattern: Pattern::Constructor {
                name: "List::Cons".to_string(),
                inner: Some(Box::new(Pattern::Tuple(vec![
                    Pattern::Binding("head".to_string()),
                    Pattern::Binding("tail".to_string()),
                ]))),
            },
            body: PureExpr::Int(0),
        },
        MatchArm {
            pattern: Pattern::Constructor {
                name: "List::Nil".to_string(),
                inner: None,
            },
            body: PureExpr::Int(0),
        },
    ];

    let target = SwitchTarget::from_arms(&arms).expect("should produce UserDefined");
    let dt = target.datatype();

    assert_eq!(dt.name, "List", "ADT name should be 'List'");
    assert_eq!(dt.constructors.len(), 2);

    // Cons: 2 fields — both Sort::Int (no recursive sort inference, #2189)
    let cons = &dt.constructors[0];
    assert_eq!(cons.name, "Cons");
    assert_eq!(cons.fields.len(), 2);
    assert_eq!(cons.fields[0].sort, Sort::Int, "head field should be Int");
    assert_eq!(
        cons.fields[1].sort,
        Sort::Int,
        "tail field should be Int (recursive sort heuristic removed, #2189)"
    );

    // Nil: 0 fields (base case)
    let nil = &dt.constructors[1];
    assert_eq!(nil.name, "Nil");
    assert_eq!(nil.fields.len(), 0);
}

/// Verify that non-recursive ADTs have all Sort::Int field sorts.
///
/// Re: #2155 sub-problem 2, #2189 — all user-defined ADT fields default to Int
#[test]
#[timeout(30000)]
fn test_switch_target_non_recursive_adt_no_self_ref() {
    use trust_wp_core::formula::{MatchArm, Pattern, PureExpr};

    // Pair::First(a, b) + Pair::Second(a, b) — no nullary base case
    let arms = vec![
        MatchArm {
            pattern: Pattern::Constructor {
                name: "Pair::First".to_string(),
                inner: Some(Box::new(Pattern::Tuple(vec![
                    Pattern::Binding("a".to_string()),
                    Pattern::Binding("b".to_string()),
                ]))),
            },
            body: PureExpr::Int(0),
        },
        MatchArm {
            pattern: Pattern::Constructor {
                name: "Pair::Second".to_string(),
                inner: Some(Box::new(Pattern::Tuple(vec![
                    Pattern::Binding("x".to_string()),
                    Pattern::Binding("y".to_string()),
                ]))),
            },
            body: PureExpr::Int(1),
        },
    ];

    let target = SwitchTarget::from_arms(&arms).expect("should produce UserDefined");
    let dt = target.datatype();

    assert_eq!(dt.name, "Pair");
    // Both constructors have 2 fields, all Int (heuristic removed, #2189)
    for ctor in &dt.constructors {
        for field in &ctor.fields {
            assert_eq!(
                field.sort,
                Sort::Int,
                "non-recursive ADT field '{}' should be Int",
                field.name
            );
        }
    }
}

/// Verify that `SwitchTarget::datatype()` for OptionInt produces the expected
/// structure (positive control for comparison with UserDefined).
///
/// Re: #901 — baseline control for datatype() tests
#[test]
#[timeout(30000)]
fn test_switch_target_option_int_datatype_structure() {
    let dt = SwitchTarget::OptionInt.datatype();

    assert_eq!(dt.name, "OptionInt");
    assert_eq!(dt.constructors.len(), 2);
    assert_eq!(dt.constructors[0].name, "None");
    assert_eq!(dt.constructors[0].fields.len(), 0);
    assert_eq!(dt.constructors[1].name, "Some");
    assert_eq!(dt.constructors[1].fields.len(), 1);
    assert_eq!(dt.constructors[1].fields[0].name, "option_some_value");
    assert_eq!(dt.constructors[1].fields[0].sort, Sort::Int);
}

/// Verify that `SwitchTarget::datatype()` for ResultIntInt produces the expected
/// structure.
///
/// Re: #901 — baseline control for datatype() tests
#[test]
#[timeout(30000)]
fn test_switch_target_result_int_int_datatype_structure() {
    let dt = SwitchTarget::ResultIntInt.datatype();

    assert_eq!(dt.name, "ResultIntInt");
    assert_eq!(dt.constructors.len(), 2);
    assert_eq!(dt.constructors[0].name, "Ok");
    assert_eq!(dt.constructors[0].fields.len(), 1);
    assert_eq!(dt.constructors[0].fields[0].name, "result_ok_value");
    assert_eq!(dt.constructors[1].name, "Err");
    assert_eq!(dt.constructors[1].fields.len(), 1);
    assert_eq!(dt.constructors[1].fields[0].name, "result_err_error");
}

/// Verify that `SwitchTarget::from_arms` infers UserDefined correctly for
/// custom enum constructors and that `datatype()` round-trips cleanly.
///
/// Re: #901 — from_arms → datatype integration
#[test]
#[timeout(30000)]
fn test_switch_target_from_arms_user_defined_round_trip() {
    let arms = vec![
        MatchArm {
            pattern: Pattern::Constructor {
                name: "Direction::North".to_string(),
                inner: None,
            },
            body: int(0),
        },
        MatchArm {
            pattern: Pattern::Constructor {
                name: "Direction::South".to_string(),
                inner: None,
            },
            body: int(1),
        },
        MatchArm {
            pattern: Pattern::Constructor {
                name: "Direction::East".to_string(),
                inner: Some(Box::new(Pattern::Binding("speed".to_string()))),
            },
            body: var("speed"),
        },
    ];

    let target = SwitchTarget::from_arms(&arms).expect("should infer UserDefined");
    let dt = target.datatype();

    assert_eq!(dt.name, "Direction", "ADT name from qualified path prefix");
    assert_eq!(dt.constructors.len(), 3);

    // North: 0 fields (no inner pattern)
    assert_eq!(dt.constructors[0].name, "North");
    assert_eq!(dt.constructors[0].fields.len(), 0);

    // South: 0 fields
    assert_eq!(dt.constructors[1].name, "South");
    assert_eq!(dt.constructors[1].fields.len(), 0);

    // East: 1 field (Binding pattern = arity 1)
    assert_eq!(dt.constructors[2].name, "East");
    assert_eq!(dt.constructors[2].fields.len(), 1);
}
