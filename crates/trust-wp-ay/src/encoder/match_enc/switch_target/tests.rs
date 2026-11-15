// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for match target inference and datatype construction helpers.

use trust_wp_core::formula::{MatchArm, Pattern, PureExpr};

use super::*;

// -- short_constructor_name --

#[test]
fn test_short_constructor_name_unqualified() {
    assert_eq!(short_constructor_name("Some"), "Some");
}

#[test]
fn test_short_constructor_name_qualified() {
    assert_eq!(short_constructor_name("Option::Some"), "Some");
}

#[test]
fn test_short_constructor_name_deeply_qualified() {
    assert_eq!(short_constructor_name("std::result::Result::Ok"), "Ok");
}

#[test]
fn test_short_constructor_name_user_defined() {
    assert_eq!(short_constructor_name("MyEnum::Variant"), "Variant");
}

#[test]
fn test_short_constructor_name_named_struct_ctor() {
    // Named struct constructors like "Point{x,y}" normalize before splitting.
    let result = short_constructor_name("Point{x,y}");
    assert_eq!(result, "Point");
}

// -- normalize_constructor_name --

#[test]
fn test_normalize_constructor_name_plain() {
    assert_eq!(normalize_constructor_name("Ok"), "Ok");
}

#[test]
fn test_normalize_constructor_name_named_struct() {
    assert_eq!(normalize_constructor_name("Point{x,y}"), "Point");
}

#[test]
fn test_normalize_constructor_name_no_braces() {
    assert_eq!(normalize_constructor_name("MyEnum::A"), "MyEnum::A");
}

// -- is_stdlib_enum_qualifier --

#[test]
fn test_is_stdlib_enum_qualifier_unqualified() {
    assert!(is_stdlib_enum_qualifier("Some", "Some"));
}

#[test]
fn test_is_stdlib_enum_qualifier_option_qualified() {
    assert!(is_stdlib_enum_qualifier("Option::Some", "Some"));
}

#[test]
fn test_is_stdlib_enum_qualifier_result_qualified() {
    assert!(is_stdlib_enum_qualifier("Result::Ok", "Ok"));
}

#[test]
fn test_is_stdlib_enum_qualifier_user_defined_returns_false() {
    assert!(!is_stdlib_enum_qualifier("OwnResult::Ok", "Ok"));
}

#[test]
fn test_is_stdlib_enum_qualifier_deeply_qualified_option() {
    // std::option::Option::Some — base qualifier is "Option"
    assert!(is_stdlib_enum_qualifier(
        "std::option::Option::Some",
        "Some"
    ));
}

// -- stdlib_constructor_target --

#[test]
fn test_stdlib_constructor_target_some() {
    assert_eq!(
        stdlib_constructor_target("Some"),
        Some(SwitchTarget::OptionInt)
    );
}

#[test]
fn test_stdlib_constructor_target_none() {
    assert_eq!(
        stdlib_constructor_target("None"),
        Some(SwitchTarget::OptionInt)
    );
}

#[test]
fn test_stdlib_constructor_target_ok() {
    assert_eq!(
        stdlib_constructor_target("Ok"),
        Some(SwitchTarget::ResultIntInt)
    );
}

#[test]
fn test_stdlib_constructor_target_err() {
    assert_eq!(
        stdlib_constructor_target("Err"),
        Some(SwitchTarget::ResultIntInt)
    );
}

#[test]
fn test_stdlib_constructor_target_qualified_option() {
    assert_eq!(
        stdlib_constructor_target("Option::Some"),
        Some(SwitchTarget::OptionInt)
    );
}

#[test]
fn test_stdlib_constructor_target_user_defined_returns_none() {
    assert_eq!(stdlib_constructor_target("OwnResult::Ok"), None);
}

#[test]
fn test_stdlib_constructor_target_unknown_returns_none() {
    assert_eq!(stdlib_constructor_target("Foo"), None);
}

// -- is_stdlib_payload_constructor --

#[test]
fn test_is_stdlib_payload_constructor_some() {
    assert!(is_stdlib_payload_constructor("Some"));
}

#[test]
fn test_is_stdlib_payload_constructor_ok() {
    assert!(is_stdlib_payload_constructor("Ok"));
}

#[test]
fn test_is_stdlib_payload_constructor_err() {
    assert!(is_stdlib_payload_constructor("Err"));
}

#[test]
fn test_is_stdlib_payload_constructor_none_returns_false() {
    // None is nullary — no payload
    assert!(!is_stdlib_payload_constructor("None"));
}

#[test]
fn test_is_stdlib_payload_constructor_user_defined_returns_false() {
    assert!(!is_stdlib_payload_constructor("OwnResult::Ok"));
}

// -- SwitchTarget::from_arms --

fn ctor_arm(name: &str, inner: Option<Pattern>) -> MatchArm {
    MatchArm {
        pattern: Pattern::Constructor {
            name: name.to_string(),
            inner: inner.map(Box::new),
        },
        body: PureExpr::Int(0),
    }
}

#[test]
fn test_from_arms_option() {
    let arms = vec![
        ctor_arm("Some", Some(Pattern::Binding("x".to_string()))),
        ctor_arm("None", None),
    ];
    assert_eq!(
        SwitchTarget::from_arms(&arms),
        Some(SwitchTarget::OptionInt)
    );
}

#[test]
fn test_from_arms_result() {
    let arms = vec![
        ctor_arm("Ok", Some(Pattern::Binding("v".to_string()))),
        ctor_arm("Err", Some(Pattern::Binding("e".to_string()))),
    ];
    assert_eq!(
        SwitchTarget::from_arms(&arms),
        Some(SwitchTarget::ResultIntInt)
    );
}

#[test]
fn test_from_arms_no_constructors_returns_none() {
    let arms = vec![MatchArm {
        pattern: Pattern::Wildcard,
        body: PureExpr::Int(0),
    }];
    assert_eq!(SwitchTarget::from_arms(&arms), None);
}

#[test]
fn test_from_arms_user_defined_enum() {
    let arms = vec![
        ctor_arm("MyEnum::A", Some(Pattern::Binding("x".to_string()))),
        ctor_arm("MyEnum::B", None),
    ];
    let result = SwitchTarget::from_arms(&arms);
    match result {
        Some(SwitchTarget::UserDefined {
            ref adt_name,
            ref constructors,
        }) => {
            assert_eq!(adt_name, "MyEnum");
            assert_eq!(constructors.len(), 2);
        }
        other => panic!("expected UserDefined, got {other:?}"),
    }
}

#[test]
fn test_from_arms_mixed_stdlib_returns_none() {
    // Some + Err is mixed stdlib — should return None
    let arms = vec![
        ctor_arm("Some", Some(Pattern::Binding("x".to_string()))),
        ctor_arm("Err", Some(Pattern::Binding("e".to_string()))),
    ];
    assert_eq!(SwitchTarget::from_arms(&arms), None);
}

// -- SwitchTarget::datatype --

#[test]
fn test_datatype_option_has_two_constructors() {
    let dt = SwitchTarget::OptionInt.datatype();
    assert_eq!(dt.name, "OptionInt");
    assert_eq!(dt.constructors.len(), 2);
    assert_eq!(dt.constructors[0].name, "None");
    assert!(dt.constructors[0].fields.is_empty());
    assert_eq!(dt.constructors[1].name, "Some");
    assert_eq!(dt.constructors[1].fields.len(), 1);
}

#[test]
fn test_datatype_result_has_two_constructors() {
    let dt = SwitchTarget::ResultIntInt.datatype();
    assert_eq!(dt.name, "ResultIntInt");
    assert_eq!(dt.constructors.len(), 2);
    assert_eq!(dt.constructors[0].name, "Ok");
    assert_eq!(dt.constructors[1].name, "Err");
}

#[test]
fn test_datatype_user_defined_field_naming() {
    let target = SwitchTarget::UserDefined {
        adt_name: "MyAdt".to_string(),
        constructors: vec![("MyAdt::Leaf".to_string(), vec![Sort::Int, Sort::Bool])],
    };
    let dt = target.datatype();
    assert_eq!(dt.name, "MyAdt");
    assert_eq!(dt.constructors.len(), 1);
    assert_eq!(dt.constructors[0].name, "Leaf");
    assert_eq!(dt.constructors[0].fields.len(), 2);
    assert_eq!(dt.constructors[0].fields[0].name, "myadt_leaf_0");
    assert_eq!(dt.constructors[0].fields[1].name, "myadt_leaf_1");
}

// -- SwitchTarget::pattern_arity --

#[test]
fn test_pattern_arity_none() {
    assert_eq!(SwitchTarget::pattern_arity(None), 0);
}

#[test]
fn test_pattern_arity_single_binding() {
    assert_eq!(
        SwitchTarget::pattern_arity(Some(&Pattern::Binding("x".to_string()))),
        1
    );
}

#[test]
fn test_pattern_arity_tuple() {
    let tuple = Pattern::Tuple(vec![
        Pattern::Binding("a".to_string()),
        Pattern::Binding("b".to_string()),
    ]);
    assert_eq!(SwitchTarget::pattern_arity(Some(&tuple)), 2);
}

// -- SwitchTarget::infer_adt_name --

#[test]
fn test_infer_adt_name_from_qualified_path() {
    let ctors = vec![("MyEnum::A".to_string(), vec![Sort::Int])];
    assert_eq!(SwitchTarget::infer_adt_name(&ctors), "MyEnum");
}

#[test]
fn test_infer_adt_name_synthesized_from_unqualified() {
    let ctors = vec![
        ("B".to_string(), vec![]),
        ("A".to_string(), vec![Sort::Int]),
    ];
    // Names are sorted: A, B
    assert_eq!(SwitchTarget::infer_adt_name(&ctors), "Adt_A_B");
}

// -- Edge case: Option::None arm only (single-arm match) --

#[test]
fn test_from_arms_option_none_only() {
    // A single None arm still classifies as Option
    let arms = vec![ctor_arm("None", None)];
    assert_eq!(
        SwitchTarget::from_arms(&arms),
        Some(SwitchTarget::OptionInt)
    );
}

#[test]
fn test_from_arms_option_qualified_none() {
    // Qualified Option::None classifies correctly
    let arms = vec![
        ctor_arm("Option::Some", Some(Pattern::Binding("v".to_string()))),
        ctor_arm("Option::None", None),
    ];
    assert_eq!(
        SwitchTarget::from_arms(&arms),
        Some(SwitchTarget::OptionInt)
    );
}

// -- Edge case: Result::Err variant arm with nested patterns --

#[test]
fn test_from_arms_result_err_with_tuple_pattern() {
    // Err arm wrapping a tuple pattern — arity should be 2
    let err_inner = Pattern::Tuple(vec![
        Pattern::Binding("code".to_string()),
        Pattern::Binding("msg".to_string()),
    ]);
    let arms = vec![
        ctor_arm("Ok", Some(Pattern::Binding("v".to_string()))),
        ctor_arm("Err", Some(err_inner)),
    ];
    assert_eq!(
        SwitchTarget::from_arms(&arms),
        Some(SwitchTarget::ResultIntInt)
    );
}

#[test]
fn test_datatype_result_err_field_name() {
    // Verify the Err constructor field is named correctly
    let dt = SwitchTarget::ResultIntInt.datatype();
    let err_ctor = &dt.constructors[1];
    assert_eq!(err_ctor.name, "Err");
    assert_eq!(err_ctor.fields.len(), 1);
    assert_eq!(err_ctor.fields[0].name, "result_err_error");
    assert_eq!(err_ctor.fields[0].sort, Sort::Int);
}

// -- Edge case: Default/wildcard arm handling --

#[test]
fn test_from_arms_wildcard_only_returns_none() {
    // Only wildcard arms — no constructors, should return None
    let arms = vec![
        MatchArm {
            pattern: Pattern::Wildcard,
            body: PureExpr::Int(42),
        },
        MatchArm {
            pattern: Pattern::Wildcard,
            body: PureExpr::Int(0),
        },
    ];
    assert_eq!(SwitchTarget::from_arms(&arms), None);
}

#[test]
fn test_from_arms_constructor_with_wildcard_arm() {
    // Mix of constructor arms and a wildcard fallback — constructors drive classification
    let arms = vec![
        ctor_arm("Some", Some(Pattern::Binding("x".to_string()))),
        MatchArm {
            pattern: Pattern::Wildcard,
            body: PureExpr::Int(0),
        },
    ];
    // Wildcard is ignored for classification; Some alone → OptionInt
    assert_eq!(
        SwitchTarget::from_arms(&arms),
        Some(SwitchTarget::OptionInt)
    );
}

// -- Edge case: User-defined enum with all-nullary constructors --

#[test]
fn test_datatype_option_none_constructor_is_nullary() {
    let dt = SwitchTarget::OptionInt.datatype();
    let none_ctor = &dt.constructors[0];
    assert_eq!(none_ctor.name, "None");
    assert!(none_ctor.fields.is_empty(), "None should have no fields");
}

#[test]
fn test_pattern_arity_wildcard_as_inner() {
    // Wildcard as inner pattern of a constructor → arity 1
    assert_eq!(SwitchTarget::pattern_arity(Some(&Pattern::Wildcard)), 1);
}
