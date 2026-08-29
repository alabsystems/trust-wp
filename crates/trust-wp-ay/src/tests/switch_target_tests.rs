// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for [`crate::encoder::match_enc::switch_target`] match target inference.
//!
//! Coverage gap: `switch_target.rs` (241 LOC) had zero tests for
//! `short_constructor_name`, `normalize_constructor_name`, `SwitchTarget::from_arms`,
//! `pattern_arity`, `infer_adt_name`, `value_constructor_name`, and `datatype()`.

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::formula::{MatchArm, Pattern, PureExpr};

use crate::encoder::match_enc::{
    is_stdlib_enum_qualifier, normalize_constructor_name, short_constructor_name, SwitchTarget,
};

fn ctor_arm(name: &str, inner: Option<Pattern>) -> MatchArm {
    MatchArm {
        pattern: Pattern::Constructor {
            name: name.to_string(),
            inner: inner.map(Box::new),
        },
        body: PureExpr::Int(0),
    }
}

fn wildcard_arm() -> MatchArm {
    MatchArm {
        pattern: Pattern::Wildcard,
        body: PureExpr::Int(0),
    }
}

// --- short_constructor_name ---

#[test]
#[timeout(30000)]
fn short_constructor_name_unqualified() {
    assert_eq!(short_constructor_name("Some"), "Some");
}

#[test]
#[timeout(30000)]
fn short_constructor_name_qualified() {
    assert_eq!(short_constructor_name("std::option::Option::Some"), "Some");
}

#[test]
#[timeout(30000)]
fn short_constructor_name_single_qualifier() {
    assert_eq!(short_constructor_name("MyEnum::A"), "A");
}

#[test]
#[timeout(30000)]
fn short_constructor_name_named_struct() {
    // "Point{x,y}" -> normalize to "Point", then no :: so return "Point"
    assert_eq!(short_constructor_name("Point{x,y}"), "Point");
}

#[test]
#[timeout(30000)]
fn short_constructor_name_qualified_named_struct() {
    // "MyMod::Point{x,y}" -> normalize to "MyMod::Point" -> short "Point"
    assert_eq!(short_constructor_name("MyMod::Point{x,y}"), "Point");
}

// --- normalize_constructor_name ---

#[test]
#[timeout(30000)]
fn normalize_plain_name_unchanged() {
    assert_eq!(normalize_constructor_name("Some"), "Some");
}

#[test]
#[timeout(30000)]
fn normalize_strips_field_metadata() {
    assert_eq!(normalize_constructor_name("Point{x,y}"), "Point");
}

#[test]
#[timeout(30000)]
fn normalize_preserves_qualified_without_fields() {
    assert_eq!(
        normalize_constructor_name("std::option::Option::None"),
        "std::option::Option::None"
    );
}

// --- SwitchTarget::from_arms ---

#[test]
#[timeout(30000)]
fn from_arms_option_some_none() {
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
#[timeout(30000)]
fn from_arms_result_ok_err() {
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
#[timeout(30000)]
fn from_arms_user_defined_enum() {
    let arms = vec![
        ctor_arm("MyEnum::A", Some(Pattern::Binding("x".to_string()))),
        ctor_arm("MyEnum::B", None),
    ];
    let result = SwitchTarget::from_arms(&arms);
    match result {
        Some(SwitchTarget::UserDefined {
            adt_name,
            constructors,
        }) => {
            assert_eq!(adt_name, "MyEnum");
            assert_eq!(constructors.len(), 2);
            assert_eq!(constructors[0].0, "MyEnum::A");
            assert_eq!(constructors[0].1.len(), 1); // arity 1
            assert_eq!(constructors[1].0, "MyEnum::B");
            assert_eq!(constructors[1].1.len(), 0); // arity 0
        }
        other => panic!("expected UserDefined, got {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn from_arms_no_constructors_returns_none() {
    let arms = vec![wildcard_arm()];
    assert_eq!(SwitchTarget::from_arms(&arms), None);
}

#[test]
#[timeout(30000)]
fn from_arms_empty_returns_none() {
    assert_eq!(SwitchTarget::from_arms(&[]), None);
}

#[test]
#[timeout(30000)]
fn from_arms_mixed_known_types_returns_none() {
    // Some + Err is invalid (mixed Option + Result)
    let arms = vec![
        ctor_arm("Some", Some(Pattern::Binding("x".to_string()))),
        ctor_arm("Err", Some(Pattern::Binding("e".to_string()))),
    ];
    assert_eq!(SwitchTarget::from_arms(&arms), None);
}

#[test]
#[timeout(30000)]
fn from_arms_qualified_option_recognized() {
    let arms = vec![
        ctor_arm(
            "std::option::Option::Some",
            Some(Pattern::Binding("x".to_string())),
        ),
        ctor_arm("std::option::Option::None", None),
    ];
    assert_eq!(
        SwitchTarget::from_arms(&arms),
        Some(SwitchTarget::OptionInt)
    );
}

#[test]
#[timeout(30000)]
fn from_arms_tuple_pattern_arity() {
    let arms = vec![ctor_arm(
        "MyEnum::Pair",
        Some(Pattern::Tuple(vec![
            Pattern::Binding("a".to_string()),
            Pattern::Binding("b".to_string()),
        ])),
    )];
    match SwitchTarget::from_arms(&arms) {
        Some(SwitchTarget::UserDefined { constructors, .. }) => {
            assert_eq!(constructors[0].1.len(), 2, "tuple arity should be 2");
        }
        other => panic!("expected UserDefined, got {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn from_arms_wildcard_plus_constructor() {
    // Wildcard arms are ignored; constructor arms still classify
    let arms = vec![
        ctor_arm("Some", Some(Pattern::Binding("x".to_string()))),
        wildcard_arm(),
    ];
    assert_eq!(
        SwitchTarget::from_arms(&arms),
        Some(SwitchTarget::OptionInt)
    );
}

// --- value_constructor_name ---

#[test]
#[timeout(30000)]
fn value_constructor_name_option() {
    assert_eq!(SwitchTarget::OptionInt.value_constructor_name(), "Some");
}

#[test]
#[timeout(30000)]
fn value_constructor_name_result() {
    assert_eq!(SwitchTarget::ResultIntInt.value_constructor_name(), "Ok");
}

#[test]
#[timeout(30000)]
fn value_constructor_name_user_defined_picks_first_with_payload() {
    let target = SwitchTarget::UserDefined {
        adt_name: "MyEnum".to_string(),
        constructors: vec![
            ("MyEnum::Empty".to_string(), vec![]),
            ("MyEnum::Data".to_string(), vec![Sort::Int]),
        ],
    };
    assert_eq!(target.value_constructor_name(), "Data");
}

#[test]
#[timeout(30000)]
fn value_constructor_name_user_defined_fallback_first() {
    // All constructors have arity 0; falls back to first
    let target = SwitchTarget::UserDefined {
        adt_name: "Unit2".to_string(),
        constructors: vec![("A".to_string(), vec![]), ("B".to_string(), vec![])],
    };
    assert_eq!(target.value_constructor_name(), "A");
}

// --- infer_adt_name ---

#[test]
#[timeout(30000)]
fn infer_adt_name_from_qualified_path() {
    let arms = vec![ctor_arm("Color::Red", None), ctor_arm("Color::Blue", None)];
    match SwitchTarget::from_arms(&arms) {
        Some(SwitchTarget::UserDefined { adt_name, .. }) => {
            assert_eq!(adt_name, "Color");
        }
        other => panic!("expected UserDefined, got {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn infer_adt_name_synthesized_from_unqualified() {
    let arms = vec![ctor_arm("Red", None), ctor_arm("Blue", None)];
    match SwitchTarget::from_arms(&arms) {
        Some(SwitchTarget::UserDefined { adt_name, .. }) => {
            assert_eq!(adt_name, "Adt_Blue_Red", "sorted alphabetically");
        }
        other => panic!("expected UserDefined, got {other:?}"),
    }
}

// --- datatype() construction ---

#[test]
#[timeout(30000)]
fn datatype_option_int_structure() {
    let dt = SwitchTarget::OptionInt.datatype();
    assert_eq!(dt.name, "OptionInt");
    assert_eq!(dt.constructors.len(), 2);
    assert_eq!(dt.constructors[0].name, "None");
    assert!(dt.constructors[0].fields.is_empty());
    assert_eq!(dt.constructors[1].name, "Some");
    assert_eq!(dt.constructors[1].fields.len(), 1);
    assert_eq!(dt.constructors[1].fields[0].sort, Sort::Int);
}

#[test]
#[timeout(30000)]
fn datatype_result_int_int_structure() {
    let dt = SwitchTarget::ResultIntInt.datatype();
    assert_eq!(dt.name, "ResultIntInt");
    assert_eq!(dt.constructors.len(), 2);
    assert_eq!(dt.constructors[0].name, "Ok");
    assert_eq!(dt.constructors[0].fields[0].sort, Sort::Int);
    assert_eq!(dt.constructors[1].name, "Err");
    assert_eq!(dt.constructors[1].fields[0].sort, Sort::Int);
}

#[test]
#[timeout(30000)]
fn datatype_user_defined_structure() {
    let target = SwitchTarget::UserDefined {
        adt_name: "MyEnum".to_string(),
        constructors: vec![
            ("MyEnum::A".to_string(), vec![Sort::Int]),
            ("MyEnum::B".to_string(), vec![]),
        ],
    };
    let dt = target.datatype();
    assert_eq!(dt.name, "MyEnum");
    assert_eq!(dt.constructors.len(), 2);
    assert_eq!(dt.constructors[0].name, "A");
    assert_eq!(dt.constructors[0].fields.len(), 1);
    assert_eq!(dt.constructors[0].fields[0].name, "myenum_a_0");
    assert_eq!(dt.constructors[1].name, "B");
    assert!(dt.constructors[1].fields.is_empty());
}

#[test]
#[timeout(30000)]
fn datatype_user_defined_multi_field() {
    let target = SwitchTarget::UserDefined {
        adt_name: "Pair".to_string(),
        constructors: vec![("Pair::MkPair".to_string(), vec![Sort::Int, Sort::Int])],
    };
    let dt = target.datatype();
    assert_eq!(dt.constructors[0].fields.len(), 2);
    assert_eq!(dt.constructors[0].fields[0].name, "pair_mkpair_0");
    assert_eq!(dt.constructors[0].fields[1].name, "pair_mkpair_1");
}

// --- is_stdlib_enum_qualifier (#2462) ---

#[test]
#[timeout(30000)]
fn stdlib_qualifier_unqualified_ok() {
    assert!(is_stdlib_enum_qualifier("Ok", "Ok"));
}

#[test]
#[timeout(30000)]
fn stdlib_qualifier_result_ok() {
    assert!(is_stdlib_enum_qualifier("Result::Ok", "Ok"));
}

#[test]
#[timeout(30000)]
fn stdlib_qualifier_std_result_ok() {
    assert!(is_stdlib_enum_qualifier("std::result::Result::Ok", "Ok"));
}

#[test]
#[timeout(30000)]
fn stdlib_qualifier_option_some() {
    assert!(is_stdlib_enum_qualifier("Option::Some", "Some"));
}

#[test]
#[timeout(30000)]
fn stdlib_qualifier_std_option_none() {
    assert!(is_stdlib_enum_qualifier(
        "std::option::Option::None",
        "None"
    ));
}

#[test]
#[timeout(30000)]
fn stdlib_qualifier_own_result_ok_is_not_stdlib() {
    assert!(!is_stdlib_enum_qualifier("OwnResult::Ok", "Ok"));
}

#[test]
#[timeout(30000)]
fn stdlib_qualifier_my_enum_err_is_not_stdlib() {
    assert!(!is_stdlib_enum_qualifier("MyEnum::Err", "Err"));
}

#[test]
#[timeout(30000)]
fn stdlib_qualifier_custom_some_is_not_stdlib() {
    assert!(!is_stdlib_enum_qualifier("CustomOption::Some", "Some"));
}

// --- from_arms: OwnResult regression (#2462) ---

#[test]
#[timeout(30000)]
fn from_arms_own_result_ok_err_is_user_defined() {
    let arms = vec![
        ctor_arm("OwnResult::Ok", Some(Pattern::Binding("v".to_string()))),
        ctor_arm("OwnResult::Err", Some(Pattern::Binding("e".to_string()))),
    ];
    match SwitchTarget::from_arms(&arms) {
        Some(SwitchTarget::UserDefined {
            adt_name,
            constructors,
        }) => {
            assert_eq!(adt_name, "OwnResult");
            assert_eq!(constructors.len(), 2);
            assert_eq!(constructors[0].0, "OwnResult::Ok");
            assert_eq!(constructors[1].0, "OwnResult::Err");
        }
        other => panic!("expected UserDefined for OwnResult, got {other:?}"),
    }
}

#[test]
#[timeout(30000)]
fn from_arms_qualified_result_ok_err_is_still_result() {
    let arms = vec![
        ctor_arm("Result::Ok", Some(Pattern::Binding("v".to_string()))),
        ctor_arm("Result::Err", Some(Pattern::Binding("e".to_string()))),
    ];
    assert_eq!(
        SwitchTarget::from_arms(&arms),
        Some(SwitchTarget::ResultIntInt)
    );
}
