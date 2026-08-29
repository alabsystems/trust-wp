// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// P1-74: Additional prefix false positive boundary tests (#1965)
// -----------------------------------------------------------------------------

#[test]
#[timeout(30000)]
fn test_sorts_are_related_two_char_prefix_false_positive() {
    // Two-char type name "Op" is a prefix of "OptionInt". This is also a
    // false positive, but more plausible than single-char "R" — real Rust types
    // like `Op`, `Fn`, `Id` exist. Document that the prefix check still
    // over-approximates for short names. (#1965, P1-74)
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("x", Sort::Uninterpreted("Op".to_string()));
    assert!(first.is_ok());

    let dt = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "val".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
        ],
    };
    // "Op" is a prefix of "OptionInt" → sorts_are_related returns true.
    // This is a false positive: "Op" and "Option" are different types.
    // Accepted because: (1) real Rust ADTs use PascalCase ≥4 chars,
    // (2) the conservative direction (Datatype→Uninterpreted) only
    // suppresses the conflict without mutating sort. (#1965, P1-74)
    let second = encoder.get_or_declare_var("x", Sort::Datatype(dt));
    assert!(
        second.is_ok(),
        "Two-char prefix 'Op' matches 'OptionInt' — accepted over-approximation: {second:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_sorts_are_related_prefix_but_not_type_parameter_boundary() {
    // "Hash" vs "HashMap" — both are real Rust types. "Hash" is a prefix of
    // "HashMap" but they are semantically unrelated. This tests the most
    // plausible false positive scenario with non-normalized type names.
    // (Vec/VecDeque is mitigated by normalize_sort mapping Vec→Seq, so use
    // a pair that doesn't hit normalization.) (#1965, P1-74)
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("h", Sort::Uninterpreted("Hash".to_string()));
    assert!(first.is_ok());

    let dt = DatatypeSort {
        name: "HashMap".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "HM".to_string(),
            fields: vec![DatatypeField {
                name: "data".to_string(),
                sort: Sort::Int,
            }],
        }],
    };
    // "HashMap".starts_with("Hash") is true → sorts_are_related returns true.
    // This is a false positive: "Hash" and "HashMap" are different types.
    // The prefix check is designed for generic instantiation patterns
    // (e.g., HashMapIntInt), but also matches type name substrings.
    // Accepted because: (1) the upgrade direction keeps the more-precise
    // Datatype sort, and (2) the suppression direction preserves existing
    // sort without mutation. Neither direction introduces unsoundness from
    // this false positive. (#1965, P1-74)
    let second = encoder.get_or_declare_var("h", Sort::Datatype(dt));
    assert!(
        second.is_ok(),
        "'Hash' prefix matches 'HashMap' — accepted false positive: {second:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_sorts_are_related_case_sensitive_rejects_wrong_case() {
    // Prefix check is case-sensitive (PascalCase). "option" should NOT
    // match "OptionInt" — Rust types are PascalCase and the mismatch
    // signals a different semantic origin. (#1965, P1-74)
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("x", Sort::Uninterpreted("option".to_string()));
    assert!(first.is_ok());

    let dt = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "val".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
        ],
    };
    // "option" is NOT a prefix of "OptionInt" (case-sensitive)
    let second = encoder.get_or_declare_var("x", Sort::Datatype(dt));
    assert!(
        second.is_err(),
        "Lowercase 'option' should NOT match 'OptionInt' (case-sensitive prefix): {second:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_sorts_are_related_adt_synthesized_partial_segment_upgrades() {
    // Uninterpreted("So") -> Datatype(Adt_Some_None) should SUCCEED: the
    // is_synthesized_adt bypass accepts all non-encoding Uninterpreted sorts
    // for Adt_ datatypes. (#2231, previously #1965 P1-74 expected error)
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("x", Sort::Uninterpreted("So".to_string()));
    assert!(first.is_ok());

    let dt = DatatypeSort {
        name: "Adt_Some_None".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "f".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
        ],
    };
    let second = encoder.get_or_declare_var("x", Sort::Datatype(dt));
    assert!(
        second.is_ok(),
        "Uninterpreted('So') -> Datatype(Adt_Some_None) should upgrade via synthesized Adt bypass: {second:?}"
    );
}

// =============================================================================
// Sort normalization in get_or_declare_var (#1965)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_normalizes_vec_to_seq() {
    // Uninterpreted("std::vec::Vec") should be normalized to Sort::Seq(Int)
    // so that seq_len/seq_index operations work correctly. (#1965, #2080)
    let mut encoder = AYEncoder::new();

    let result = encoder.get_or_declare_var("v", Sort::Uninterpreted("std::vec::Vec".to_string()));
    assert!(result.is_ok());
    assert_eq!(
        encoder.var_sort("v"),
        Some(&Sort::seq(Sort::Int)),
        "std::vec::Vec should be normalized to Seq"
    );
}

/// List-sorted variable (bare name) should stay as Uninterpreted. (#2231)
///
/// `List` was removed from `is_seq_model_type` because in Creusot compat tests,
/// `List` is a user-defined recursive enum (`Cons | Nil`) that must use Datatype
/// encoding, not Seq. The standard library list type is `LinkedList`.
#[test]
#[timeout(30000)]
fn test_get_or_declare_var_list_stays_uninterpreted_2231() {
    let mut encoder = AYEncoder::new();

    let result = encoder.get_or_declare_var("l", Sort::Uninterpreted("List".to_string()));
    assert!(result.is_ok());
    assert_eq!(
        encoder.var_sort("l"),
        Some(&Sort::Uninterpreted("List".to_string())),
        "List should stay as Uninterpreted (not normalized to Seq) (#2231)"
    );
}

/// Qualified List type should also stay as Uninterpreted. (#2231)
#[test]
#[timeout(30000)]
fn test_get_or_declare_var_qualified_list_stays_uninterpreted_2231() {
    let mut encoder = AYEncoder::new();

    let result =
        encoder.get_or_declare_var("l", Sort::Uninterpreted("creusot_test::List".to_string()));
    assert!(result.is_ok());
    assert_eq!(
        encoder.var_sort("l"),
        Some(&Sort::Uninterpreted("List".to_string())),
        "creusot_test::List should stay as Uninterpreted (not normalized to Seq) (#2231)"
    );
}

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_normalizes_fmap_to_fmap() {
    // Uninterpreted("creusot_std::FMap") should be normalized to the canonical
    // FMap sort. (#1965)
    let mut encoder = AYEncoder::new();

    let result =
        encoder.get_or_declare_var("m", Sort::Uninterpreted("creusot_std::FMap".to_string()));
    assert!(result.is_ok());
    // FMap sort is Uninterpreted("FMap")
    assert_eq!(
        encoder.var_sort("m"),
        Some(&Sort::Uninterpreted("FMap".to_string())),
        "creusot_std::FMap should be normalized to FMap"
    );
}

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_normalizes_duration_to_int() {
    // Uninterpreted("std::time::Duration") should be normalized to Int. (#1965)
    let mut encoder = AYEncoder::new();

    let result =
        encoder.get_or_declare_var("d", Sort::Uninterpreted("std::time::Duration".to_string()));
    assert!(result.is_ok());
    assert_eq!(
        encoder.var_sort("d"),
        Some(&Sort::Int),
        "std::time::Duration should be normalized to Int"
    );
}

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_normalization_prevents_vec_seq_conflict() {
    // If v is first declared as normalized-from-Vec (→ Seq), and then
    // requested as Seq directly, there should be no conflict. (#1965)
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("v", Sort::Uninterpreted("std::vec::Vec".to_string()));
    assert!(first.is_ok());

    let second = encoder.get_or_declare_var("v", Sort::seq(Sort::Int));
    assert!(
        second.is_ok(),
        "Vec (normalized to Seq) then Seq should not conflict: {second:?}"
    );
}

/// HashSet-sorted variable should be normalized to Int (FSet encoding). (#2155)
#[test]
#[timeout(30000)]
fn test_get_or_declare_var_normalizes_hashset_to_int_2155() {
    let mut encoder = AYEncoder::new();

    let result = encoder.get_or_declare_var(
        "s",
        Sort::Uninterpreted("std::collections::HashSet".to_string()),
    );
    assert!(result.is_ok());
    assert_eq!(
        encoder.var_sort("s"),
        Some(&Sort::Int),
        "std::collections::HashSet should be normalized to Int for FSet encoding (#2155)"
    );
}

/// Variable declared as Seq then requested as Datatype(OptionInt) should
/// upgrade to OptionInt. The Seq was a speculative pre-scan result; the
/// match encoding's OptionInt Datatype is definitively more specific. (#2155)
#[test]
#[timeout(30000)]
fn test_get_or_declare_var_seq_to_option_datatype_upgrade_2155() {
    let mut encoder = AYEncoder::new();

    // First: prescan declares result as Seq
    let first = encoder.get_or_declare_var("result", Sort::seq(Sort::Int));
    assert!(first.is_ok());
    assert_eq!(encoder.var_sort("result"), Some(&Sort::seq(Sort::Int)));

    // Declare the OptionInt datatype
    let dt = ay_dpll::api::DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            ay_dpll::api::DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
            ay_dpll::api::DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![ay_dpll::api::DatatypeField {
                    name: "option_some_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);

    // Second: match encoding requests Datatype(OptionInt) — should upgrade
    let second = encoder.get_or_declare_var("result", Sort::Datatype(dt));
    assert!(
        second.is_ok(),
        "Seq → Datatype(OptionInt) upgrade should succeed: {second:?}"
    );
    assert!(
        matches!(encoder.var_sort("result"), Some(Sort::Datatype(ref dt)) if dt.name == "OptionInt"),
        "result should be upgraded to OptionInt Datatype sort (#2155)"
    );
}

/// Variable declared as Seq then requested as Datatype(ResultIntInt) should
/// upgrade. Same logic as OptionInt case. (#2155)
#[test]
#[timeout(30000)]
fn test_get_or_declare_var_seq_to_result_datatype_upgrade_2155() {
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("result", Sort::seq(Sort::Int));
    assert!(first.is_ok());

    let dt = ay_dpll::api::DatatypeSort {
        name: "ResultIntInt".to_string(),
        constructors: vec![
            ay_dpll::api::DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![ay_dpll::api::DatatypeField {
                    name: "result_ok_value".to_string(),
                    sort: Sort::Int,
                }],
            },
            ay_dpll::api::DatatypeConstructor {
                name: "Err".to_string(),
                fields: vec![ay_dpll::api::DatatypeField {
                    name: "result_err_error".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);

    let second = encoder.get_or_declare_var("result", Sort::Datatype(dt));
    assert!(
        second.is_ok(),
        "Seq → Datatype(ResultIntInt) upgrade should succeed: {second:?}"
    );
    assert!(
        matches!(encoder.var_sort("result"), Some(Sort::Datatype(ref dt)) if dt.name == "ResultIntInt"),
        "result should be upgraded to ResultIntInt Datatype sort (#2155)"
    );
}

/// FMap-sorted variable then requested as Datatype(OptionInt) should upgrade.
/// FMap pre-scan can also misattribute collection operations. (#2155)
#[test]
#[timeout(30000)]
fn test_get_or_declare_var_fmap_to_option_datatype_upgrade_2155() {
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("result", Sort::Uninterpreted("FMap".to_string()));
    assert!(first.is_ok());

    let dt = ay_dpll::api::DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            ay_dpll::api::DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
            ay_dpll::api::DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![ay_dpll::api::DatatypeField {
                    name: "option_some_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);

    let second = encoder.get_or_declare_var("result", Sort::Datatype(dt));
    assert!(
        second.is_ok(),
        "FMap → Datatype(OptionInt) upgrade should succeed: {second:?}"
    );
}

/// Synthesized Datatypes (Adt_*) should upgrade from encoding sort. (#2231)
///
/// When a variable was speculatively declared as Seq(Int) from sort inference
/// (e.g., because the type name matched is_seq_model_type) but match encoding
/// later reveals it's a user-defined recursive ADT, the Datatype sort should
/// win. This is the inverse of the #2155 well-known Datatype upgrade, but for
/// synthesized ADT names like Adt_Cons_Nil.
#[test]
#[timeout(30000)]
fn test_get_or_declare_var_seq_to_synthesized_adt_upgrades_2231() {
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("x", Sort::seq(Sort::Int));
    assert!(first.is_ok());

    let dt = ay_dpll::api::DatatypeSort {
        name: "Adt_Cons_Nil".to_string(),
        constructors: vec![
            ay_dpll::api::DatatypeConstructor {
                name: "Cons".to_string(),
                fields: vec![
                    ay_dpll::api::DatatypeField {
                        name: "adt_cons_nil_cons_0".to_string(),
                        sort: Sort::Int,
                    },
                    ay_dpll::api::DatatypeField {
                        name: "adt_cons_nil_cons_1".to_string(),
                        sort: Sort::Int,
                    },
                ],
            },
            ay_dpll::api::DatatypeConstructor {
                name: "Nil".to_string(),
                fields: vec![],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);

    let second = encoder.get_or_declare_var("x", Sort::Datatype(dt));
    assert!(
        second.is_ok(),
        "Seq → Datatype(Adt_Cons_Nil) should upgrade for synthesized ADTs (#2231): {second:?}"
    );
    assert!(
        matches!(encoder.var_sort("x"), Some(Sort::Datatype(_))),
        "Variable sort should be upgraded to Datatype after Seq → Adt_Cons_Nil upgrade"
    );
}
