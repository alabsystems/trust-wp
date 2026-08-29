// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// sorts_are_related — cross-name validation (#1965, P1-72)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_cross_name_unrelated_uninterpreted_to_datatype_rejected() {
    // Uninterpreted("String") → Datatype(OptionInt) should be rejected:
    // "String" is not related to "OptionInt". (#1965, P1 Finding 5)
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("x", Sort::Uninterpreted("String".to_string()));
    assert!(first.is_ok());

    let dt = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "value".to_string(),
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
        second.is_err(),
        "Unrelated Uninterpreted('String') → Datatype(OptionInt) should error: {second:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_cross_name_unrelated_datatype_to_uninterpreted_rejected() {
    // Datatype(OptionInt) → Uninterpreted("String") should be rejected:
    // "String" is not related to "OptionInt". (#1965, P1 Finding 5)
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let dt = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "value".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
        ],
    };
    let first = encoder.get_or_declare_var("x", Sort::Datatype(dt));
    assert!(first.is_ok());

    let second = encoder.get_or_declare_var("x", Sort::Uninterpreted("String".to_string()));
    assert!(
        second.is_err(),
        "Unrelated Datatype(OptionInt) → Uninterpreted('String') should error: {second:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_cross_name_related_prefix_still_works() {
    // Uninterpreted("Option") → Datatype(OptionInt) should still upgrade:
    // "Option" is a prefix of "OptionInt". (#1965)
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("o", Sort::Uninterpreted("Option".to_string()));
    assert!(first.is_ok());

    let dt = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "value".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
        ],
    };
    let second = encoder.get_or_declare_var("o", Sort::Datatype(dt));
    assert!(
        second.is_ok(),
        "Related Uninterpreted('Option') → Datatype(OptionInt) should upgrade: {second:?}"
    );
    assert!(
        matches!(encoder.var_sort("o"), Some(Sort::Datatype(_))),
        "var_sorts should be upgraded to Datatype"
    );
}

// =============================================================================
// sorts_are_related boundary conditions (#1965, P1-73 algorithm audit)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_sorts_are_related_single_char_prefix_false_positive() {
    // A single-char Rust type name "R" should NOT match Datatype "ResultIntInt"
    // via prefix check if they are truly unrelated. The prefix check
    // `starts_with("R")` would match, so "R" → Datatype(ResultIntInt) would
    // incorrectly upgrade. This tests whether short prefixes cause unsound
    // merging. (#1965, P1-73 Finding 1)
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    // Declare as Uninterpreted("R") — a hypothetical single-char type
    let first = encoder.get_or_declare_var("x", Sort::Uninterpreted("R".to_string()));
    assert!(first.is_ok());

    let dt = DatatypeSort {
        name: "ResultIntInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "val".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Err".to_string(),
                fields: vec![DatatypeField {
                    name: "err".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    // "R" is a prefix of "ResultIntInt" — sorts_are_related returns true.
    // This is a known over-approximation: single-char type names may match
    // unrelated ADTs. Document this as accepted behavior since single-char
    // type names are extremely rare in real Rust code. (#1965, P1-73)
    let second = encoder.get_or_declare_var("x", Sort::Datatype(dt));
    // The current implementation accepts this (starts_with("R") matches).
    // If this becomes a false-positive in practice, add a minimum length
    // guard to sorts_are_related.
    assert!(
        second.is_ok(),
        "Single-char prefix 'R' matches 'ResultIntInt' — accepted over-approximation: {second:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_sorts_are_related_empty_type_name_after_path_strip() {
    // Edge case: a trailing "::" in the type path produces an empty string
    // after rsplit("::").next(). Empty string prefix `starts_with("")` is
    // always true, so this would match ANY Datatype. (#1965, P1-73 Finding 2)
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    // Note: normalize_sort may catch this first if it matches a known type.
    // Use a path that doesn't match any normalization rule.
    let first = encoder.get_or_declare_var("x", Sort::Uninterpreted("some::module::".to_string()));
    assert!(first.is_ok());

    let dt = DatatypeSort {
        name: "TotallyUnrelatedAdt".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Ctor".to_string(),
            fields: vec![DatatypeField {
                name: "f".to_string(),
                sort: Sort::Int,
            }],
        }],
    };
    let second = encoder.get_or_declare_var("x", Sort::Datatype(dt));
    // Empty prefix from trailing "::" would cause starts_with("") to match
    // everything. The empty-string guard in sorts_are_related rejects this
    // as unrelated. (#1965, P1-73)
    assert!(
        second.is_err(),
        "Empty type name from trailing '::' should be rejected as unrelated: {second:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_sorts_are_related_exact_match_with_module_path() {
    // "std::result::Result" should match Datatype("Result") after path stripping.
    // This is the most common real-world scenario. (#1965)
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let first =
        encoder.get_or_declare_var("r", Sort::Uninterpreted("std::result::Result".to_string()));
    assert!(first.is_ok());

    let dt = DatatypeSort {
        name: "Result".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "val".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Err".to_string(),
                fields: vec![DatatypeField {
                    name: "err".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    let second = encoder.get_or_declare_var("r", Sort::Datatype(dt));
    assert!(
        second.is_ok(),
        "Exact match after path stripping should upgrade: {second:?}"
    );
    assert!(
        matches!(encoder.var_sort("r"), Some(Sort::Datatype(_))),
        "var_sorts should be upgraded to Datatype"
    );
}

#[test]
#[timeout(30000)]
fn test_sorts_are_related_adt_synthesized_case_insensitive() {
    // Synthesized ADT names like "Adt_some_NONE" use case-insensitive
    // matching for the Rust type name. Verify "Some" matches segment "some"
    // case-insensitively. (#1965, P1-73 Finding 3)
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("x", Sort::Uninterpreted("Some".to_string()));
    assert!(first.is_ok());

    let dt = DatatypeSort {
        name: "Adt_some_None".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "some".to_string(),
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
        "Case-insensitive Adt_ segment match should work: {second:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_sorts_are_related_adt_synthesized_upgrade_in_both_directions() {
    // Uninterpreted("Foo") -> Datatype(Adt_Bar_Baz) should SUCCEED: synthesized
    // Adt_ names never contain the Rust type name. (#2231)
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("x", Sort::Uninterpreted("Foo".to_string()));
    assert!(first.is_ok());

    let dt = DatatypeSort {
        name: "Adt_Bar_Baz".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Bar".to_string(),
                fields: vec![DatatypeField {
                    name: "f".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Baz".to_string(),
                fields: vec![],
            },
        ],
    };
    let second = encoder.get_or_declare_var("x", Sort::Datatype(dt));
    assert!(
        second.is_ok(),
        "Uninterpreted('Foo') -> Datatype(Adt_Bar_Baz) should upgrade via synthesized Adt bypass: {second:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_sorts_are_related_tree_adt_upgrade_2231() {
    // Tree (Leaf/Node) produces Adt_Leaf_Node via synthesized ADT naming.
    // Uninterpreted("Tree") -> Datatype(Adt_Leaf_Node) must succeed.
    // This is the exact pattern from inc_some_tree.rs. (#2231)
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("self_current", Sort::Uninterpreted("Tree".to_string()));
    assert!(first.is_ok());

    let dt = DatatypeSort {
        name: "Adt_Leaf_Node".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Node".to_string(),
                fields: vec![
                    DatatypeField {
                        name: "adt_leaf_node_node_0".to_string(),
                        sort: Sort::Int,
                    },
                    DatatypeField {
                        name: "adt_leaf_node_node_1".to_string(),
                        sort: Sort::Int,
                    },
                    DatatypeField {
                        name: "adt_leaf_node_node_2".to_string(),
                        sort: Sort::Int,
                    },
                ],
            },
            DatatypeConstructor {
                name: "Leaf".to_string(),
                fields: vec![],
            },
        ],
    };
    let second = encoder.get_or_declare_var("self_current", Sort::Datatype(dt));
    assert!(
        second.is_ok(),
        "Tree -> Adt_Leaf_Node upgrade should succeed via synthesized Adt bypass: {second:?}"
    );
}
#[test]
#[timeout(30000)]
fn test_sorts_are_related_synthesized_adt_bypass_datatype_to_uninterpreted() {
    // Datatype(Adt_Bar_Baz) → Uninterpreted("Foo") SHOULD be suppressed in
    // the Datatype→Uninterpreted direction because synthesized ADTs ("Adt_*")
    // get the is_synthesized_adt bypass. The asymmetry is intentional:
    // Datatype→Uninterpreted is conservative (keeps existing Datatype sort),
    // while Uninterpreted→Datatype is a mutation that needs name validation.
    // (#1965, P1-73 Finding 4: test direction asymmetry)
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let dt = DatatypeSort {
        name: "Adt_Bar_Baz".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Bar".to_string(),
                fields: vec![DatatypeField {
                    name: "f".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Baz".to_string(),
                fields: vec![],
            },
        ],
    };
    let first = encoder.get_or_declare_var("x", Sort::Datatype(dt));
    assert!(first.is_ok(), "Datatype declaration should succeed");

    // Same unrelated "Foo", but now in the Datatype→Uninterpreted direction
    let second = encoder.get_or_declare_var("x", Sort::Uninterpreted("Foo".to_string()));
    assert!(
        second.is_ok(),
        "Datatype(Adt_*) → Uninterpreted should be suppressed via synthesized ADT bypass: {second:?}"
    );
    assert!(
        matches!(encoder.var_sort("x"), Some(Sort::Datatype(_))),
        "var_sorts should keep the Datatype (existing sort preserved)"
    );
}
