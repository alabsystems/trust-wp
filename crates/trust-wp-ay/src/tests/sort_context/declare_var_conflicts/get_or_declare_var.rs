// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;
use trust_wp_core::formula::intern_sort_name;

use super::*;

// get_or_declare_var sort conflict tests (#835, #1965)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_int_to_non_int_upgrades_sort() {
    // Int→Bool: Int is the universal fallback default, so upgrading to Bool
    // should succeed — the original Int declaration was speculative. (#1965)
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("x", Sort::Int);
    assert!(
        first.is_ok(),
        "first declaration should succeed: {:?}",
        first.as_ref().err()
    );

    let upgraded = encoder.get_or_declare_var("x", Sort::Bool);
    assert!(
        upgraded.is_ok(),
        "Int→Bool should upgrade, not error: {upgraded:?}"
    );

    // After upgrade, var_sorts should reflect the new sort
    assert_eq!(
        encoder.var_sort("x"),
        Some(&Sort::Bool),
        "var_sorts should reflect Bool after Int→Bool upgrade"
    );
}

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_non_int_conflict_returns_error() {
    // Bool→Seq: genuine conflict (neither side is Int fallback). Must error.
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("y", Sort::Bool);
    assert!(first.is_ok(), "first declaration should succeed");

    let conflict = encoder.get_or_declare_var("y", Sort::seq(Sort::Int));
    assert!(
        conflict.is_err(),
        "Bool→Seq should return sort conflict error, got {conflict:?}"
    );
    assert!(
        matches!(conflict, Err(crate::EncodingError::SortConflict { .. })),
        "Bool→Seq should return SortConflict variant, got: {conflict:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_sort_from_expr_sort_prefers_registered_datatype_over_list_seq_alias() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    let mut encoder = AYEncoder::new();
    let list_dt = DatatypeSort {
        name: "List".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "List".to_string(),
            fields: vec![DatatypeField {
                name: "list_head".to_string(),
                sort: Sort::Int,
            }],
        }],
    };
    encoder.ensure_datatype_declared(&list_dt);

    let resolved = encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("crate::List")));
    assert_eq!(
        resolved,
        Sort::Datatype(list_dt),
        "registered user ADTs should not collapse to the Seq alias just because their bare name is List"
    );
}

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_same_sort_reuses_term() {
    // Requesting the same variable with the same sort should return the same term.
    let mut encoder = AYEncoder::new();

    let first = encoder
        .get_or_declare_var("y", Sort::Int)
        .expect("declare var 'y' as Int");
    let second = encoder
        .get_or_declare_var("y", Sort::Int)
        .expect("re-declare var 'y' as Int should reuse");
    assert_eq!(
        first, second,
        "same name + same sort should return the cached term"
    );
}

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_different_names_independent() {
    // Different variable names can have different sorts without conflict.
    let mut encoder = AYEncoder::new();

    let int_var = encoder.get_or_declare_var("a", Sort::Int);
    let bool_var = encoder.get_or_declare_var("b", Sort::Bool);
    assert!(
        int_var.is_ok(),
        "Int variable 'a' should succeed: {:?}",
        int_var.as_ref().err()
    );
    assert!(
        bool_var.is_ok(),
        "Bool variable 'b' should succeed: {:?}",
        bool_var.as_ref().err()
    );
}

// =============================================================================
// Uninterpreted→Int downgrade for Int-model Datatype sorts (#1965)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_uninterpreted_to_int_downgrade() {
    // A variable declared with Sort::Uninterpreted("std::time::Duration") should
    // be re-declared as Int when a subsequent call requests Sort::Int. This models
    // the case where a code path declares the variable before the sort resolution
    // cascade identifies it as an Int-model type. (#1965)
    let mut encoder = AYEncoder::new();

    let first =
        encoder.get_or_declare_var("d", Sort::Uninterpreted("std::time::Duration".to_string()));
    assert!(
        first.is_ok(),
        "first declaration as Uninterpreted should succeed"
    );

    let second = encoder.get_or_declare_var("d", Sort::Int);
    assert!(
        second.is_ok(),
        "Uninterpreted(Duration) → Int should succeed, got: {:?}",
        second.as_ref().err()
    );
    // After downgrade, the variable should have Int sort.
    assert_eq!(
        encoder.var_sort("d"),
        Some(&Sort::Int),
        "variable sort should be Int after downgrade"
    );
}

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_seq_to_int_remains_error() {
    // Seq→Int should NOT be downgraded — Seq is a well-known encoding sort
    // that genuinely means the variable holds a sequence value.
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("s", Sort::seq(Sort::Int));
    assert!(first.is_ok());

    let conflict = encoder.get_or_declare_var("s", Sort::Int);
    assert!(
        conflict.is_err(),
        "Seq → Int should be a genuine sort conflict, got: {:?}",
        conflict.as_ref().ok()
    );
}

// =============================================================================
// Datatype sort conflict suppression for recursive ADTs (#1965)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_datatype_same_name_suppressed() {
    // Recursive ADTs (e.g., List = Cons | Nil) produce structurally different
    // DatatypeSort objects when the recursive field is resolved at different
    // stages. Both have the same ADT name, so the conflict should be suppressed.
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let dt1 = DatatypeSort {
        name: "Adt_Cons_Nil".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Cons".to_string(),
                fields: vec![
                    DatatypeField {
                        name: "cons_0".to_string(),
                        sort: Sort::Int,
                    },
                    DatatypeField {
                        name: "cons_1".to_string(),
                        sort: Sort::Int,
                    },
                ],
            },
            DatatypeConstructor {
                name: "Nil".to_string(),
                fields: vec![],
            },
        ],
    };
    let first = encoder.get_or_declare_var("self", Sort::Datatype(dt1));
    assert!(first.is_ok(), "first Datatype declaration should succeed");

    // Second declaration with different field sorts (recursive field resolved)
    let dt2 = DatatypeSort {
        name: "Adt_Cons_Nil".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Cons".to_string(),
                fields: vec![
                    DatatypeField {
                        name: "cons_0".to_string(),
                        sort: Sort::Int,
                    },
                    DatatypeField {
                        name: "cons_1".to_string(),
                        sort: Sort::Uninterpreted("Adt_Cons_Nil".to_string()),
                    },
                ],
            },
            DatatypeConstructor {
                name: "Nil".to_string(),
                fields: vec![],
            },
        ],
    };
    let second = encoder.get_or_declare_var("self", Sort::Datatype(dt2));
    assert!(
        second.is_ok(),
        "same-name Datatype re-resolution should not error: {second:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_uninterpreted_to_datatype_upgrade() {
    // A variable first declared as Sort::Uninterpreted("ResultIntInt") should
    // be upgradeable to Sort::Datatype(DatatypeSort { name: "ResultIntInt" }).
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var(
        "call_3_current",
        Sort::Uninterpreted("ResultIntInt".to_string()),
    );
    assert!(
        first.is_ok(),
        "first Uninterpreted declaration should succeed"
    );

    let dt = DatatypeSort {
        name: "ResultIntInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "ok_0".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Err".to_string(),
                fields: vec![DatatypeField {
                    name: "err_0".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    let second = encoder.get_or_declare_var("call_3_current", Sort::Datatype(dt));
    assert!(
        second.is_ok(),
        "Uninterpreted → Datatype with matching name should upgrade: {second:?}"
    );
    assert!(
        matches!(encoder.var_sort("call_3_current"), Some(Sort::Datatype(_))),
        "var_sorts should reflect Datatype after upgrade"
    );
}

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_datatype_to_uninterpreted_kept() {
    // A variable first declared as Sort::Datatype should keep Datatype when
    // a later code path requests Sort::Uninterpreted with the same name.
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let dt = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "some_0".to_string(),
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
    assert!(first.is_ok(), "Datatype declaration should succeed");

    let second = encoder.get_or_declare_var("x", Sort::Uninterpreted("OptionInt".to_string()));
    assert!(
        second.is_ok(),
        "Datatype → Uninterpreted with matching name should succeed: {second:?}"
    );
    // Sort should still be Datatype (the more precise variant).
    assert!(
        matches!(encoder.var_sort("x"), Some(Sort::Datatype(_))),
        "var_sorts should keep Datatype when Uninterpreted is requested"
    );
}

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_different_datatype_names_still_error() {
    // Two Datatype sorts with different names should still error.
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let dt1 = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "some_0".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
        ],
    };
    let first = encoder.get_or_declare_var("v", Sort::Datatype(dt1));
    assert!(first.is_ok());

    let dt2 = DatatypeSort {
        name: "ResultIntInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "ok_0".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Err".to_string(),
                fields: vec![DatatypeField {
                    name: "err_0".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    let second = encoder.get_or_declare_var("v", Sort::Datatype(dt2));
    assert!(
        second.is_err(),
        "different-name Datatypes should still error: {second:?}"
    );
}

// =============================================================================
// Cross-name Datatype/Uninterpreted sort conflict resolution (#1965)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_datatype_to_uninterpreted_cross_name_suppressed() {
    // Recursive ADTs: the match encoding creates Datatype(Adt_Cons_Nil) from
    // constructor names, but sort inference may later request
    // Uninterpreted("List") from the Rust type name. The Datatype is more
    // precise, so the conflict should be suppressed. (#1965)
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let dt = DatatypeSort {
        name: "Adt_Cons_Nil".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Cons".to_string(),
                fields: vec![
                    DatatypeField {
                        name: "adt_cons_nil_cons_0".to_string(),
                        sort: Sort::Int,
                    },
                    DatatypeField {
                        name: "adt_cons_nil_cons_1".to_string(),
                        sort: Sort::Int,
                    },
                ],
            },
            DatatypeConstructor {
                name: "Nil".to_string(),
                fields: vec![],
            },
        ],
    };
    let first = encoder.get_or_declare_var("l", Sort::Datatype(dt));
    assert!(first.is_ok(), "Datatype declaration should succeed");

    // Request Uninterpreted("MyAdt") — different name, but still a user ADT.
    // (Uses "MyAdt" rather than "List" for clarity — we want to test
    // cross-name suppression with an unrelated name.)
    let second = encoder.get_or_declare_var("l", Sort::Uninterpreted("MyAdt".to_string()));
    assert!(
        second.is_ok(),
        "Datatype → Uninterpreted with different name (MyAdt) should be suppressed: {second:?}"
    );
    assert!(
        matches!(encoder.var_sort("l"), Some(Sort::Datatype(_))),
        "var_sorts should keep Datatype when cross-name Uninterpreted is requested"
    );
}

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_uninterpreted_to_datatype_cross_name_upgrade() {
    // A variable declared as Uninterpreted("std::result::Result") should be
    // upgradeable to Datatype(ResultIntInt) even though the names differ.
    // The Datatype is the more precise representation. (#1965)
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var(
        "result_var",
        Sort::Uninterpreted("std::result::Result".to_string()),
    );
    assert!(first.is_ok(), "Uninterpreted declaration should succeed");

    let dt = DatatypeSort {
        name: "ResultIntInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "result_ok_value".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Err".to_string(),
                fields: vec![DatatypeField {
                    name: "result_err_error".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    let second = encoder.get_or_declare_var("result_var", Sort::Datatype(dt));
    assert!(
        second.is_ok(),
        "Uninterpreted → Datatype with different name should upgrade: {second:?}"
    );
    assert!(
        matches!(encoder.var_sort("result_var"), Some(Sort::Datatype(_))),
        "var_sorts should be upgraded to Datatype"
    );
}

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_datatype_to_seq_uninterpreted_still_errors() {
    // Datatype → Sort::Seq(Int) should NOT be suppressed: Seq is a
    // well-known encoding sort with its own axioms. (#1965, #2080)
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let dt = DatatypeSort {
        name: "SomeAdt".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Ctor".to_string(),
            fields: vec![DatatypeField {
                name: "f".to_string(),
                sort: Sort::Int,
            }],
        }],
    };
    let first = encoder.get_or_declare_var("x", Sort::Datatype(dt));
    assert!(first.is_ok());

    let second = encoder.get_or_declare_var("x", Sort::seq(Sort::Int));
    assert!(
        second.is_err(),
        "Datatype → Seq(Int) should still error: Seq is an encoding sort"
    );
}

// =============================================================================
// ClosureEnv Uninterpreted/Datatype equivalence suppression (#2151)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_closure_env_uninterpreted_to_datatype_suppressed() {
    // Closure sorts are declared as Datatype (#2151) but axiom code may
    // reconstruct them as Uninterpreted from sort tags. Since ay maps
    // Datatype→Uninterpreted internally, these are equivalent.
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var(
        "closure_var",
        Sort::Uninterpreted("ClosureEnv_my_fn".to_string()),
    );
    assert!(
        first.is_ok(),
        "ClosureEnv Uninterpreted declaration should succeed"
    );

    let dt = DatatypeSort {
        name: "ClosureEnv_my_fn".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "ClosureEnv_my_fn_ctor".to_string(),
            fields: vec![DatatypeField {
                name: "capture_0".to_string(),
                sort: Sort::Int,
            }],
        }],
    };
    let second = encoder.get_or_declare_var("closure_var", Sort::Datatype(dt));
    assert!(
        second.is_ok(),
        "ClosureEnv Uninterpreted → Datatype with same name should be suppressed: {second:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_closure_env_datatype_to_uninterpreted_suppressed() {
    // Reverse direction: Datatype first, then Uninterpreted.
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let dt = DatatypeSort {
        name: "ClosureEnv_other_fn".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "ClosureEnv_other_fn_ctor".to_string(),
            fields: vec![DatatypeField {
                name: "capture_0".to_string(),
                sort: Sort::Bool,
            }],
        }],
    };
    let first = encoder.get_or_declare_var("cv", Sort::Datatype(dt));
    assert!(
        first.is_ok(),
        "ClosureEnv Datatype declaration should succeed"
    );

    let second =
        encoder.get_or_declare_var("cv", Sort::Uninterpreted("ClosureEnv_other_fn".to_string()));
    assert!(
        second.is_ok(),
        "ClosureEnv Datatype → Uninterpreted with same name should be suppressed: {second:?}"
    );
}

// =============================================================================
// Uninterpreted→Uninterpreted upgrade for related monomorphized names (#761)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_uninterpreted_to_uninterpreted_upgrade_option_to_option_int() {
    // A variable declared as Uninterpreted("Option") (generic) should be
    // upgraded to the native OptionInt datatype. AY 0.4 rejects declaring a
    // reserved name as uninterpreted and later redeclaring it as a datatype,
    // so the monomorphized spelling is canonicalized at first use. (#761,
    // #2706)
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("result", Sort::Uninterpreted("Option".to_string()));
    assert!(
        first.is_ok(),
        "first Uninterpreted declaration should succeed"
    );

    let second = encoder.get_or_declare_var("result", Sort::Uninterpreted("OptionInt".to_string()));
    assert!(
        second.is_ok(),
        "Option → OptionInt should upgrade, not error: {second:?}"
    );
    assert!(
        matches!(
            encoder.var_sort("result"),
            Some(Sort::Datatype(datatype)) if datatype.name == "OptionInt"
        ),
        "var_sorts should reflect native OptionInt after upgrade"
    );
}

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_uninterpreted_to_uninterpreted_reverse_keeps_specific() {
    // If the variable is already declared with the reserved monomorphized
    // spelling, it is native from first use. Requesting the generic name
    // (Option) should preserve that more-specific datatype.
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("result", Sort::Uninterpreted("OptionInt".to_string()));
    assert!(first.is_ok(), "first declaration should succeed");

    let second = encoder.get_or_declare_var("result", Sort::Uninterpreted("Option".to_string()));
    assert!(
        second.is_ok(),
        "OptionInt → Option should suppress, not error: {second:?}"
    );
    assert!(
        matches!(
            encoder.var_sort("result"),
            Some(Sort::Datatype(datatype)) if datatype.name == "OptionInt"
        ),
        "var_sorts should keep native OptionInt (the more specific sort)"
    );
}

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_uninterpreted_to_uninterpreted_result_upgrade() {
    // Same native-canonicalization pattern for Result → ResultIntInt.
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("r", Sort::Uninterpreted("Result".to_string()));
    assert!(first.is_ok(), "first declaration should succeed");

    let second = encoder.get_or_declare_var("r", Sort::Uninterpreted("ResultIntInt".to_string()));
    assert!(
        second.is_ok(),
        "Result → ResultIntInt should upgrade: {second:?}"
    );
    assert!(
        matches!(
            encoder.var_sort("r"),
            Some(Sort::Datatype(datatype)) if datatype.name == "ResultIntInt"
        ),
        "var_sorts should reflect native ResultIntInt after upgrade"
    );
}

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_uninterpreted_to_uninterpreted_unrelated_still_errors() {
    // Unrelated Uninterpreted names should still produce a sort conflict error.
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("x", Sort::Uninterpreted("String".to_string()));
    assert!(first.is_ok(), "first declaration should succeed");

    let conflict = encoder.get_or_declare_var("x", Sort::Uninterpreted("OptionInt".to_string()));
    assert!(
        conflict.is_err(),
        "String → OptionInt should be a genuine sort conflict: {conflict:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_uninterpreted_to_uninterpreted_encoding_sort_excluded() {
    // Encoding sorts (Seq, FMap, Unit, Tuple*, ClosureEnv_*) should NOT
    // be handled by this path — they have their own dedicated handlers.
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("t", Sort::Uninterpreted("Tuple2".to_string()));
    assert!(first.is_ok(), "first declaration should succeed");

    let conflict = encoder.get_or_declare_var("t", Sort::Uninterpreted("Tuple2Int".to_string()));
    assert!(
        conflict.is_err(),
        "Tuple2 → Tuple2Int should fall through to error (encoding sort excluded): {conflict:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_phantom_variable_upgrade_counter_fires_on_uninterpreted_to_uninterpreted() {
    use crate::encoder::unsoundness::{self, UnsoundnessCategory};
    let mut encoder = AYEncoder::new();

    let before = unsoundness::snapshot();
    encoder
        .get_or_declare_var("result", Sort::Uninterpreted("Option".to_string()))
        .expect("declare as Option");
    encoder
        .get_or_declare_var("result", Sort::Uninterpreted("OptionInt".to_string()))
        .expect("upgrade to OptionInt");
    let after = unsoundness::snapshot();

    let d = unsoundness::delta(&before, &after);
    assert!(
        d.get(&UnsoundnessCategory::PhantomVariableUpgrade)
            .copied()
            .unwrap_or(0)
            > 0,
        "Uninterpreted→Uninterpreted upgrade should increment PhantomVariableUpgrade, delta={d:?}"
    );
}

// =============================================================================
// Encoding-sort → well-known-Datatype upgrade (#2155)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_seq_to_option_datatype_upgrade() {
    // Postcondition prescan may misattribute Seq evidence to `result` while
    // the actual return type is Option<i64>. The Datatype sort is definitively
    // more specific and should replace the encoding sort. (#2155)
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("result", Sort::seq(Sort::Int));
    assert!(
        first.is_ok(),
        "Seq Uninterpreted declaration should succeed"
    );

    let dt = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "some_0".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
        ],
    };
    let second = encoder.get_or_declare_var("result", Sort::Datatype(dt));
    assert!(
        second.is_ok(),
        "Seq → OptionInt Datatype should upgrade (#2155): {second:?}"
    );
    assert!(
        matches!(encoder.var_sort("result"), Some(Sort::Datatype(_))),
        "var_sorts should reflect Datatype after encoding-sort → well-known-DT upgrade"
    );
}

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_fmap_to_result_datatype_upgrade() {
    // Same pattern but FMap → ResultIntInt.
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("r", Sort::Uninterpreted("FMap".to_string()));
    assert!(
        first.is_ok(),
        "FMap Uninterpreted declaration should succeed"
    );

    let dt = DatatypeSort {
        name: "ResultIntInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "ok_0".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Err".to_string(),
                fields: vec![DatatypeField {
                    name: "err_0".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    let second = encoder.get_or_declare_var("r", Sort::Datatype(dt));
    assert!(
        second.is_ok(),
        "FMap → ResultIntInt Datatype should upgrade (#2155): {second:?}"
    );
    assert!(
        matches!(encoder.var_sort("r"), Some(Sort::Datatype(_))),
        "var_sorts should reflect Datatype after FMap → well-known-DT upgrade"
    );
}

// =============================================================================
// Datatype(collection_model) downgrade guard tightening (#2557)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_get_or_declare_var_collection_datatype_then_bool_remains_conflict() {
    // Datatype(Vec) → Bool should NOT silently downgrade to Seq.
    // The downgrade guard must only fire for canonical target sorts or Int.
    // (#2557)
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let dt = DatatypeSort {
        name: "Vec".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Vec_ctor".to_string(),
            fields: vec![DatatypeField {
                name: "buf".to_string(),
                sort: Sort::Int,
            }],
        }],
    };
    let first = encoder.get_or_declare_var("v", Sort::Datatype(dt));
    assert!(first.is_ok(), "Datatype(Vec) declaration should succeed");

    let conflict = encoder.get_or_declare_var("v", Sort::Bool);
    assert!(
        conflict.is_err(),
        "Datatype(Vec) → Bool should be a genuine sort conflict, not silently downgraded: {conflict:?}"
    );
}

// =============================================================================
// PhantomVariableUpgrade counter verification (#2567)
// =============================================================================

#[test]
#[timeout(30000)]
fn test_phantom_variable_upgrade_counter_fires_on_int_to_non_int() {
    use crate::encoder::unsoundness::{self, UnsoundnessCategory};
    let mut encoder = AYEncoder::new();

    let before = unsoundness::snapshot();
    encoder
        .get_or_declare_var("x", Sort::Int)
        .expect("declare as Int");
    encoder
        .get_or_declare_var("x", Sort::Bool)
        .expect("upgrade Int→Bool");
    let after = unsoundness::snapshot();

    let d = unsoundness::delta(&before, &after);
    assert!(
        d.get(&UnsoundnessCategory::PhantomVariableUpgrade)
            .copied()
            .unwrap_or(0)
            > 0,
        "Int→Bool upgrade should increment PhantomVariableUpgrade, delta={d:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_phantom_variable_upgrade_counter_fires_on_uninterpreted_to_int_downgrade() {
    use crate::encoder::unsoundness::{self, UnsoundnessCategory};
    let mut encoder = AYEncoder::new();

    // Use a type name that normalize_sort doesn't canonicalize to Int.
    // "std::time::Duration" becomes Int via canonical_sort, so no conflict.
    let before = unsoundness::snapshot();
    encoder
        .get_or_declare_var("d", Sort::Uninterpreted("MyDuration".to_string()))
        .expect("declare as Uninterpreted");
    encoder
        .get_or_declare_var("d", Sort::Int)
        .expect("downgrade to Int");
    let after = unsoundness::snapshot();

    let d = unsoundness::delta(&before, &after);
    assert!(
        d.get(&UnsoundnessCategory::PhantomVariableUpgrade)
            .copied()
            .unwrap_or(0)
            > 0,
        "Uninterpreted→Int downgrade should increment PhantomVariableUpgrade, delta={d:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_phantom_variable_upgrade_counter_fires_on_uninterpreted_to_datatype() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    use crate::encoder::unsoundness::{self, UnsoundnessCategory};
    let mut encoder = AYEncoder::new();

    let before = unsoundness::snapshot();
    encoder
        .get_or_declare_var("r", Sort::Uninterpreted("std::result::Result".to_string()))
        .expect("declare as Uninterpreted");
    let dt = DatatypeSort {
        name: "ResultIntInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "ok_0".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Err".to_string(),
                fields: vec![DatatypeField {
                    name: "err_0".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder
        .get_or_declare_var("r", Sort::Datatype(dt))
        .expect("upgrade to Datatype");
    let after = unsoundness::snapshot();

    let d = unsoundness::delta(&before, &after);
    assert!(
        d.get(&UnsoundnessCategory::PhantomVariableUpgrade)
            .copied()
            .unwrap_or(0)
            > 0,
        "Uninterpreted→Datatype upgrade should increment PhantomVariableUpgrade, delta={d:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_phantom_variable_upgrade_counter_fires_on_encoding_to_well_known_dt() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    use crate::encoder::unsoundness::{self, UnsoundnessCategory};
    let mut encoder = AYEncoder::new();

    let before = unsoundness::snapshot();
    encoder
        .get_or_declare_var("result", Sort::seq(Sort::Int))
        .expect("declare as Seq");
    let dt = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "some_0".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
        ],
    };
    encoder
        .get_or_declare_var("result", Sort::Datatype(dt))
        .expect("upgrade Seq→OptionInt");
    let after = unsoundness::snapshot();

    let d = unsoundness::delta(&before, &after);
    assert!(
        d.get(&UnsoundnessCategory::PhantomVariableUpgrade)
            .copied()
            .unwrap_or(0)
            > 0,
        "encoding-sort→well-known-Datatype should increment PhantomVariableUpgrade, delta={d:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_phantom_variable_upgrade_counter_fires_on_collection_to_canonical() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    use crate::encoder::unsoundness::{self, UnsoundnessCategory};
    let mut encoder = AYEncoder::new();

    // Datatype(Vec) → Seq(Int) canonical downgrade creates a phantom.
    let dt = DatatypeSort {
        name: "Vec".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Vec_ctor".to_string(),
            fields: vec![DatatypeField {
                name: "buf".to_string(),
                sort: Sort::Int,
            }],
        }],
    };
    encoder
        .get_or_declare_var("v", Sort::Datatype(dt))
        .expect("declare as Datatype(Vec)");

    let before = unsoundness::snapshot();
    encoder
        .get_or_declare_var("v", Sort::seq(Sort::Int))
        .expect("downgrade to Seq");
    let after = unsoundness::snapshot();

    let d = unsoundness::delta(&before, &after);
    assert!(
        d.get(&UnsoundnessCategory::PhantomVariableUpgrade)
            .copied()
            .unwrap_or(0)
            > 0,
        "Datatype(Vec)→Seq canonical downgrade should increment PhantomVariableUpgrade, delta={d:?}"
    );
}

#[test]
#[timeout(30000)]
fn test_phantom_variable_upgrade_counter_does_not_fire_on_suppression() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    use crate::encoder::unsoundness::{self, UnsoundnessCategory};
    let mut encoder = AYEncoder::new();

    // Datatype→Datatype same name = suppression, no phantom variable
    let dt1 = DatatypeSort {
        name: "MyAdt".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Ctor".to_string(),
            fields: vec![DatatypeField {
                name: "f".to_string(),
                sort: Sort::Int,
            }],
        }],
    };
    encoder
        .get_or_declare_var("v", Sort::Datatype(dt1))
        .expect("declare as Datatype");

    let before = unsoundness::snapshot();
    let dt2 = DatatypeSort {
        name: "MyAdt".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Ctor".to_string(),
            fields: vec![DatatypeField {
                name: "f".to_string(),
                sort: Sort::Bool,
            }],
        }],
    };
    encoder
        .get_or_declare_var("v", Sort::Datatype(dt2))
        .expect("same-name Datatype suppression");
    let after = unsoundness::snapshot();

    let d = unsoundness::delta(&before, &after);
    assert_eq!(
        d.get(&UnsoundnessCategory::PhantomVariableUpgrade)
            .copied()
            .unwrap_or(0),
        0,
        "suppression paths should NOT increment PhantomVariableUpgrade, delta={d:?}"
    );
}

// =============================================================================
// Cross-family encoding sort conflict suppression (#2699)
// =============================================================================

/// FMap→Seq cross-family encoding sort conflict should be suppressed.
///
/// When a variable is declared as Uninterpreted("FMap") (from prescan) but later
/// requested as Seq(Int) (from a different code path), the cross-family encoding
/// sort check should suppress the conflict since both are encoding-level
/// approximations. (#2699)
#[test]
#[timeout(30000)]
fn test_fmap_to_seq_cross_family_suppressed() {
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("call_6", Sort::Uninterpreted("FMap".to_string()));
    assert!(first.is_ok(), "FMap declaration should succeed");

    let second = encoder.get_or_declare_var("call_6", Sort::seq(Sort::Int));
    assert!(
        second.is_ok(),
        "FMap → Seq(Int) should be suppressed as cross-family encoding sort conflict, \
         got: {second:?}"
    );
}

/// Seq→FMap cross-family encoding sort conflict should also be suppressed.
#[test]
#[timeout(30000)]
fn test_seq_to_fmap_cross_family_suppressed() {
    let mut encoder = AYEncoder::new();

    let first = encoder.get_or_declare_var("x", Sort::seq(Sort::Int));
    assert!(first.is_ok(), "Seq declaration should succeed");

    let second = encoder.get_or_declare_var("x", Sort::Uninterpreted("FMap".to_string()));
    assert!(
        second.is_ok(),
        "Seq(Int) → FMap should be suppressed as cross-family encoding sort conflict, \
         got: {second:?}"
    );
}

// =============================================================================
// TupleN ↔ Datatype sort conflict suppression (#2699)
// =============================================================================

/// Datatype(Point{x:Int, y:Int}) → Uninterpreted("Tuple2") should be suppressed.
///
/// The driver emits TupleN as a positional placeholder for named structs.
/// When the Datatype is already declared with named fields and the same
/// field count, the Tuple request should be suppressed. (#2699)
#[test]
#[timeout(30000)]
fn test_datatype_to_tuple2_arity_match_suppressed() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let dt = DatatypeSort {
        name: "Point".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Point".to_string(),
            fields: vec![
                DatatypeField {
                    name: "point_x".to_string(),
                    sort: Sort::Int,
                },
                DatatypeField {
                    name: "point_y".to_string(),
                    sort: Sort::Int,
                },
            ],
        }],
    };
    encoder
        .get_or_declare_var("result", Sort::Datatype(dt))
        .expect("declare as Datatype(Point)");

    let second = encoder.get_or_declare_var("result", Sort::Uninterpreted("Tuple2".to_string()));
    assert!(
        second.is_ok(),
        "Datatype(Point) → Tuple2 should be suppressed (arity match): {second:?}"
    );
}

/// Uninterpreted("Tuple2") → Datatype(Board{size:Int, field:Seq(Int)}) should upgrade.
///
/// When the variable was speculatively declared as TupleN but the match encoding
/// later produces a proper Datatype with N fields, upgrade to the Datatype. (#2699)
#[test]
#[timeout(30000)]
fn test_tuple2_to_datatype_arity_match_upgrades() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    use crate::encoder::unsoundness::{self, UnsoundnessCategory};
    let mut encoder = AYEncoder::new();

    encoder
        .get_or_declare_var("result", Sort::Uninterpreted("Tuple2".to_string()))
        .expect("declare as Tuple2");

    let before = unsoundness::snapshot();
    let dt = DatatypeSort {
        name: "Board".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Board".to_string(),
            fields: vec![
                DatatypeField {
                    name: "board_size".to_string(),
                    sort: Sort::Int,
                },
                DatatypeField {
                    name: "board_field".to_string(),
                    sort: Sort::seq(Sort::Int),
                },
            ],
        }],
    };
    let second = encoder.get_or_declare_var("result", Sort::Datatype(dt));
    assert!(
        second.is_ok(),
        "Tuple2 → Datatype(Board) should upgrade: {second:?}"
    );
    let after = unsoundness::snapshot();
    let d = unsoundness::delta(&before, &after);
    assert!(
        d.get(&UnsoundnessCategory::PhantomVariableUpgrade)
            .copied()
            .unwrap_or(0)
            > 0,
        "TupleN → Datatype upgrade should increment PhantomVariableUpgrade, delta={d:?}"
    );
}

/// Datatype(Point{x:Int, y:Int, z:Int}) → Tuple2 should NOT be suppressed
/// (arity mismatch: 3 fields vs Tuple2).
#[test]
#[timeout(30000)]
fn test_datatype_3field_to_tuple2_arity_mismatch_not_suppressed() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let dt = DatatypeSort {
        name: "Point3D".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Point3D".to_string(),
            fields: vec![
                DatatypeField {
                    name: "x".to_string(),
                    sort: Sort::Int,
                },
                DatatypeField {
                    name: "y".to_string(),
                    sort: Sort::Int,
                },
                DatatypeField {
                    name: "z".to_string(),
                    sort: Sort::Int,
                },
            ],
        }],
    };
    encoder
        .get_or_declare_var("p", Sort::Datatype(dt))
        .expect("declare as Datatype(Point3D)");

    let second = encoder.get_or_declare_var("p", Sort::Uninterpreted("Tuple2".to_string()));
    assert!(
        second.is_err(),
        "Datatype(Point3D) with 3 fields → Tuple2 should be a sort conflict (arity mismatch)"
    );
}

// =============================================================================
// Well-known Datatype ↔ encoding sort suppression (#2699)
// =============================================================================

/// Datatype(OptionInt) → Seq(Int) should be suppressed.
///
/// When result type inference declares the variable as OptionInt (from
/// Iterator::next() returning Option<T>) but body encoding later tries
/// to redeclare as Seq(Int) (from collection operations on the result),
/// keep the existing Datatype since it is more precise. (#2699)
#[test]
#[timeout(30000)]
fn test_option_datatype_to_seq_keeps_datatype() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let dt = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "option_some_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder
        .get_or_declare_var("result", Sort::Datatype(dt))
        .expect("declare as Datatype(OptionInt)");

    let second = encoder.get_or_declare_var("result", Sort::seq(Sort::Int));
    assert!(
        second.is_ok(),
        "Datatype(OptionInt) → Seq(Int) should be suppressed: {second:?}"
    );
}

/// Datatype(ResultIntInt) → FMap should be suppressed.
#[test]
#[timeout(30000)]
fn test_result_datatype_to_fmap_keeps_datatype() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};
    let mut encoder = AYEncoder::new();

    let dt = DatatypeSort {
        name: "ResultIntInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "result_ok_value".to_string(),
                    sort: Sort::Int,
                }],
            },
            DatatypeConstructor {
                name: "Err".to_string(),
                fields: vec![DatatypeField {
                    name: "result_err_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder
        .get_or_declare_var("result", Sort::Datatype(dt))
        .expect("declare as Datatype(ResultIntInt)");

    let second = encoder.get_or_declare_var("result", Sort::Uninterpreted("FMap".to_string()));
    assert!(
        second.is_ok(),
        "Datatype(ResultIntInt) → FMap should be suppressed: {second:?}"
    );
}

/// Seq(Int) → Datatype(OptionInt) should upgrade to the Datatype.
#[test]
#[timeout(30000)]
fn test_seq_to_option_datatype_upgrades() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort};

    use crate::encoder::unsoundness::{self, UnsoundnessCategory};
    let mut encoder = AYEncoder::new();

    encoder
        .get_or_declare_var("result", Sort::seq(Sort::Int))
        .expect("declare as Seq(Int)");

    let before = unsoundness::snapshot();
    let dt = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "option_some_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    let second = encoder.get_or_declare_var("result", Sort::Datatype(dt));
    assert!(
        second.is_ok(),
        "Seq(Int) → Datatype(OptionInt) should upgrade: {second:?}"
    );
    let after = unsoundness::snapshot();
    let d = unsoundness::delta(&before, &after);
    assert!(
        d.get(&UnsoundnessCategory::PhantomVariableUpgrade)
            .copied()
            .unwrap_or(0)
            > 0,
        "encoding sort → well-known Datatype upgrade should increment PhantomVariableUpgrade"
    );
}
