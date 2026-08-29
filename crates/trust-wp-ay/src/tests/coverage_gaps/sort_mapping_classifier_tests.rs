// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for Datatype(collection_model)→canonical sort downgrade (#2554).
//!
//! When the driver's struct layout extraction creates native DatatypeSort for
//! types like Vec or HashMap, the variable declaration system must accept
//! subsequent requests for the canonical encoding sort (Seq, FMap) without
//! erroring. These tests verify the downgrade arm in `get_or_declare_var`.

use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

use crate::encoder::{sort_context::is_seq_family_sort, AYEncoder};

fn vec_datatype() -> DatatypeSort {
    DatatypeSort::new(
        "Vec",
        vec![DatatypeConstructor::new(
            "Vec",
            vec![
                DatatypeField::new("vec_buf", Sort::Int),
                DatatypeField::new("vec_len", Sort::Int),
            ],
        )],
    )
}

fn hashmap_datatype() -> DatatypeSort {
    DatatypeSort::new(
        "HashMap",
        vec![DatatypeConstructor::new(
            "HashMap",
            vec![DatatypeField::new("hashmap_inner", Sort::Int)],
        )],
    )
}

/// Datatype(Vec) declared first, then Seq requested → downgrade to Seq.
#[test]
fn test_vec_datatype_downgrades_to_seq_on_seq_request() {
    let mut encoder = AYEncoder::new();
    let dt = vec_datatype();
    encoder.ensure_datatype_declared(&dt);

    // First declaration as Datatype(Vec)
    let _t1 = encoder
        .get_or_declare_var("v", Sort::Datatype(dt))
        .expect("should declare v as Datatype(Vec)");

    // Second request as Seq — should downgrade, not error
    let t2 = encoder
        .get_or_declare_var("v", Sort::seq(Sort::Int))
        .expect("should downgrade Datatype(Vec) → Seq without error");

    // Verify the variable now has Seq sort
    let var_sort = encoder.var_sort("v").expect("v should have a sort");
    assert!(
        is_seq_family_sort(var_sort),
        "v should be Seq-sorted after downgrade, got {var_sort:?}"
    );

    // Verify the returned term is usable
    let _ = t2;
}

/// Datatype(Vec) declared first, then Int requested → downgrade to Seq
/// (Vec is a Seq-model type; the canonical sort is Seq, not Int).
#[test]
fn test_vec_datatype_downgrades_to_seq_on_int_request() {
    let mut encoder = AYEncoder::new();
    let dt = vec_datatype();
    encoder.ensure_datatype_declared(&dt);

    let _t1 = encoder
        .get_or_declare_var("v", Sort::Datatype(dt))
        .expect("should declare v as Datatype(Vec)");

    // Int request triggers the downgrade because declared sort is
    // Datatype(Vec) and canonical_sort("Vec") = Seq.
    let _t2 = encoder
        .get_or_declare_var("v", Sort::Int)
        .expect("should downgrade Datatype(Vec) on Int request");

    let var_sort = encoder.var_sort("v").expect("v should have a sort");
    assert!(
        is_seq_family_sort(var_sort),
        "v should be Seq-sorted (canonical for Vec), got {var_sort:?}"
    );
}

/// Datatype(HashMap) declared first, then FMap requested → downgrade to FMap.
#[test]
fn test_hashmap_datatype_downgrades_to_fmap_on_fmap_request() {
    let mut encoder = AYEncoder::new();
    let dt = hashmap_datatype();
    encoder.ensure_datatype_declared(&dt);

    let _t1 = encoder
        .get_or_declare_var("m", Sort::Datatype(dt))
        .expect("should declare m as Datatype(HashMap)");

    let _t2 = encoder
        .get_or_declare_var("m", Sort::Uninterpreted("FMap".to_string()))
        .expect("should downgrade Datatype(HashMap) → FMap without error");

    let var_sort = encoder.var_sort("m").expect("m should have a sort");
    assert_eq!(
        *var_sort,
        Sort::Uninterpreted("FMap".to_string()),
        "m should be FMap-sorted after downgrade"
    );
}

/// OptionInt Datatype should NOT be downgraded — it's a well-known ADT.
#[test]
fn test_option_datatype_not_downgraded() {
    let mut encoder = AYEncoder::new();
    let dt = DatatypeSort::new(
        "OptionInt",
        vec![
            DatatypeConstructor::new("None", vec![]),
            DatatypeConstructor::new(
                "Some",
                vec![DatatypeField::new("option_some_value", Sort::Int)],
            ),
        ],
    );
    encoder.ensure_datatype_declared(&dt);

    let _t1 = encoder
        .get_or_declare_var("opt", Sort::Datatype(dt))
        .expect("should declare opt as Datatype(OptionInt)");

    // Int request should NOT downgrade OptionInt — it's a genuine ADT
    let result = encoder.get_or_declare_var("opt", Sort::Int);
    // This should either error (sort conflict) or succeed via Int→OptionInt upgrade
    // The important thing is that OptionInt is NOT downgraded to Int
    if result.is_ok() {
        let var_sort = encoder.var_sort("opt").expect("opt should have a sort");
        assert!(
            matches!(var_sort, Sort::Datatype(ref dt) if dt.name == "OptionInt"),
            "opt should remain OptionInt, got {var_sort:?}"
        );
    }
    // Error is also acceptable — the conflict is genuine
}

/// User-defined ADT (Adt_Cons_Nil) should NOT be downgraded.
#[test]
fn test_user_adt_not_downgraded() {
    let mut encoder = AYEncoder::new();
    let dt = DatatypeSort::new(
        "Adt_Cons_Nil",
        vec![
            DatatypeConstructor::new(
                "Cons",
                vec![
                    DatatypeField::new("cons_head", Sort::Int),
                    DatatypeField::new("cons_tail", Sort::Int),
                ],
            ),
            DatatypeConstructor::new("Nil", vec![]),
        ],
    );
    encoder.ensure_datatype_declared(&dt);

    let _t1 = encoder
        .get_or_declare_var("list", Sort::Datatype(dt))
        .expect("should declare list as Datatype(Adt_Cons_Nil)");

    // Int request should NOT downgrade a user-defined ADT
    let result = encoder.get_or_declare_var("list", Sort::Int);
    // Error is expected — genuine conflict between user ADT and Int
    if result.is_ok() {
        let var_sort = encoder.var_sort("list").expect("list should have a sort");
        assert!(
            matches!(var_sort, Sort::Datatype(ref dt) if dt.name == "Adt_Cons_Nil"),
            "list should remain Adt_Cons_Nil, got {var_sort:?}"
        );
    }
}
