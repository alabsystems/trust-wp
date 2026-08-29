// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::*;

/// FMap insert + lookup identity: after insert(k, v), lookup(k) == v.
///
/// Models the core FMap spec from ghost_map.rs:
///   map.insert_ghost(1, 21);
///   proof_assert!(map.lookup(1i32) == 21i32);
///
/// At ay level with uninterpreted functions:
///   insert postcondition gives map1_lookup_k == v,
///   so lookup(k) == v holds.
///
/// Part of #1075
#[test]
#[timeout(30000)]
fn test_verify_fmap_insert_lookup_identity() {
    // Key and value
    let key_assumption = eq(var("k"), int(1));
    let val_assumption = eq(var("v"), int(21));

    // insert_ghost postcondition (simplified):
    //   result_contains_k == true (i.e., the map contains k)
    //   result_lookup_k == v (i.e., lookup(k) == v)
    let insert_contains = eq(var("map1_contains_k"), bool_expr(true));
    let insert_lookup = eq(var("map1_lookup_k"), var("v"));

    // ensures: map1_lookup_k == 21
    let ens = eq(var("map1_lookup_k"), int(21));

    let body = var("map1_lookup_k");

    let result = verify_function_with_modes(
        VerificationRequest::new(
            &[
                key_assumption,
                val_assumption,
                insert_contains,
                insert_lookup,
            ],
            &[ens],
        )
        .return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "FMap insert+lookup identity should verify: {result:?}"
    );
}

/// FMap empty has no elements: forall k, !empty.contains(k).
///
/// Models the FMap::EMPTY spec:
///   ensures: result.len() == 0
///   ensures: forall<k: _> !result.contains(k)
///
/// At ay level: empty_len == 0 and empty_contains_any == false.
///
/// Part of #1075
#[test]
#[timeout(30000)]
fn test_verify_fmap_empty_no_elements() {
    // empty spec: len == 0
    let empty_len = eq(var("empty_len"), int(0));

    // empty spec: for a specific key, contains == false
    let empty_contains = eq(var("empty_contains_k"), bool_expr(false));

    // ensures: empty_len == 0
    let ens_len = eq(var("empty_len"), int(0));
    // ensures: empty_contains_k is false
    let ens_contains = eq(var("empty_contains_k"), bool_expr(false));

    let body = var("empty_len");

    let result = verify_function_with_modes(
        VerificationRequest::new(&[empty_len, empty_contains], &[ens_len, ens_contains])
            .return_expr(Some(&body)),
    );
    assert!(
        matches!(result, Ok(VerificationResult::Verified(_))),
        "FMap empty should verify: {result:?}"
    );
}
