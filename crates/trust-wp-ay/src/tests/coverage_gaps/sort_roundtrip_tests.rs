// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Roundtrip property tests for `ay_sort_to_expr_sort` ↔ `sort_from_expr_sort`.
//!
//! The roundtrip `ay_sort_to_expr_sort(sort_from_expr_sort(e))` holds for most
//! ExprSort variants but is intentionally lossy for:
//! - `ExprSort::Int` → `Sort::Int` → `None` (Int is the default, represented as None)
//! - `ExprSort::Ref(inner)` → peels Ref, loses wrapper
//! - `ExprSort::MutRef(inner)` now preserves its wrapper via a dedicated carrier
//! - `ExprSort::Datatype("..Snapshot")` → `Sort::Int` → `None` (#2075)
//!
//! Requested in W4 commit 04543f3 handoff.

use ay_dpll::api::Sort;
use ntest::timeout;
use trust_wp_core::formula::{intern_sort_name, ExprSort};

use crate::{encoder::sort_context::ay_sort_to_expr_sort, AYEncoder};

// ── Roundtrip-preserving variants ──────────────────────────────────────

/// Bool roundtrips: ExprSort::Bool → Sort::Bool → Some(ExprSort::Bool).
#[test]
#[timeout(30000)]
fn roundtrip_bool_preserves() {
    let mut encoder = AYEncoder::new();
    let ay_sort = encoder.sort_from_expr_sort(ExprSort::Bool);
    assert_eq!(ay_sort, Sort::Bool);
    let back = ay_sort_to_expr_sort(&ay_sort);
    assert_eq!(back, Some(ExprSort::Bool), "Bool roundtrip should preserve");
}

/// Seq roundtrips: ExprSort::Seq → Sort::Seq(Int) → Some(ExprSort::Seq). (#2080)
#[test]
#[timeout(30000)]
fn roundtrip_seq_preserves() {
    let mut encoder = AYEncoder::new();
    let ay_sort = encoder.sort_from_expr_sort(ExprSort::Seq);
    let back = ay_sort_to_expr_sort(&ay_sort);
    assert_eq!(back, Some(ExprSort::Seq), "Seq roundtrip should preserve");
}

/// FMap roundtrips: ExprSort::FMap → Sort::Uninterpreted("FMap") → Some(ExprSort::FMap).
#[test]
#[timeout(30000)]
fn roundtrip_fmap_preserves() {
    let mut encoder = AYEncoder::new();
    let ay_sort = encoder.sort_from_expr_sort(ExprSort::FMap);
    let back = ay_sort_to_expr_sort(&ay_sort);
    assert_eq!(back, Some(ExprSort::FMap), "FMap roundtrip should preserve");
}

/// Unit roundtrips: ExprSort::Unit → Sort::Uninterpreted("Unit") → Some(ExprSort::Unit).
#[test]
#[timeout(30000)]
fn roundtrip_unit_preserves() {
    let mut encoder = AYEncoder::new();
    let ay_sort = encoder.sort_from_expr_sort(ExprSort::Unit);
    let back = ay_sort_to_expr_sort(&ay_sort);
    assert_eq!(back, Some(ExprSort::Unit), "Unit roundtrip should preserve");
}

/// Tuple(3) roundtrips: ExprSort::Tuple(3) → Sort::Uninterpreted("Tuple3") → Some(ExprSort::Tuple(3)).
#[test]
#[timeout(30000)]
fn roundtrip_tuple_preserves() {
    let mut encoder = AYEncoder::new();
    let ay_sort = encoder.sort_from_expr_sort(ExprSort::Tuple(3));
    assert_eq!(ay_sort, Sort::Uninterpreted("Tuple3".to_string()));
    let back = ay_sort_to_expr_sort(&ay_sort);
    assert_eq!(
        back,
        Some(ExprSort::Tuple(3)),
        "Tuple(3) roundtrip should preserve"
    );
}

/// Non-Snapshot Datatype roundtrips via Uninterpreted path (no declared DatatypeSort).
/// ExprSort::Datatype("MyAdt") → Sort::Uninterpreted("MyAdt") → Some(ExprSort::Datatype(intern("MyAdt"))).
#[test]
#[timeout(30000)]
fn roundtrip_datatype_uninterpreted_preserves() {
    let mut encoder = AYEncoder::new();
    let id = intern_sort_name("MyAdt");
    let ay_sort = encoder.sort_from_expr_sort(ExprSort::Datatype(id));
    assert_eq!(ay_sort, Sort::Uninterpreted("MyAdt".to_string()));
    let back = ay_sort_to_expr_sort(&ay_sort);
    assert_eq!(
        back,
        Some(ExprSort::Datatype(intern_sort_name("MyAdt"))),
        "Non-Snapshot Datatype roundtrip should preserve (Uninterpreted path)"
    );
}

/// MutRef(Bool) roundtrips through the dedicated mut-ref carrier. (#2141)
#[test]
#[timeout(30000)]
fn roundtrip_mutref_bool_preserves() {
    let mut encoder = AYEncoder::new();
    let ay_sort = encoder.sort_from_expr_sort(ExprSort::MutRef(Box::new(ExprSort::Bool)));
    let back = ay_sort_to_expr_sort(&ay_sort);
    assert_eq!(
        back,
        Some(ExprSort::MutRef(Box::new(ExprSort::Bool))),
        "MutRef(Bool) roundtrip should preserve the mutable-reference wrapper"
    );
}

/// MutRef(Datatype(MyAdt)) roundtrips through the dedicated mut-ref carrier. (#2141)
#[test]
#[timeout(30000)]
fn roundtrip_mutref_datatype_preserves() {
    let mut encoder = AYEncoder::new();
    let id = intern_sort_name("MyAdt");
    let ay_sort = encoder.sort_from_expr_sort(ExprSort::MutRef(Box::new(ExprSort::Datatype(id))));
    let back = ay_sort_to_expr_sort(&ay_sort);
    assert_eq!(
        back,
        Some(ExprSort::MutRef(Box::new(ExprSort::Datatype(
            intern_sort_name("MyAdt")
        )))),
        "MutRef(Datatype(MyAdt)) roundtrip should preserve the mutable-reference wrapper"
    );
}

// ── Intentionally lossy variants ───────────────────────────────────────

/// Int does not roundtrip: ExprSort::Int → Sort::Int → None.
///
/// `None` is the semantic equivalent of Int in the `ay_sort_to_expr_sort` API.
/// This is by design: `Sort::Int` is the default representation and returning
/// `None` maintains backward compatibility.
#[test]
#[timeout(30000)]
fn roundtrip_int_returns_none() {
    let mut encoder = AYEncoder::new();
    let ay_sort = encoder.sort_from_expr_sort(ExprSort::Int);
    assert_eq!(ay_sort, Sort::Int);
    let back = ay_sort_to_expr_sort(&ay_sort);
    assert_eq!(
        back, None,
        "Int roundtrip returns None (Int is the default, represented as absence of annotation)"
    );
}

/// Ref(Bool) loses the Ref wrapper: ExprSort::Ref(Bool) → Sort::Bool → Some(ExprSort::Bool).
///
/// `expr_sort_to_ay_sort` recursively peels Ref wrapping because ay sorts
/// have no reference concept — references are modeled via separation logic,
/// not the sort system.
#[test]
#[timeout(30000)]
fn roundtrip_ref_loses_wrapper() {
    let mut encoder = AYEncoder::new();
    let ay_sort = encoder.sort_from_expr_sort(ExprSort::Ref(Box::new(ExprSort::Bool)));
    assert_eq!(ay_sort, Sort::Bool, "Ref(Bool) should map to Sort::Bool");
    let back = ay_sort_to_expr_sort(&ay_sort);
    assert_eq!(
        back,
        Some(ExprSort::Bool),
        "Ref(Bool) roundtrip loses Ref, returns Some(Bool)"
    );
}

/// Ref(Int) loses both Ref and Int: ExprSort::Ref(Int) → Sort::Int → None.
#[test]
#[timeout(30000)]
fn roundtrip_ref_int_loses_both() {
    let mut encoder = AYEncoder::new();
    let ay_sort = encoder.sort_from_expr_sort(ExprSort::Ref(Box::new(ExprSort::Int)));
    assert_eq!(ay_sort, Sort::Int, "Ref(Int) should map to Sort::Int");
    let back = ay_sort_to_expr_sort(&ay_sort);
    assert_eq!(
        back, None,
        "Ref(Int) roundtrip loses both Ref wrapper and Int → None"
    );
}

/// Snapshot Datatype maps to Int then to None (#2075).
/// ExprSort::Datatype("creusot_std::Snapshot") → Sort::Int → None.
#[test]
#[timeout(30000)]
fn roundtrip_snapshot_maps_to_int_then_none() {
    let mut encoder = AYEncoder::new();
    let id = intern_sort_name("creusot_std::Snapshot");
    let ay_sort = encoder.sort_from_expr_sort(ExprSort::Datatype(id));
    assert_eq!(
        ay_sort,
        Sort::Int,
        "Snapshot Datatype should map to Sort::Int (#2075)"
    );
    let back = ay_sort_to_expr_sort(&ay_sort);
    assert_eq!(
        back, None,
        "Snapshot → Int → None (lossy: Snapshot information is lost)"
    );
}

// ── Reverse direction: ay Sort → ExprSort → ay Sort ───────────────────

/// A non-reserved native datatype roundtrips through ExprSort::Datatype then
/// back to Sort::Uninterpreted. TrustWP only has enough information to
/// reconstruct a native datatype for its standard reserved families.
#[test]
#[timeout(30000)]
fn reverse_roundtrip_native_datatype_downgrades() {
    use ay_dpll::api::{DatatypeConstructor, DatatypeSort};

    let dt = DatatypeSort::new(
        "UserEnum",
        vec![
            DatatypeConstructor::unit("Empty_UserEnum"),
            DatatypeConstructor::new(
                "Value_UserEnum",
                vec![ay_dpll::api::DatatypeField::new("val", Sort::Int)],
            ),
        ],
    );
    let native_sort = Sort::Datatype(dt);

    // Forward: Sort::Datatype → Some(ExprSort::Datatype(intern("UserEnum")))
    let expr_sort = ay_sort_to_expr_sort(&native_sort);
    let expected_es = ExprSort::Datatype(intern_sort_name("UserEnum"));
    assert_eq!(expr_sort, Some(expected_es.clone()));

    // Reverse (without a declared datatype): custom names remain uninterpreted.
    let mut encoder = AYEncoder::new();
    let back = encoder.sort_from_expr_sort(expected_es);
    assert_eq!(
        back,
        Sort::Uninterpreted("UserEnum".to_string()),
        "custom datatype round-trip should preserve the uninterpreted family"
    );
}

/// Reserved standard datatype names carry enough schema information to
/// reconstruct the native AY datatype even before an explicit declaration.
#[test]
#[timeout(30000)]
fn reverse_roundtrip_reserved_option_uses_native_datatype() {
    let mut encoder = AYEncoder::new();
    let back = encoder.sort_from_expr_sort(ExprSort::Datatype(intern_sort_name("OptionInt")));

    assert!(
        matches!(&back, Sort::Datatype(dt) if dt.name == "OptionInt"),
        "reserved OptionInt must use the canonical native datatype: {back:?}"
    );
}

/// Sort::Bool roundtrips perfectly through ExprSort and back.
#[test]
#[timeout(30000)]
fn reverse_roundtrip_bool_preserves() {
    let expr_sort = ay_sort_to_expr_sort(&Sort::Bool);
    assert_eq!(expr_sort, Some(ExprSort::Bool));
    let mut encoder = AYEncoder::new();
    let back = encoder.sort_from_expr_sort(expr_sort.unwrap());
    assert_eq!(
        back,
        Sort::Bool,
        "Sort::Bool reverse roundtrip should preserve"
    );
}
