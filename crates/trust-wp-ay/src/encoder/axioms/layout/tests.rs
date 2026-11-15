// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tests for layout intrinsic axioms (`size_of_logic` / `align_of_logic`).

use ay_dpll::api::SolveResult;

use super::{ALIGN_OF_LOGIC_PREFIX, SIZE_OF_LOGIC_PREFIX};
use crate::{tests::helpers::*, AYEncoder};

fn sat_or_unknown(result: &SolveResult) -> bool {
    matches!(result, SolveResult::Sat)
}

/// Verify the SMT name prefix constants match the actual transformation
/// from `logic_fn_smt_name`. If these are wrong, the axioms silently
/// fail to find any matching declarations.
#[test]
fn test_layout_smt_name_prefixes_match_transformation() {
    let size_smt = trust_wp_core::logic::logic_fn_smt_name("size_of_logic");
    let align_smt = trust_wp_core::logic::logic_fn_smt_name("align_of_logic");

    assert!(
        size_smt.starts_with(SIZE_OF_LOGIC_PREFIX),
        "SIZE_OF_LOGIC_PREFIX {SIZE_OF_LOGIC_PREFIX:?} must be a prefix of {size_smt:?}"
    );
    assert!(
        align_smt.starts_with(ALIGN_OF_LOGIC_PREFIX),
        "ALIGN_OF_LOGIC_PREFIX {ALIGN_OF_LOGIC_PREFIX:?} must be a prefix of {align_smt:?}"
    );
}

/// After asserting layout axioms, `size_of_logic() >= 0` should hold.
/// The solver should not find a model where `size_of_logic() < 0`.
#[test]
#[ntest::timeout(10000)]
fn test_layout_axiom_size_non_negative() {
    let mut encoder = AYEncoder::new();

    // Encode a use of size_of_logic() to trigger placeholder creation
    let expr = logic_fn_call("size_of_logic", vec![]);
    let term = encoder.encode_pure(&expr).expect("encode size_of_logic");

    // Assert layout axioms
    encoder.assert_layout_axioms();

    // Try to assert size_of_logic() < 0 -- should be UNSAT
    let zero = encoder.solver.int_const(0);
    let lt_zero = encoder.solver.lt(term, zero);
    encoder.assert_term(lt_zero);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic() < 0 should be unsatisfiable after layout axioms (#2324)"
    );
}

/// After asserting layout axioms, `align_of_logic() >= 1` should hold.
/// The solver should not find a model where `align_of_logic() <= 0`.
#[test]
#[ntest::timeout(10000)]
fn test_layout_axiom_align_at_least_one() {
    let mut encoder = AYEncoder::new();

    // Encode a use of align_of_logic() to trigger placeholder creation
    let expr = logic_fn_call("align_of_logic", vec![]);
    let term = encoder.encode_pure(&expr).expect("encode align_of_logic");

    // Assert layout axioms
    encoder.assert_layout_axioms();

    // Try to assert align_of_logic() <= 0 -- should be UNSAT
    let zero = encoder.solver.int_const(0);
    let le_zero = encoder.solver.le(term, zero);
    encoder.assert_term(le_zero);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "align_of_logic() <= 0 should be unsatisfiable after layout axioms (#2324)"
    );
}

/// After asserting layout axioms, `size_of_logic() mod align_of_logic() == 0`
/// should hold. The solver should not find a model violating divisibility.
#[test]
#[ntest::timeout(10000)]
fn test_layout_axiom_size_divisible_by_align() {
    let mut encoder = AYEncoder::new();

    // Encode uses of both functions to trigger placeholder creation
    let size_expr = logic_fn_call("size_of_logic", vec![]);
    let align_expr = logic_fn_call("align_of_logic", vec![]);
    let size_term = encoder
        .encode_pure(&size_expr)
        .expect("encode size_of_logic");
    let align_term = encoder
        .encode_pure(&align_expr)
        .expect("encode align_of_logic");

    // Assert layout axioms
    encoder.assert_layout_axioms();

    // Try to assert size % align != 0 -- should be UNSAT
    let remainder = encoder.solver.modulo(size_term, align_term);
    let zero = encoder.solver.int_const(0);
    let eq_zero = encoder.solver.eq(remainder, zero);
    let not_divisible = encoder.solver.not(eq_zero);
    encoder.assert_term(not_divisible);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic() mod align_of_logic() != 0 should be unsatisfiable (#2324)"
    );
}

/// The layout axioms should still permit valid layout values.
/// size_of_logic() == 8, align_of_logic() == 4 should be SAT.
#[test]
#[ntest::timeout(10000)]
fn test_layout_axiom_permits_valid_values() {
    let mut encoder = AYEncoder::new();

    let size_expr = logic_fn_call("size_of_logic", vec![]);
    let align_expr = logic_fn_call("align_of_logic", vec![]);
    let size_term = encoder
        .encode_pure(&size_expr)
        .expect("encode size_of_logic");
    let align_term = encoder
        .encode_pure(&align_expr)
        .expect("encode align_of_logic");

    encoder.assert_layout_axioms();

    // Assert concrete valid values: size=8, align=4
    let eight = encoder.solver.int_const(8);
    let four = encoder.solver.int_const(4);
    let size_eq_8 = encoder.solver.eq(size_term, eight);
    let align_eq_4 = encoder.solver.eq(align_term, four);
    encoder.assert_term(size_eq_8);
    encoder.assert_term(align_eq_4);

    let result = encoder.check_sat();
    assert!(
        sat_or_unknown(&result),
        "size=8, align=4 is a valid layout and should be SAT or UNKNOWN with latest ay, got {result:?} (#2324)"
    );
}

/// Without layout axioms, size_of_logic() < 0 is satisfiable (regression guard).
/// This documents the pre-fix behavior from the design doc.
#[test]
#[ntest::timeout(10000)]
fn test_unconstrained_size_of_logic_negative_is_sat_before_axioms() {
    let mut encoder = AYEncoder::new();

    let expr = logic_fn_call("size_of_logic", vec![]);
    let term = encoder.encode_pure(&expr).expect("encode size_of_logic");

    // Without layout axioms, the solver can freely assign negative values
    let zero = encoder.solver.int_const(0);
    let lt_zero = encoder.solver.lt(term, zero);
    encoder.assert_term(lt_zero);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "without layout axioms, size_of_logic() < 0 is satisfiable (unconstrained UF)"
    );
}

/// After asserting layout axioms, `align_of_logic() == 3` should be UNSAT
/// because 3 is not a power of 2.
#[test]
#[ntest::timeout(10000)]
fn test_layout_axiom_align_rejects_non_power_of_two() {
    let mut encoder = AYEncoder::new();

    let expr = logic_fn_call("align_of_logic", vec![]);
    let term = encoder.encode_pure(&expr).expect("encode align_of_logic");

    encoder.assert_layout_axioms();

    // Try to assert align == 3 -- should be UNSAT (3 is not a power of 2)
    let three = encoder.solver.int_const(3);
    let eq_three = encoder.solver.eq(term, three);
    encoder.assert_term(eq_three);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "align_of_logic() == 3 should be unsatisfiable (not a power of 2) (#2324)"
    );
}

/// After asserting layout axioms, `align_of_logic() == 6` should be UNSAT
/// because 6 is not a power of 2.
#[test]
#[ntest::timeout(10000)]
fn test_layout_axiom_align_rejects_six() {
    let mut encoder = AYEncoder::new();

    let expr = logic_fn_call("align_of_logic", vec![]);
    let term = encoder.encode_pure(&expr).expect("encode align_of_logic");

    encoder.assert_layout_axioms();

    let six = encoder.solver.int_const(6);
    let eq_six = encoder.solver.eq(term, six);
    encoder.assert_term(eq_six);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "align_of_logic() == 6 should be unsatisfiable (not a power of 2) (#2324)"
    );
}

/// After asserting layout axioms, `align_of_logic() == 16` should be SAT
/// because 16 = 2^4 is a valid power of 2.
#[test]
#[ntest::timeout(10000)]
fn test_layout_axiom_align_accepts_power_of_two() {
    let mut encoder = AYEncoder::new();

    let expr = logic_fn_call("align_of_logic", vec![]);
    let term = encoder.encode_pure(&expr).expect("encode align_of_logic");

    encoder.assert_layout_axioms();

    let sixteen = encoder.solver.int_const(16);
    let eq_sixteen = encoder.solver.eq(term, sixteen);
    encoder.assert_term(eq_sixteen);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "align_of_logic() == 16 should be satisfiable (2^4) (#2324)"
    );
}

/// After asserting layout axioms, `align_of_logic() == 1` should be SAT
/// (1 = 2^0, the minimum valid alignment).
#[test]
#[ntest::timeout(10000)]
fn test_layout_axiom_align_accepts_one() {
    let mut encoder = AYEncoder::new();

    let expr = logic_fn_call("align_of_logic", vec![]);
    let term = encoder.encode_pure(&expr).expect("encode align_of_logic");

    encoder.assert_layout_axioms();

    let one = encoder.solver.int_const(1);
    let eq_one = encoder.solver.eq(term, one);
    encoder.assert_term(eq_one);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "align_of_logic() == 1 should be satisfiable (2^0) (#2324)"
    );
}

/// Layout axioms should be a no-op when no layout UFs are declared.
#[test]
#[ntest::timeout(10000)]
fn test_layout_axiom_noop_without_layout_ufs() {
    let mut encoder = AYEncoder::new();

    // Encode some unrelated expression
    let expr = eq(var("x"), int(42));
    encoder.encode_pure(&expr).expect("encode x == 42");

    // assert_layout_axioms should not panic or change behavior
    encoder.assert_layout_axioms();

    // The query should still be satisfiable
    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "layout axioms should be a no-op without layout UFs"
    );
}

/// Combined test: size=4, align=4 is valid (divides evenly, align is power of 2).
/// Exercises interaction between all three axiom categories.
#[test]
#[ntest::timeout(10000)]
fn test_layout_axiom_combined_size_4_align_4() {
    let mut encoder = AYEncoder::new();

    let size_expr = logic_fn_call("size_of_logic", vec![]);
    let align_expr = logic_fn_call("align_of_logic", vec![]);
    let size_term = encoder
        .encode_pure(&size_expr)
        .expect("encode size_of_logic");
    let align_term = encoder
        .encode_pure(&align_expr)
        .expect("encode align_of_logic");

    encoder.assert_layout_axioms();

    // size=4, align=4: valid (4 is power of 2, 4 mod 4 == 0)
    let four = encoder.solver.int_const(4);
    let size_eq = encoder.solver.eq(size_term, four);
    let align_eq = encoder.solver.eq(align_term, four);
    encoder.assert_term(size_eq);
    encoder.assert_term(align_eq);

    let result = encoder.check_sat();
    assert!(
        sat_or_unknown(&result),
        "size=4, align=4 is a valid layout and should be SAT or UNKNOWN with latest ay, got {result:?} (#2324)"
    );
}

/// Combined test: size=3, align=2 is invalid because 3 mod 2 != 0.
/// Uses small values to stay within ay's modular arithmetic completeness.
#[test]
#[ntest::timeout(10000)]
fn test_layout_axiom_combined_size_3_align_2_invalid() {
    let mut encoder = AYEncoder::new();

    let size_expr = logic_fn_call("size_of_logic", vec![]);
    let align_expr = logic_fn_call("align_of_logic", vec![]);
    let size_term = encoder
        .encode_pure(&size_expr)
        .expect("encode size_of_logic");
    let align_term = encoder
        .encode_pure(&align_expr)
        .expect("encode align_of_logic");

    encoder.assert_layout_axioms();

    // size=3, align=2: invalid (3 mod 2 != 0)
    let three = encoder.solver.int_const(3);
    let two = encoder.solver.int_const(2);
    let size_eq = encoder.solver.eq(size_term, three);
    let align_eq = encoder.solver.eq(align_term, two);
    encoder.assert_term(size_eq);
    encoder.assert_term(align_eq);

    let result = encoder.check_sat();
    assert!(
        result == SolveResult::unsat() || result == SolveResult::Unknown,
        "size=3, align=2 should be unsatisfiable or unknown (3 mod 2 != 0) (#2324), got {result:?}"
    );
}

/// Without the power-of-2 axiom, align=3 would be satisfiable.
/// Regression guard documenting pre-fix behavior.
#[test]
#[ntest::timeout(10000)]
fn test_unconstrained_align_three_is_sat_before_axioms() {
    let mut encoder = AYEncoder::new();

    let expr = logic_fn_call("align_of_logic", vec![]);
    let term = encoder.encode_pure(&expr).expect("encode align_of_logic");

    // Do NOT assert layout axioms — check that align=3 is sat without them
    let three = encoder.solver.int_const(3);
    let eq_three = encoder.solver.eq(term, three);
    encoder.assert_term(eq_three);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "without layout axioms, align_of_logic() == 3 is satisfiable (unconstrained UF)"
    );
}

/// Combined test: size=1, align=1 models a u8/bool-like layout.
#[test]
#[ntest::timeout(10000)]
fn test_layout_axiom_combined_size_1_align_1() {
    let mut encoder = AYEncoder::new();

    let size_expr = logic_fn_call("size_of_logic", vec![]);
    let align_expr = logic_fn_call("align_of_logic", vec![]);
    let size_term = encoder
        .encode_pure(&size_expr)
        .expect("encode size_of_logic");
    let align_term = encoder
        .encode_pure(&align_expr)
        .expect("encode align_of_logic");

    encoder.assert_layout_axioms();

    // size=1, align=1: valid (models u8, bool, i8)
    let one = encoder.solver.int_const(1);
    let size_eq = encoder.solver.eq(size_term, one);
    let align_eq = encoder.solver.eq(align_term, one);
    encoder.assert_term(size_eq);
    encoder.assert_term(align_eq);

    let result = encoder.check_sat();
    assert!(
        sat_or_unknown(&result),
        "size=1, align=1 is a valid layout and should be SAT or UNKNOWN with latest ay, got {result:?} (#2324)"
    );
}

/// Combined test: size=0, align=1 is valid (ZSTs like () or [T; 0]).
#[test]
#[ntest::timeout(10000)]
fn test_layout_axiom_combined_size_0_align_1_zst() {
    let mut encoder = AYEncoder::new();

    let size_expr = logic_fn_call("size_of_logic", vec![]);
    let align_expr = logic_fn_call("align_of_logic", vec![]);
    let size_term = encoder
        .encode_pure(&size_expr)
        .expect("encode size_of_logic");
    let align_term = encoder
        .encode_pure(&align_expr)
        .expect("encode align_of_logic");

    encoder.assert_layout_axioms();

    // size=0, align=1: valid (zero-sized types)
    let zero = encoder.solver.int_const(0);
    let one = encoder.solver.int_const(1);
    let size_eq = encoder.solver.eq(size_term, zero);
    let align_eq = encoder.solver.eq(align_term, one);
    encoder.assert_term(size_eq);
    encoder.assert_term(align_eq);

    let result = encoder.check_sat();
    assert!(
        sat_or_unknown(&result),
        "size=0, align=1 is valid and should be SAT or UNKNOWN with latest ay, got {result:?} (#2324)"
    );
}

/// Test that size=0, align=0 is rejected (align must be >= 1 and power of 2).
#[test]
#[ntest::timeout(10000)]
fn test_layout_axiom_rejects_zero_align() {
    let mut encoder = AYEncoder::new();

    let expr = logic_fn_call("align_of_logic", vec![]);
    let term = encoder.encode_pure(&expr).expect("encode align_of_logic");

    encoder.assert_layout_axioms();

    let zero = encoder.solver.int_const(0);
    let eq_zero = encoder.solver.eq(term, zero);
    encoder.assert_term(eq_zero);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "align_of_logic() == 0 should be unsatisfiable (#2324)"
    );
}

/// Verify that the MAX_ALIGN_EXPONENT constant covers Rust's practical
/// alignment requirements. 2^6 = 64 should be accepted (#2674).
#[test]
#[ntest::timeout(10000)]
fn test_layout_axiom_align_accepts_max_exponent() {
    let mut encoder = AYEncoder::new();

    let expr = logic_fn_call("align_of_logic", vec![]);
    let term = encoder.encode_pure(&expr).expect("encode align_of_logic");

    encoder.assert_layout_axioms();

    // 2^MAX_ALIGN_EXPONENT (= 64) is the largest valid alignment in the disjunction
    let max_align = encoder.solver.int_const(1i64 << super::MAX_ALIGN_EXPONENT);
    let eq_max = encoder.solver.eq(term, max_align);
    encoder.assert_term(eq_max);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "align_of_logic() == 2^{} should be satisfiable (max valid alignment) (#2324, #2674)",
        super::MAX_ALIGN_EXPONENT,
    );
}

/// Verify that 2^(MAX_ALIGN_EXPONENT+1) is rejected by the disjunction.
#[test]
#[ntest::timeout(10000)]
fn test_layout_axiom_align_rejects_above_max() {
    let mut encoder = AYEncoder::new();

    let expr = logic_fn_call("align_of_logic", vec![]);
    let term = encoder.encode_pure(&expr).expect("encode align_of_logic");

    encoder.assert_layout_axioms();

    // 2^(MAX_ALIGN_EXPONENT+1) exceeds the alignment disjunction and should be rejected
    let above_max = encoder
        .solver
        .int_const(1i64 << (super::MAX_ALIGN_EXPONENT + 1));
    let eq_above = encoder.solver.eq(term, above_max);
    encoder.assert_term(eq_above);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "align_of_logic() == 2^{} should be unsatisfiable (exceeds max) (#2324, #2674)",
        super::MAX_ALIGN_EXPONENT + 1,
    );
}

// ---- Concrete primitive layout axiom tests (#2324) ----

/// Verify that type-specialized SMT names still start with the base prefix,
/// so generic axioms apply to them too.
#[test]
fn test_type_specialized_smt_names_start_with_base_prefix() {
    let types = [
        "u8", "u16", "u32", "u64", "i8", "i16", "i32", "i64", "bool", "usize", "isize",
    ];
    for ty in types {
        let size_name = format!("size_of_logic__{ty}");
        let align_name = format!("align_of_logic__{ty}");
        let size_smt = trust_wp_core::logic::logic_fn_smt_name(&size_name);
        let align_smt = trust_wp_core::logic::logic_fn_smt_name(&align_name);
        assert!(
            size_smt.starts_with(SIZE_OF_LOGIC_PREFIX),
            "size SMT name for {ty} should start with prefix: {size_smt}"
        );
        assert!(
            align_smt.starts_with(ALIGN_OF_LOGIC_PREFIX),
            "align SMT name for {ty} should start with prefix: {align_smt}"
        );
    }
}

/// Verify that the PRIMITIVE_LAYOUTS table suffixes match the actual SMT
/// name transformation. If these are wrong, concrete axioms silently fail.
#[test]
fn test_primitive_layout_suffixes_match_smt_transformation() {
    let type_to_suffix: &[(&str, &str)] = &[
        ("u8", "____u8"),
        ("u16", "____u16"),
        ("u32", "____u32"),
        ("u64", "____u64"),
        ("i8", "____i8"),
        ("i16", "____i16"),
        ("i32", "____i32"),
        ("i64", "____i64"),
        ("bool", "____bool"),
        ("usize", "____usize"),
        ("isize", "____isize"),
    ];
    for &(ty, expected_suffix) in type_to_suffix {
        let size_name = format!("size_of_logic__{ty}");
        let size_smt = trust_wp_core::logic::logic_fn_smt_name(&size_name);
        let actual_suffix = &size_smt[SIZE_OF_LOGIC_PREFIX.len()..];
        assert_eq!(
            actual_suffix, expected_suffix,
            "SMT suffix for {ty}: expected {expected_suffix:?}, got {actual_suffix:?}"
        );
    }
}

/// After asserting layout axioms, `size_of_logic__u32() == 4` should hold.
/// The solver should not find a model where it equals anything else.
#[test]
#[ntest::timeout(10000)]
fn test_concrete_size_of_u32_is_4() {
    let mut encoder = AYEncoder::new();

    let expr = logic_fn_call("size_of_logic__u32", vec![]);
    let term = encoder
        .encode_pure(&expr)
        .expect("encode size_of_logic__u32");

    encoder.assert_layout_axioms();

    // Assert size != 4 -- should be UNSAT because the axiom pins it to 4
    let four = encoder.solver.int_const(4);
    let neq_four = encoder.solver.neq(term, four);
    encoder.assert_term(neq_four);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__u32() != 4 should be unsatisfiable (#2324)"
    );
}

/// After asserting layout axioms, `align_of_logic__u32() == 4` should hold.
#[test]
#[ntest::timeout(10000)]
fn test_concrete_align_of_u32_is_4() {
    let mut encoder = AYEncoder::new();

    let expr = logic_fn_call("align_of_logic__u32", vec![]);
    let term = encoder
        .encode_pure(&expr)
        .expect("encode align_of_logic__u32");

    encoder.assert_layout_axioms();

    let four = encoder.solver.int_const(4);
    let neq_four = encoder.solver.neq(term, four);
    encoder.assert_term(neq_four);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "align_of_logic__u32() != 4 should be unsatisfiable (#2324)"
    );
}

/// After asserting layout axioms, `size_of_logic__u8() == 1`.
#[test]
#[ntest::timeout(10000)]
fn test_concrete_size_of_u8_is_1() {
    let mut encoder = AYEncoder::new();

    let expr = logic_fn_call("size_of_logic__u8", vec![]);
    let term = encoder
        .encode_pure(&expr)
        .expect("encode size_of_logic__u8");

    encoder.assert_layout_axioms();

    let one = encoder.solver.int_const(1);
    let neq = encoder.solver.neq(term, one);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__u8() != 1 should be unsatisfiable (#2324)"
    );
}

/// After asserting layout axioms, `size_of_logic__bool() == 1`.
#[test]
#[ntest::timeout(10000)]
fn test_concrete_size_of_bool_is_1() {
    let mut encoder = AYEncoder::new();

    let expr = logic_fn_call("size_of_logic__bool", vec![]);
    let term = encoder
        .encode_pure(&expr)
        .expect("encode size_of_logic__bool");

    encoder.assert_layout_axioms();

    let one = encoder.solver.int_const(1);
    let neq = encoder.solver.neq(term, one);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__bool() != 1 should be unsatisfiable (#2324)"
    );
}

/// After asserting layout axioms, `size_of_logic__u64() == 8`.
#[test]
#[ntest::timeout(10000)]
fn test_concrete_size_of_u64_is_8() {
    let mut encoder = AYEncoder::new();

    let expr = logic_fn_call("size_of_logic__u64", vec![]);
    let term = encoder
        .encode_pure(&expr)
        .expect("encode size_of_logic__u64");

    encoder.assert_layout_axioms();

    let eight = encoder.solver.int_const(8);
    let neq = encoder.solver.neq(term, eight);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__u64() != 8 should be unsatisfiable (#2324)"
    );
}

/// After asserting layout axioms, `size_of_logic__usize() == 8` (64-bit).
#[test]
#[ntest::timeout(10000)]
fn test_concrete_size_of_usize_is_8() {
    let mut encoder = AYEncoder::new();

    let expr = logic_fn_call("size_of_logic__usize", vec![]);
    let term = encoder
        .encode_pure(&expr)
        .expect("encode size_of_logic__usize");

    encoder.assert_layout_axioms();

    let eight = encoder.solver.int_const(8);
    let neq = encoder.solver.neq(term, eight);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__usize() != 8 should be unsatisfiable (#2324)"
    );
}

/// Unspecialized `size_of_logic()` (no type suffix) remains unconstrained
/// to any specific value — only generic laws apply.
#[test]
#[ntest::timeout(10000)]
fn test_unspecialized_size_of_logic_not_pinned() {
    let mut encoder = AYEncoder::new();

    let expr = logic_fn_call("size_of_logic", vec![]);
    let term = encoder.encode_pure(&expr).expect("encode size_of_logic");

    encoder.assert_layout_axioms();

    // Unspecialized size_of_logic() == 16 should be satisfiable
    // (16 is a valid size, satisfies >= 0)
    let sixteen = encoder.solver.int_const(16);
    let eq_sixteen = encoder.solver.eq(term, sixteen);
    encoder.assert_term(eq_sixteen);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "unspecialized size_of_logic() == 16 should still be satisfiable (#2324)"
    );
}

// ---- Generic type-relational layout axiom tests ----

/// After asserting layout axioms, `size_of_logic__&T() == size_of_logic__usize()`
/// should hold (references are pointer-sized).
#[test]
#[ntest::timeout(10000)]
fn test_relational_ref_equals_usize() {
    let mut encoder = AYEncoder::new();

    let ref_expr = logic_fn_call("size_of_logic__&T", vec![]);
    let usize_expr = logic_fn_call("size_of_logic__usize", vec![]);
    let ref_term = encoder
        .encode_pure(&ref_expr)
        .expect("encode size_of_logic__&T");
    let usize_term = encoder
        .encode_pure(&usize_expr)
        .expect("encode size_of_logic__usize");

    encoder.assert_layout_axioms();

    // Assert they differ -- should be UNSAT because axiom equates them
    let neq = encoder.solver.neq(ref_term, usize_term);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__&T() != size_of_logic__usize() should be unsatisfiable"
    );
}

/// After asserting layout axioms, `size_of_logic__*const T()` equals
/// `size_of_logic__usize()` (raw pointers are pointer-sized).
#[test]
#[ntest::timeout(10000)]
fn test_relational_raw_ptr_equals_usize() {
    let mut encoder = AYEncoder::new();

    let ptr_expr = logic_fn_call("size_of_logic__*const T", vec![]);
    let usize_expr = logic_fn_call("size_of_logic__usize", vec![]);
    let ptr_term = encoder
        .encode_pure(&ptr_expr)
        .expect("encode size_of_logic__*const T");
    let usize_term = encoder
        .encode_pure(&usize_expr)
        .expect("encode size_of_logic__usize");

    encoder.assert_layout_axioms();

    let neq = encoder.solver.neq(ptr_term, usize_term);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__*const T() != size_of_logic__usize() should be unsatisfiable"
    );
}

/// After asserting layout axioms, `size_of_logic__Box<T>()` equals
/// `size_of_logic__usize()` (Box is pointer-sized).
#[test]
#[ntest::timeout(10000)]
fn test_relational_box_equals_usize() {
    let mut encoder = AYEncoder::new();

    let box_expr = logic_fn_call("size_of_logic__Box<T>", vec![]);
    let usize_expr = logic_fn_call("size_of_logic__usize", vec![]);
    let box_term = encoder
        .encode_pure(&box_expr)
        .expect("encode size_of_logic__Box<T>");
    let usize_term = encoder
        .encode_pure(&usize_expr)
        .expect("encode size_of_logic__usize");

    encoder.assert_layout_axioms();

    let neq = encoder.solver.neq(box_term, usize_term);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__Box<T>() != size_of_logic__usize() should be unsatisfiable"
    );
}

/// After asserting layout axioms, `size_of_logic__Option<&T>()` equals
/// `size_of_logic__usize()` (niche optimization for Option<&T>).
#[test]
#[ntest::timeout(10000)]
fn test_relational_option_ref_equals_usize() {
    let mut encoder = AYEncoder::new();

    let opt_ref_expr = logic_fn_call("size_of_logic__Option<&T>", vec![]);
    let usize_expr = logic_fn_call("size_of_logic__usize", vec![]);
    let opt_ref_term = encoder
        .encode_pure(&opt_ref_expr)
        .expect("encode size_of_logic__Option<&T>");
    let usize_term = encoder
        .encode_pure(&usize_expr)
        .expect("encode size_of_logic__usize");

    encoder.assert_layout_axioms();

    let neq = encoder.solver.neq(opt_ref_term, usize_term);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__Option<&T>() != size_of_logic__usize() should be unsatisfiable"
    );
}

/// After asserting layout axioms, `size_of_logic__Option<Box<T>>()` equals
/// `size_of_logic__usize()` (niche optimization for Option<Box<T>>).
#[test]
#[ntest::timeout(10000)]
fn test_relational_option_box_equals_usize() {
    let mut encoder = AYEncoder::new();

    let opt_box_expr = logic_fn_call("size_of_logic__Option<Box<T>>", vec![]);
    let usize_expr = logic_fn_call("size_of_logic__usize", vec![]);
    let opt_box_term = encoder
        .encode_pure(&opt_box_expr)
        .expect("encode size_of_logic__Option<Box<T>>");
    let usize_term = encoder
        .encode_pure(&usize_expr)
        .expect("encode size_of_logic__usize");

    encoder.assert_layout_axioms();

    let neq = encoder.solver.neq(opt_box_term, usize_term);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__Option<Box<T>>() != size_of_logic__usize() should be unsatisfiable"
    );
}

/// When no `size_of_logic__usize` is declared, pointer-sized axioms fall back
/// to the concrete value 8 (64-bit).
#[test]
#[ntest::timeout(10000)]
fn test_relational_ref_fallback_to_8() {
    let mut encoder = AYEncoder::new();

    // Only declare the reference type, not usize
    let ref_expr = logic_fn_call("size_of_logic__&T", vec![]);
    let ref_term = encoder
        .encode_pure(&ref_expr)
        .expect("encode size_of_logic__&T");

    encoder.assert_layout_axioms();

    // ref size should be pinned to 8
    let eight = encoder.solver.int_const(8);
    let neq = encoder.solver.neq(ref_term, eight);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__&T() != 8 should be unsatisfiable when usize is absent"
    );
}

/// `size_of_logic__()() == 0` for the unit type.
#[test]
#[ntest::timeout(10000)]
fn test_relational_unit_type_is_zero() {
    let mut encoder = AYEncoder::new();

    let unit_expr = logic_fn_call("size_of_logic__()", vec![]);
    let unit_term = encoder
        .encode_pure(&unit_expr)
        .expect("encode size_of_logic__()");

    encoder.assert_layout_axioms();

    let zero = encoder.solver.int_const(0);
    let neq = encoder.solver.neq(unit_term, zero);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__()() != 0 should be unsatisfiable (unit type is ZST)"
    );
}

/// `size_of_logic__[T; 0]() == 0` for zero-length arrays.
#[test]
#[ntest::timeout(10000)]
fn test_relational_array_zero_length_is_zero() {
    let mut encoder = AYEncoder::new();

    let arr_expr = logic_fn_call("size_of_logic__[T; 0]", vec![]);
    let arr_term = encoder
        .encode_pure(&arr_expr)
        .expect("encode size_of_logic__[T; 0]");

    encoder.assert_layout_axioms();

    let zero = encoder.solver.int_const(0);
    let neq = encoder.solver.neq(arr_term, zero);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__[T; 0]() != 0 should be unsatisfiable"
    );
}

/// `size_of_logic__[u32; 5]() == 5 * size_of_logic__u32()` for concrete arrays.
#[test]
#[ntest::timeout(10000)]
fn test_relational_array_concrete_elem_size() {
    let mut encoder = AYEncoder::new();

    let arr_expr = logic_fn_call("size_of_logic__[u32; 5]", vec![]);
    let u32_expr = logic_fn_call("size_of_logic__u32", vec![]);
    let arr_term = encoder
        .encode_pure(&arr_expr)
        .expect("encode size_of_logic__[u32; 5]");
    let _u32_term = encoder
        .encode_pure(&u32_expr)
        .expect("encode size_of_logic__u32");

    encoder.assert_layout_axioms();

    // After axioms: arr == 5 * u32 == 5 * 4 == 20
    let twenty = encoder.solver.int_const(20);
    let neq = encoder.solver.neq(arr_term, twenty);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__[u32; 5]() != 20 should be unsatisfiable"
    );
}

/// `size_of_logic__[T; 5]() == 5 * size_of_logic__T()` for generic arrays.
#[test]
#[ntest::timeout(10000)]
fn test_relational_array_generic_elem_times_n() {
    let mut encoder = AYEncoder::new();

    let arr_expr = logic_fn_call("size_of_logic__[T; 5]", vec![]);
    let t_expr = logic_fn_call("size_of_logic__T", vec![]);
    let arr_term = encoder
        .encode_pure(&arr_expr)
        .expect("encode size_of_logic__[T; 5]");
    let t_term = encoder
        .encode_pure(&t_expr)
        .expect("encode size_of_logic__T");

    encoder.assert_layout_axioms();

    // After axioms: arr == 5 * T
    let five = encoder.solver.int_const(5);
    let expected = encoder.solver.mul(five, t_term);
    let neq = encoder.solver.neq(arr_term, expected);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__[T; 5]() != 5 * size_of_logic__T() should be unsatisfiable"
    );
}

/// Verify is_pointer_sized_type_suffix accepts all expected patterns.
#[test]
fn test_is_pointer_sized_type_suffix_acceptance() {
    let accept = [
        "_____R_T",                       // &T
        "_____R_SomeType",                // &SomeType
        "_____D_const_S_T",               // *const T
        "_____D_mut_S_T",                 // *mut T
        "____Box_LT_T_GT_",               // Box<T>
        "____Box_LT_SomeType_GT_",        // Box<SomeType>
        "____Option_LT__R_T_GT_",         // Option<&T>
        "____Option_LT_Box_LT_T_GT__GT_", // Option<Box<T>>
    ];
    for suffix in &accept {
        assert!(
            super::is_pointer_sized_type_suffix(suffix),
            "should accept pointer-sized suffix: {suffix}"
        );
    }
}

/// Verify is_pointer_sized_type_suffix rejects non-pointer types.
#[test]
fn test_is_pointer_sized_type_suffix_rejection() {
    let reject = [
        "____usize",
        "____u32",
        "____bool",
        "____T",
        "_____LB_T_x3B__S_5_RB_", // [T; 5]
        "_____LP__RP_",           // ()
    ];
    for suffix in &reject {
        assert!(
            !super::is_pointer_sized_type_suffix(suffix),
            "should reject non-pointer suffix: {suffix}"
        );
    }
}

// ---- Tests for lookup_primitive_size and is_unit_type_suffix (#2675) ----

/// Verify lookup_primitive_size finds known primitives.
#[test]
fn test_lookup_primitive_size_known_types() {
    assert_eq!(super::lookup_primitive_size("____u8"), Some(1));
    assert_eq!(super::lookup_primitive_size("____u32"), Some(4));
    assert_eq!(super::lookup_primitive_size("____u64"), Some(8));
    assert_eq!(super::lookup_primitive_size("____i32"), Some(4));
    assert_eq!(super::lookup_primitive_size("____bool"), Some(1));
    assert_eq!(super::lookup_primitive_size("____char"), Some(4));
    assert_eq!(super::lookup_primitive_size("____usize"), Some(8));
}

/// Verify lookup_primitive_size returns None for unknown types.
#[test]
fn test_lookup_primitive_size_unknown_types() {
    assert_eq!(super::lookup_primitive_size("____String"), None);
    assert_eq!(super::lookup_primitive_size("____T"), None);
    assert_eq!(super::lookup_primitive_size("____Vec"), None);
}

/// Verify is_unit_type_suffix matches unit type patterns.
#[test]
fn test_is_unit_type_suffix_acceptance() {
    assert!(super::is_unit_type_suffix("_____LP__RP_"));
    // The element suffix form from array parsing
    assert!(super::is_unit_type_suffix(super::UNIT_TYPE_SUFFIX_ELEMENT));
}

/// Verify is_unit_type_suffix rejects non-unit types.
#[test]
fn test_is_unit_type_suffix_rejection() {
    assert!(!super::is_unit_type_suffix("____u32"));
    assert!(!super::is_unit_type_suffix("____T"));
    assert!(!super::is_unit_type_suffix("____bool"));
}

/// Array size axiom fallback: `[u32; 5]` should get size 20 even when no
/// separate `size_of_logic__u32` UF exists, by looking up the primitive
/// layout table.
#[test]
#[ntest::timeout(10000)]
fn test_array_size_fallback_to_primitive_table() {
    let mut encoder = AYEncoder::new();

    // Only encode the array type -- do NOT encode size_of_logic__u32 separately.
    let expr = logic_fn_call("size_of_logic__[u32; 5]", vec![]);
    let term = encoder
        .encode_pure(&expr)
        .expect("encode size_of_logic__[u32; 5]");

    encoder.assert_layout_axioms();

    // Assert size != 20 -- should be UNSAT because the fallback computes 5 * 4 = 20
    let twenty = encoder.solver.int_const(20);
    let neq = encoder.solver.neq(term, twenty);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__[u32; 5]() != 20 should be UNSAT via primitive fallback (#2675)"
    );
}

/// Array of unit type: `[(); 5]` should have size 0.
#[test]
#[ntest::timeout(10000)]
fn test_array_of_unit_type_size_is_zero() {
    let mut encoder = AYEncoder::new();

    let expr = logic_fn_call("size_of_logic__[(); 5]", vec![]);
    let term = encoder
        .encode_pure(&expr)
        .expect("encode size_of_logic__[(); 5]");

    encoder.assert_layout_axioms();

    // Assert size != 0 -- should be UNSAT because [(); N] is always 0
    let zero = encoder.solver.int_const(0);
    let neq = encoder.solver.neq(term, zero);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__[(); 5]() != 0 should be UNSAT (#2675)"
    );
}

// ---- Generic container relational layout axiom tests (#2693) ----

/// After asserting layout axioms, `size_of_logic__Option<T>() >= size_of_logic__T()`
/// should hold (Option must hold T; niche optimization may make them equal).
#[test]
#[ntest::timeout(10000)]
fn test_relational_option_ge_inner() {
    let mut encoder = AYEncoder::new();

    let option_expr = logic_fn_call("size_of_logic__Option<T>", vec![]);
    let t_expr = logic_fn_call("size_of_logic__T", vec![]);
    let option_term = encoder
        .encode_pure(&option_expr)
        .expect("encode size_of_logic__Option<T>");
    let t_term = encoder
        .encode_pure(&t_expr)
        .expect("encode size_of_logic__T");

    encoder.assert_layout_axioms();

    // Assert Option<T> < T -- should be UNSAT because axiom says Option<T> >= T
    let lt = encoder.solver.lt(option_term, t_term);
    encoder.assert_term(lt);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__Option<T>() < size_of_logic__T() should be unsatisfiable (#2693)"
    );
}

/// Option<T> > T permits valid values like Option<u32> = 8 > T = 4.
#[test]
#[ntest::timeout(10000)]
fn test_relational_option_permits_valid_values() {
    let mut encoder = AYEncoder::new();

    let option_expr = logic_fn_call("size_of_logic__Option<T>", vec![]);
    let t_expr = logic_fn_call("size_of_logic__T", vec![]);
    let option_term = encoder
        .encode_pure(&option_expr)
        .expect("encode size_of_logic__Option<T>");
    let t_term = encoder
        .encode_pure(&t_expr)
        .expect("encode size_of_logic__T");

    encoder.assert_layout_axioms();

    // Option<u32> has size 8 (4 bytes payload + 4 bytes discriminant+padding).
    // Assert Option<T> == 8, T == 4 -- should be SAT
    let eight = encoder.solver.int_const(8);
    let four = encoder.solver.int_const(4);
    let opt_eq = encoder.solver.eq(option_term, eight);
    let t_eq = encoder.solver.eq(t_term, four);
    encoder.assert_term(opt_eq);
    encoder.assert_term(t_eq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "Option<T>=8, T=4 should be satisfiable (#2693)"
    );
}

/// Niche-optimized Option<&T> should NOT trigger the generic Option axiom
/// (it is handled as pointer-sized instead).
#[test]
#[ntest::timeout(10000)]
fn test_relational_option_ref_is_pointer_sized_not_generic() {
    let mut encoder = AYEncoder::new();

    // Option<&T> is niche-optimized to pointer size, not generic Option.
    let opt_ref_expr = logic_fn_call("size_of_logic__Option<&T>", vec![]);
    let opt_ref_term = encoder
        .encode_pure(&opt_ref_expr)
        .expect("encode size_of_logic__Option<&T>");

    encoder.assert_layout_axioms();

    // Option<&T> == 8 (pointer-sized) should be SAT.
    let eight = encoder.solver.int_const(8);
    let eq = encoder.solver.eq(opt_ref_term, eight);
    encoder.assert_term(eq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "Option<&T> == 8 should be satisfiable (pointer-sized, not generic) (#2693)"
    );
}

/// After asserting layout axioms, `size_of_logic__Result<T, E>() >= size_of_logic__T()`
/// should hold (Result must hold T; niche optimization may make them equal).
#[test]
#[ntest::timeout(10000)]
fn test_relational_result_ge_ok() {
    let mut encoder = AYEncoder::new();

    let result_expr = logic_fn_call("size_of_logic__Result<T, E>", vec![]);
    let t_expr = logic_fn_call("size_of_logic__T", vec![]);
    let result_term = encoder
        .encode_pure(&result_expr)
        .expect("encode size_of_logic__Result<T, E>");
    let t_term = encoder
        .encode_pure(&t_expr)
        .expect("encode size_of_logic__T");

    encoder.assert_layout_axioms();

    // Assert Result<T, E> < T -- should be UNSAT
    let lt = encoder.solver.lt(result_term, t_term);
    encoder.assert_term(lt);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__Result<T, E>() < size_of_logic__T() should be unsatisfiable (#2693)"
    );
}

/// After asserting layout axioms, `size_of_logic__Result<T, E>() >= size_of_logic__E()`.
#[test]
#[ntest::timeout(10000)]
fn test_relational_result_ge_err() {
    let mut encoder = AYEncoder::new();

    let result_expr = logic_fn_call("size_of_logic__Result<T, E>", vec![]);
    let e_expr = logic_fn_call("size_of_logic__E", vec![]);
    let result_term = encoder
        .encode_pure(&result_expr)
        .expect("encode size_of_logic__Result<T, E>");
    let e_term = encoder
        .encode_pure(&e_expr)
        .expect("encode size_of_logic__E");

    encoder.assert_layout_axioms();

    // Assert Result<T, E> < E -- should be UNSAT
    let lt = encoder.solver.lt(result_term, e_term);
    encoder.assert_term(lt);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__Result<T, E>() < size_of_logic__E() should be unsatisfiable (#2693)"
    );
}

/// Result<T, E> permits valid values like Result<u32, u8> = 8.
#[test]
#[ntest::timeout(10000)]
fn test_relational_result_permits_valid_values() {
    let mut encoder = AYEncoder::new();

    let result_expr = logic_fn_call("size_of_logic__Result<T, E>", vec![]);
    let t_expr = logic_fn_call("size_of_logic__T", vec![]);
    let e_expr = logic_fn_call("size_of_logic__E", vec![]);
    let result_term = encoder
        .encode_pure(&result_expr)
        .expect("encode size_of_logic__Result<T, E>");
    let t_term = encoder
        .encode_pure(&t_expr)
        .expect("encode size_of_logic__T");
    let e_term = encoder
        .encode_pure(&e_expr)
        .expect("encode size_of_logic__E");

    encoder.assert_layout_axioms();

    // Result<u32, u8>: T=4, E=1, Result=8 (discriminant + max(4,1) + padding)
    let eight = encoder.solver.int_const(8);
    let four = encoder.solver.int_const(4);
    let one = encoder.solver.int_const(1);
    let r_eq = encoder.solver.eq(result_term, eight);
    let t_eq = encoder.solver.eq(t_term, four);
    let e_eq = encoder.solver.eq(e_term, one);
    encoder.assert_term(r_eq);
    encoder.assert_term(t_eq);
    encoder.assert_term(e_eq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "Result<T,E>=8, T=4, E=1 should be satisfiable (#2693)"
    );
}

/// After asserting layout axioms, `size_of_logic__Vec<T>() >= 3 * size_of_logic__usize()`.
#[test]
#[ntest::timeout(10000)]
fn test_relational_vec_at_least_triple_usize() {
    let mut encoder = AYEncoder::new();

    let vec_expr = logic_fn_call("size_of_logic__Vec<T>", vec![]);
    let usize_expr = logic_fn_call("size_of_logic__usize", vec![]);
    let vec_term = encoder
        .encode_pure(&vec_expr)
        .expect("encode size_of_logic__Vec<T>");
    let usize_term = encoder
        .encode_pure(&usize_expr)
        .expect("encode size_of_logic__usize");

    encoder.assert_layout_axioms();

    // Compute 3 * usize = 3 * 8 = 24
    let three = encoder.solver.int_const(3);
    let triple_usize = encoder.solver.mul(three, usize_term);

    // Assert Vec<T> < 3*usize -- should be UNSAT
    let lt = encoder.solver.lt(vec_term, triple_usize);
    encoder.assert_term(lt);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__Vec<T>() < 3 * size_of_logic__usize() should be unsatisfiable (#2693)"
    );
}

/// Vec<T> == 24 is valid (3 * 8 = 24 on 64-bit).
#[test]
#[ntest::timeout(10000)]
fn test_relational_vec_permits_exact_triple_usize() {
    let mut encoder = AYEncoder::new();

    let vec_expr = logic_fn_call("size_of_logic__Vec<T>", vec![]);
    let usize_expr = logic_fn_call("size_of_logic__usize", vec![]);
    let vec_term = encoder
        .encode_pure(&vec_expr)
        .expect("encode size_of_logic__Vec<T>");
    let _usize_term = encoder
        .encode_pure(&usize_expr)
        .expect("encode size_of_logic__usize");

    encoder.assert_layout_axioms();

    // Vec<T> == 24 (3 * 8) should be SAT
    let twenty_four = encoder.solver.int_const(24);
    let eq = encoder.solver.eq(vec_term, twenty_four);
    encoder.assert_term(eq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "Vec<T> == 24 should be satisfiable (3 * 8 on 64-bit) (#2693)"
    );
}

/// Vec<T> without usize declaration falls back to concrete 8 for usize.
#[test]
#[ntest::timeout(10000)]
fn test_relational_vec_fallback_to_concrete_usize() {
    let mut encoder = AYEncoder::new();

    // Only declare Vec, not usize
    let vec_expr = logic_fn_call("size_of_logic__Vec<T>", vec![]);
    let vec_term = encoder
        .encode_pure(&vec_expr)
        .expect("encode size_of_logic__Vec<T>");

    encoder.assert_layout_axioms();

    // Without usize decl, falls back to 8. Vec<T> >= 3*8 = 24.
    // Assert Vec<T> < 24 -- should be UNSAT
    let twenty_four = encoder.solver.int_const(24);
    let lt = encoder.solver.lt(vec_term, twenty_four);
    encoder.assert_term(lt);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "Vec<T> < 24 should be unsatisfiable when usize falls back to 8 (#2693)"
    );
}

// ---- Helper function tests for generic container parsing (#2693) ----

/// Verify extract_generic_inner_type parses Option<T> correctly.
#[test]
fn test_extract_generic_inner_type_option() {
    let suffix = "____Option_LT_T_GT_";
    let result = super::extract_generic_inner_type(suffix, super::OPTION_GENERIC_TYPE_PREFIX);
    assert_eq!(result, Some("T"), "should extract T from Option<T>");
}

/// Verify extract_generic_inner_type parses Option<u32> correctly.
#[test]
fn test_extract_generic_inner_type_option_u32() {
    let suffix = "____Option_LT_u32_GT_";
    let result = super::extract_generic_inner_type(suffix, super::OPTION_GENERIC_TYPE_PREFIX);
    assert_eq!(result, Some("u32"), "should extract u32 from Option<u32>");
}

/// Verify extract_generic_inner_type returns None for malformed suffix.
#[test]
fn test_extract_generic_inner_type_malformed() {
    let suffix = "____Option_LT_T";
    let result = super::extract_generic_inner_type(suffix, super::OPTION_GENERIC_TYPE_PREFIX);
    assert_eq!(result, None, "should return None for missing _GT_");
}

/// Verify extract_result_inner_types parses Result<T, E> correctly.
#[test]
fn test_extract_result_inner_types_basic() {
    let suffix = "____Result_LT_T_C__S_E_GT_";
    let result = super::extract_result_inner_types(suffix);
    assert_eq!(
        result,
        Some(("T", "E")),
        "should extract T and E from Result<T, E>"
    );
}

/// Verify extract_result_inner_types parses Result<u32, String> correctly.
#[test]
fn test_extract_result_inner_types_concrete() {
    let suffix = "____Result_LT_u32_C__S_String_GT_";
    let result = super::extract_result_inner_types(suffix);
    assert_eq!(
        result,
        Some(("u32", "String")),
        "should extract u32 and String from Result<u32, String>"
    );
}

/// Verify extract_result_inner_types returns None for malformed suffix.
#[test]
fn test_extract_result_inner_types_malformed() {
    let suffix = "____Result_LT_T_GT_";
    let result = super::extract_result_inner_types(suffix);
    assert_eq!(result, None, "should return None when no comma separator");
}

/// Option<T> axiom should NOT fire when inner type T has no size_of_logic
/// declaration (graceful no-op).
#[test]
#[ntest::timeout(10000)]
fn test_relational_option_noop_without_inner_decl() {
    let mut encoder = AYEncoder::new();

    // Only declare Option<SomeType>, not SomeType itself
    let option_expr = logic_fn_call("size_of_logic__Option<SomeType>", vec![]);
    let option_term = encoder
        .encode_pure(&option_expr)
        .expect("encode size_of_logic__Option<SomeType>");

    encoder.assert_layout_axioms();

    // Without the inner type's declaration, the relational axiom is skipped.
    // Option<SomeType> should still satisfy generic laws (>= 0).
    let ten = encoder.solver.int_const(10);
    let eq = encoder.solver.eq(option_term, ten);
    encoder.assert_term(eq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "Option<SomeType> == 10 should be SAT when SomeType has no decl (#2693)"
    );
}

/// Result with concrete primitive types: Result<u32, u8>.
#[test]
#[ntest::timeout(10000)]
fn test_relational_result_with_concrete_types() {
    let mut encoder = AYEncoder::new();

    let result_expr = logic_fn_call("size_of_logic__Result<u32, u8>", vec![]);
    let u32_expr = logic_fn_call("size_of_logic__u32", vec![]);
    let u8_expr = logic_fn_call("size_of_logic__u8", vec![]);
    let result_term = encoder
        .encode_pure(&result_expr)
        .expect("encode size_of_logic__Result<u32, u8>");
    let u32_term = encoder
        .encode_pure(&u32_expr)
        .expect("encode size_of_logic__u32");
    let _u8_term = encoder
        .encode_pure(&u8_expr)
        .expect("encode size_of_logic__u8");

    encoder.assert_layout_axioms();

    // Result<u32, u8> >= u32 == 4, so Result >= 4. Assert Result < 4 -- UNSAT.
    let lt = encoder.solver.lt(result_term, u32_term);
    encoder.assert_term(lt);

    // u32 is pinned to 4, so Result < 4 is UNSAT
    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "Result<u32, u8> < u32 (== 4) should be unsatisfiable (#2693)"
    );
}

// ---- Niche optimization soundness tests (#2693) ----

/// `Option<bool>` has size 1 in Rust (niche optimization: bool uses only 0/1,
/// so Option uses 2 for None). The `>=` axiom must permit Option<T> == T.
#[test]
#[ntest::timeout(10000)]
fn test_relational_option_niche_equal_size_is_sat() {
    let mut encoder = AYEncoder::new();

    let option_expr = logic_fn_call("size_of_logic__Option<T>", vec![]);
    let t_expr = logic_fn_call("size_of_logic__T", vec![]);
    let option_term = encoder
        .encode_pure(&option_expr)
        .expect("encode size_of_logic__Option<T>");
    let t_term = encoder
        .encode_pure(&t_expr)
        .expect("encode size_of_logic__T");

    encoder.assert_layout_axioms();

    // Model niche optimization: Option<bool> has size 1, same as bool.
    // Option<T> == T == 1 should be SAT under the >= axiom.
    let one = encoder.solver.int_const(1);
    let opt_eq = encoder.solver.eq(option_term, one);
    let t_eq = encoder.solver.eq(t_term, one);
    encoder.assert_term(opt_eq);
    encoder.assert_term(t_eq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "Option<T>=1, T=1 should be SAT (niche optimization, e.g. Option<bool>) (#2693)"
    );
}

/// `Result<NonZeroI32, ()>` has size 4 in Rust (niche optimization: NonZeroI32
/// uses the zero value for the Err(()) discriminant). The `>=` axiom must
/// permit Result<T, E> == T when niche optimization applies.
#[test]
#[ntest::timeout(10000)]
fn test_relational_result_niche_equal_size_is_sat() {
    let mut encoder = AYEncoder::new();

    let result_expr = logic_fn_call("size_of_logic__Result<T, E>", vec![]);
    let t_expr = logic_fn_call("size_of_logic__T", vec![]);
    let e_expr = logic_fn_call("size_of_logic__E", vec![]);
    let result_term = encoder
        .encode_pure(&result_expr)
        .expect("encode size_of_logic__Result<T, E>");
    let t_term = encoder
        .encode_pure(&t_expr)
        .expect("encode size_of_logic__T");
    let e_term = encoder
        .encode_pure(&e_expr)
        .expect("encode size_of_logic__E");

    encoder.assert_layout_axioms();

    // Model niche optimization: Result<NonZeroI32, ()> has size 4.
    // T=4 (NonZeroI32), E=0 (unit), Result=4.
    let four = encoder.solver.int_const(4);
    let zero = encoder.solver.int_const(0);
    let r_eq = encoder.solver.eq(result_term, four);
    let t_eq = encoder.solver.eq(t_term, four);
    let e_eq = encoder.solver.eq(e_term, zero);
    encoder.assert_term(r_eq);
    encoder.assert_term(t_eq);
    encoder.assert_term(e_eq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "Result<T,E>=4, T=4, E=0 should be SAT (niche optimization) (#2693)"
    );
}

// ---- Tuple layout axiom tests (#2693) ----

/// After asserting layout axioms, `size_of((A, B)) >= size_of(A) + size_of(B)`.
#[test]
#[ntest::timeout(10000)]
fn test_relational_tuple_ge_sum_of_fields() {
    let mut encoder = AYEncoder::new();

    let tuple_expr = logic_fn_call("size_of_logic__(A, B)", vec![]);
    let a_expr = logic_fn_call("size_of_logic__A", vec![]);
    let b_expr = logic_fn_call("size_of_logic__B", vec![]);
    let tuple_term = encoder
        .encode_pure(&tuple_expr)
        .expect("encode size_of_logic__(A, B)");
    let a_term = encoder
        .encode_pure(&a_expr)
        .expect("encode size_of_logic__A");
    let b_term = encoder
        .encode_pure(&b_expr)
        .expect("encode size_of_logic__B");

    encoder.assert_layout_axioms();

    // Assert tuple < A + B -- should be UNSAT
    let sum = encoder.solver.add(a_term, b_term);
    let lt = encoder.solver.lt(tuple_term, sum);
    encoder.assert_term(lt);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of((A, B)) < size_of(A) + size_of(B) should be unsatisfiable (#2693)"
    );
}

/// Tuple size permits valid values: `(u32, u64)` has size 16 >= 4 + 8 = 12.
#[test]
#[ntest::timeout(10000)]
fn test_relational_tuple_permits_valid_values() {
    let mut encoder = AYEncoder::new();

    let tuple_expr = logic_fn_call("size_of_logic__(A, B)", vec![]);
    let a_expr = logic_fn_call("size_of_logic__A", vec![]);
    let b_expr = logic_fn_call("size_of_logic__B", vec![]);
    let tuple_term = encoder
        .encode_pure(&tuple_expr)
        .expect("encode size_of_logic__(A, B)");
    let a_term = encoder
        .encode_pure(&a_expr)
        .expect("encode size_of_logic__A");
    let b_term = encoder
        .encode_pure(&b_expr)
        .expect("encode size_of_logic__B");

    encoder.assert_layout_axioms();

    // (u32, u64): A=4, B=8, tuple=16 (12 + padding). Should be SAT.
    let sixteen = encoder.solver.int_const(16);
    let four = encoder.solver.int_const(4);
    let eight = encoder.solver.int_const(8);
    let tuple_eq = encoder.solver.eq(tuple_term, sixteen);
    let a_eq = encoder.solver.eq(a_term, four);
    let b_eq = encoder.solver.eq(b_term, eight);
    encoder.assert_term(tuple_eq);
    encoder.assert_term(a_eq);
    encoder.assert_term(b_eq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "Tuple (A=4, B=8) = 16 should be satisfiable (#2693)"
    );
}

/// Tuple size with concrete primitive fields: `(u32, u64)` with known types.
#[test]
#[ntest::timeout(10000)]
fn test_relational_tuple_concrete_primitives() {
    let mut encoder = AYEncoder::new();

    let tuple_expr = logic_fn_call("size_of_logic__(u32, u64)", vec![]);
    let u32_expr = logic_fn_call("size_of_logic__u32", vec![]);
    let u64_expr = logic_fn_call("size_of_logic__u64", vec![]);
    let tuple_term = encoder
        .encode_pure(&tuple_expr)
        .expect("encode size_of_logic__(u32, u64)");
    let _u32_term = encoder
        .encode_pure(&u32_expr)
        .expect("encode size_of_logic__u32");
    let _u64_term = encoder
        .encode_pure(&u64_expr)
        .expect("encode size_of_logic__u64");

    encoder.assert_layout_axioms();

    // (u32, u64): u32=4, u64=8, tuple >= 4+8 = 12.
    // Assert tuple < 12 -- should be UNSAT.
    let twelve = encoder.solver.int_const(12);
    let lt = encoder.solver.lt(tuple_term, twelve);
    encoder.assert_term(lt);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of((u32, u64)) < 12 should be unsatisfiable (#2693)"
    );
}

/// Tuple size with primitive fallback: `(u32, u64)` without separate size_of declarations.
#[test]
#[ntest::timeout(10000)]
fn test_relational_tuple_primitive_fallback() {
    let mut encoder = AYEncoder::new();

    // Only declare the tuple type, not the field types separately.
    let tuple_expr = logic_fn_call("size_of_logic__(u32, u64)", vec![]);
    let tuple_term = encoder
        .encode_pure(&tuple_expr)
        .expect("encode size_of_logic__(u32, u64)");

    encoder.assert_layout_axioms();

    // Primitive fallback: u32=4 + u64=8 = 12. Tuple >= 12.
    // Assert tuple < 12 -- should be UNSAT.
    let twelve = encoder.solver.int_const(12);
    let lt = encoder.solver.lt(tuple_term, twelve);
    encoder.assert_term(lt);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of((u32, u64)) < 12 should be UNSAT via primitive fallback (#2693)"
    );
}

/// Three-element tuple: `(A, B, C)` >= size_of(A) + size_of(B) + size_of(C).
#[test]
#[ntest::timeout(10000)]
fn test_relational_tuple_three_fields() {
    let mut encoder = AYEncoder::new();

    let tuple_expr = logic_fn_call("size_of_logic__(A, B, C)", vec![]);
    let a_expr = logic_fn_call("size_of_logic__A", vec![]);
    let b_expr = logic_fn_call("size_of_logic__B", vec![]);
    let c_expr = logic_fn_call("size_of_logic__C", vec![]);
    let tuple_term = encoder
        .encode_pure(&tuple_expr)
        .expect("encode size_of_logic__(A, B, C)");
    let a_term = encoder
        .encode_pure(&a_expr)
        .expect("encode size_of_logic__A");
    let b_term = encoder
        .encode_pure(&b_expr)
        .expect("encode size_of_logic__B");
    let c_term = encoder
        .encode_pure(&c_expr)
        .expect("encode size_of_logic__C");

    encoder.assert_layout_axioms();

    // Assert tuple < A + B + C -- should be UNSAT
    let sum_ab = encoder.solver.add(a_term, b_term);
    let sum_abc = encoder.solver.add(sum_ab, c_term);
    let lt = encoder.solver.lt(tuple_term, sum_abc);
    encoder.assert_term(lt);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of((A, B, C)) < A + B + C should be unsatisfiable (#2693)"
    );
}

/// Tuple axiom is a no-op for unknown field types without declarations.
#[test]
#[ntest::timeout(10000)]
fn test_relational_tuple_noop_unknown_fields() {
    let mut encoder = AYEncoder::new();

    // Only declare the tuple, not its field types.
    let tuple_expr = logic_fn_call("size_of_logic__(Foo, Bar)", vec![]);
    let tuple_term = encoder
        .encode_pure(&tuple_expr)
        .expect("encode size_of_logic__(Foo, Bar)");

    encoder.assert_layout_axioms();

    // Without field declarations, the tuple axiom is skipped.
    // The tuple only satisfies generic laws (>= 0). Assert == 5 -- SAT.
    let five = encoder.solver.int_const(5);
    let eq = encoder.solver.eq(tuple_term, five);
    encoder.assert_term(eq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "Tuple with unknown fields == 5 should be SAT (no tuple axiom applied) (#2693)"
    );
}

/// Tuple with exact-sum values is SAT: `(u32, u32)` >= 4+4=8, and tuple==8.
#[test]
#[ntest::timeout(10000)]
fn test_relational_tuple_exact_sum_is_sat() {
    let mut encoder = AYEncoder::new();

    let tuple_expr = logic_fn_call("size_of_logic__(u32, u32)", vec![]);
    let u32_expr = logic_fn_call("size_of_logic__u32", vec![]);
    let tuple_term = encoder
        .encode_pure(&tuple_expr)
        .expect("encode size_of_logic__(u32, u32)");
    let _u32_term = encoder
        .encode_pure(&u32_expr)
        .expect("encode size_of_logic__u32");

    encoder.assert_layout_axioms();

    // (u32, u32) >= 4+4=8. Tuple == 8 is exactly the minimum. Should be SAT.
    let eight = encoder.solver.int_const(8);
    let eq = encoder.solver.eq(tuple_term, eight);
    encoder.assert_term(eq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "(u32, u32) == 8 should be SAT (no padding needed) (#2693)"
    );
}

// ---- Helper function tests for tuple parsing (#2693) ----

/// Verify extract_tuple_field_types parses (A, B) correctly.
#[test]
fn test_extract_tuple_field_types_two_fields() {
    let suffix = "_____LP_A_C__S_B_RP_";
    let result = super::extract_tuple_field_types(suffix);
    assert_eq!(
        result,
        Some(vec!["A", "B"]),
        "should extract A and B from (A, B)"
    );
}

/// Verify extract_tuple_field_types parses (u32, u64) correctly.
#[test]
fn test_extract_tuple_field_types_primitives() {
    let suffix = "_____LP_u32_C__S_u64_RP_";
    let result = super::extract_tuple_field_types(suffix);
    assert_eq!(
        result,
        Some(vec!["u32", "u64"]),
        "should extract u32 and u64 from (u32, u64)"
    );
}

/// Verify extract_tuple_field_types parses three-element tuple (A, B, C).
#[test]
fn test_extract_tuple_field_types_three_fields() {
    let suffix = "_____LP_A_C__S_B_C__S_C_RP_";
    let result = super::extract_tuple_field_types(suffix);
    assert_eq!(
        result,
        Some(vec!["A", "B", "C"]),
        "should extract A, B, C from (A, B, C)"
    );
}

/// Verify extract_tuple_field_types returns None for unit type `()`.
#[test]
fn test_extract_tuple_field_types_unit_type() {
    let suffix = "_____LP__RP_";
    let result = super::extract_tuple_field_types(suffix);
    assert_eq!(result, None, "should return None for unit type ()");
}

/// Verify extract_tuple_field_types returns None for malformed suffix.
#[test]
fn test_extract_tuple_field_types_malformed() {
    let suffix = "_____LP_A_C__S_B";
    let result = super::extract_tuple_field_types(suffix);
    assert_eq!(result, None, "should return None for missing _RP_");
}

// ---- Transparent wrapper layout axiom tests (#2693) ----

/// After asserting layout axioms, `size_of_logic__Wrapping<T>() == size_of_logic__T()`
/// should hold (Wrapping is `#[repr(transparent)]`).
#[test]
#[ntest::timeout(10000)]
fn test_relational_wrapping_equals_inner() {
    let mut encoder = AYEncoder::new();

    let wrapper_expr = logic_fn_call("size_of_logic__Wrapping<T>", vec![]);
    let t_expr = logic_fn_call("size_of_logic__T", vec![]);
    let wrapper_term = encoder
        .encode_pure(&wrapper_expr)
        .expect("encode size_of_logic__Wrapping<T>");
    let t_term = encoder
        .encode_pure(&t_expr)
        .expect("encode size_of_logic__T");

    encoder.assert_layout_axioms();

    // Assert Wrapping<T> != T -- should be UNSAT
    let neq = encoder.solver.neq(wrapper_term, t_term);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__Wrapping<T>() != size_of_logic__T() should be unsatisfiable (#2693)"
    );
}

/// Wrapping<T> permits valid values when equal to T.
#[test]
#[ntest::timeout(10000)]
fn test_relational_wrapping_permits_valid_values() {
    let mut encoder = AYEncoder::new();

    let wrapper_expr = logic_fn_call("size_of_logic__Wrapping<T>", vec![]);
    let t_expr = logic_fn_call("size_of_logic__T", vec![]);
    let wrapper_term = encoder
        .encode_pure(&wrapper_expr)
        .expect("encode size_of_logic__Wrapping<T>");
    let t_term = encoder
        .encode_pure(&t_expr)
        .expect("encode size_of_logic__T");

    encoder.assert_layout_axioms();

    // Wrapping<u32>: wrapper=4, T=4. Should be SAT.
    let four = encoder.solver.int_const(4);
    let w_eq = encoder.solver.eq(wrapper_term, four);
    let t_eq = encoder.solver.eq(t_term, four);
    encoder.assert_term(w_eq);
    encoder.assert_term(t_eq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "Wrapping<T>=4, T=4 should be satisfiable (#2693)"
    );
}

/// After asserting layout axioms, `size_of_logic__NonZero<T>() == size_of_logic__T()`.
#[test]
#[ntest::timeout(10000)]
fn test_relational_nonzero_equals_inner() {
    let mut encoder = AYEncoder::new();

    let wrapper_expr = logic_fn_call("size_of_logic__NonZero<T>", vec![]);
    let t_expr = logic_fn_call("size_of_logic__T", vec![]);
    let wrapper_term = encoder
        .encode_pure(&wrapper_expr)
        .expect("encode size_of_logic__NonZero<T>");
    let t_term = encoder
        .encode_pure(&t_expr)
        .expect("encode size_of_logic__T");

    encoder.assert_layout_axioms();

    let neq = encoder.solver.neq(wrapper_term, t_term);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__NonZero<T>() != size_of_logic__T() should be unsatisfiable (#2693)"
    );
}

/// After asserting layout axioms, `size_of_logic__ManuallyDrop<T>() == size_of_logic__T()`.
#[test]
#[ntest::timeout(10000)]
fn test_relational_manually_drop_equals_inner() {
    let mut encoder = AYEncoder::new();

    let wrapper_expr = logic_fn_call("size_of_logic__ManuallyDrop<T>", vec![]);
    let t_expr = logic_fn_call("size_of_logic__T", vec![]);
    let wrapper_term = encoder
        .encode_pure(&wrapper_expr)
        .expect("encode size_of_logic__ManuallyDrop<T>");
    let t_term = encoder
        .encode_pure(&t_expr)
        .expect("encode size_of_logic__T");

    encoder.assert_layout_axioms();

    let neq = encoder.solver.neq(wrapper_term, t_term);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__ManuallyDrop<T>() != size_of_logic__T() should be unsatisfiable (#2693)"
    );
}

/// After asserting layout axioms, `size_of_logic__MaybeUninit<T>() == size_of_logic__T()`.
#[test]
#[ntest::timeout(10000)]
fn test_relational_maybe_uninit_equals_inner() {
    let mut encoder = AYEncoder::new();

    let wrapper_expr = logic_fn_call("size_of_logic__MaybeUninit<T>", vec![]);
    let t_expr = logic_fn_call("size_of_logic__T", vec![]);
    let wrapper_term = encoder
        .encode_pure(&wrapper_expr)
        .expect("encode size_of_logic__MaybeUninit<T>");
    let t_term = encoder
        .encode_pure(&t_expr)
        .expect("encode size_of_logic__T");

    encoder.assert_layout_axioms();

    let neq = encoder.solver.neq(wrapper_term, t_term);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__MaybeUninit<T>() != size_of_logic__T() should be unsatisfiable (#2693)"
    );
}

/// After asserting layout axioms, `size_of_logic__Pin<P>() == size_of_logic__P()`.
#[test]
#[ntest::timeout(10000)]
fn test_relational_pin_equals_inner() {
    let mut encoder = AYEncoder::new();

    let wrapper_expr = logic_fn_call("size_of_logic__Pin<P>", vec![]);
    let p_expr = logic_fn_call("size_of_logic__P", vec![]);
    let wrapper_term = encoder
        .encode_pure(&wrapper_expr)
        .expect("encode size_of_logic__Pin<P>");
    let p_term = encoder
        .encode_pure(&p_expr)
        .expect("encode size_of_logic__P");

    encoder.assert_layout_axioms();

    let neq = encoder.solver.neq(wrapper_term, p_term);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__Pin<P>() != size_of_logic__P() should be unsatisfiable (#2693)"
    );
}

/// After asserting layout axioms, `size_of_logic__Cell<T>() == size_of_logic__T()`.
#[test]
#[ntest::timeout(10000)]
fn test_relational_cell_equals_inner() {
    let mut encoder = AYEncoder::new();

    let wrapper_expr = logic_fn_call("size_of_logic__Cell<T>", vec![]);
    let t_expr = logic_fn_call("size_of_logic__T", vec![]);
    let wrapper_term = encoder
        .encode_pure(&wrapper_expr)
        .expect("encode size_of_logic__Cell<T>");
    let t_term = encoder
        .encode_pure(&t_expr)
        .expect("encode size_of_logic__T");

    encoder.assert_layout_axioms();

    let neq = encoder.solver.neq(wrapper_term, t_term);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__Cell<T>() != size_of_logic__T() should be unsatisfiable (#2693)"
    );
}

/// After asserting layout axioms, `size_of_logic__UnsafeCell<T>() == size_of_logic__T()`.
#[test]
#[ntest::timeout(10000)]
fn test_relational_unsafe_cell_equals_inner() {
    let mut encoder = AYEncoder::new();

    let wrapper_expr = logic_fn_call("size_of_logic__UnsafeCell<T>", vec![]);
    let t_expr = logic_fn_call("size_of_logic__T", vec![]);
    let wrapper_term = encoder
        .encode_pure(&wrapper_expr)
        .expect("encode size_of_logic__UnsafeCell<T>");
    let t_term = encoder
        .encode_pure(&t_expr)
        .expect("encode size_of_logic__T");

    encoder.assert_layout_axioms();

    let neq = encoder.solver.neq(wrapper_term, t_term);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__UnsafeCell<T>() != size_of_logic__T() should be unsatisfiable (#2693)"
    );
}

/// After asserting layout axioms, `size_of_logic__Saturating<T>() == size_of_logic__T()`.
#[test]
#[ntest::timeout(10000)]
fn test_relational_saturating_equals_inner() {
    let mut encoder = AYEncoder::new();

    let wrapper_expr = logic_fn_call("size_of_logic__Saturating<T>", vec![]);
    let t_expr = logic_fn_call("size_of_logic__T", vec![]);
    let wrapper_term = encoder
        .encode_pure(&wrapper_expr)
        .expect("encode size_of_logic__Saturating<T>");
    let t_term = encoder
        .encode_pure(&t_expr)
        .expect("encode size_of_logic__T");

    encoder.assert_layout_axioms();

    let neq = encoder.solver.neq(wrapper_term, t_term);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__Saturating<T>() != size_of_logic__T() should be unsatisfiable (#2693)"
    );
}

/// Transparent wrapper with concrete primitive inner type: `Wrapping<u32>` == 4
/// even without a separate `size_of_logic__u32` declaration.
#[test]
#[ntest::timeout(10000)]
fn test_relational_wrapping_primitive_fallback() {
    let mut encoder = AYEncoder::new();

    // Only declare the wrapper, not the inner type.
    let wrapper_expr = logic_fn_call("size_of_logic__Wrapping<u32>", vec![]);
    let wrapper_term = encoder
        .encode_pure(&wrapper_expr)
        .expect("encode size_of_logic__Wrapping<u32>");

    encoder.assert_layout_axioms();

    // Primitive fallback: u32 size is 4. Assert wrapper != 4 -- UNSAT.
    let four = encoder.solver.int_const(4);
    let neq = encoder.solver.neq(wrapper_term, four);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__Wrapping<u32>() != 4 should be UNSAT via primitive fallback (#2693)"
    );
}

/// Transparent wrapper with no inner type declaration is a no-op.
#[test]
#[ntest::timeout(10000)]
fn test_relational_wrapping_noop_unknown_inner() {
    let mut encoder = AYEncoder::new();

    // Only declare the wrapper, inner type SomeType is unknown.
    let wrapper_expr = logic_fn_call("size_of_logic__Wrapping<SomeType>", vec![]);
    let wrapper_term = encoder
        .encode_pure(&wrapper_expr)
        .expect("encode size_of_logic__Wrapping<SomeType>");

    encoder.assert_layout_axioms();

    // Without inner type declaration, axiom is skipped. Wrapper == 10 should be SAT.
    let ten = encoder.solver.int_const(10);
    let eq = encoder.solver.eq(wrapper_term, ten);
    encoder.assert_term(eq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::Sat,
        "Wrapping<SomeType> == 10 should be SAT when SomeType has no decl (#2693)"
    );
}

/// Transparent wrapper with concrete type via declaration: `NonZero<u32>` == `u32`.
#[test]
#[ntest::timeout(10000)]
fn test_relational_nonzero_with_concrete_inner_decl() {
    let mut encoder = AYEncoder::new();

    let wrapper_expr = logic_fn_call("size_of_logic__NonZero<u32>", vec![]);
    let u32_expr = logic_fn_call("size_of_logic__u32", vec![]);
    let wrapper_term = encoder
        .encode_pure(&wrapper_expr)
        .expect("encode size_of_logic__NonZero<u32>");
    let _u32_term = encoder
        .encode_pure(&u32_expr)
        .expect("encode size_of_logic__u32");

    encoder.assert_layout_axioms();

    // NonZero<u32> == u32 == 4. Assert wrapper != 4 -- UNSAT.
    let four = encoder.solver.int_const(4);
    let neq = encoder.solver.neq(wrapper_term, four);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__NonZero<u32>() != 4 should be unsatisfiable (#2693)"
    );
}

// ---- NonZero transparent layout axiom tests (#2669) ----

/// Verify that the NONZERO_GENERIC_PREFIX constant matches the actual SMT
/// transformation for `NonZero<T>`.
#[test]
fn test_nonzero_smt_name_prefix_matches_transformation() {
    // NonZero<u32> encodes as size_of_logic__NonZero<u32>
    let name = "size_of_logic__NonZero<u32>";
    let smt = trust_wp_core::logic::logic_fn_smt_name(name);
    // The full SMT name should contain the generic prefix
    let suffix = &smt[SIZE_OF_LOGIC_PREFIX.len()..];
    assert!(
        suffix.starts_with(super::NONZERO_GENERIC_PREFIX),
        "NonZero<u32> suffix should start with NONZERO_GENERIC_PREFIX: got {suffix:?}"
    );
}

/// Verify that the NONZERO_LEGACY_LAYOUTS table suffixes match the actual
/// SMT name transformation.
#[test]
fn test_nonzero_legacy_suffixes_match_smt_transformation() {
    let type_to_suffix: &[(&str, &str)] = &[
        ("NonZeroU8", "____NonZeroU8"),
        ("NonZeroU32", "____NonZeroU32"),
        ("NonZeroI64", "____NonZeroI64"),
        ("NonZeroUsize", "____NonZeroUsize"),
    ];
    for &(ty, expected_suffix) in type_to_suffix {
        let size_name = format!("size_of_logic__{ty}");
        let size_smt = trust_wp_core::logic::logic_fn_smt_name(&size_name);
        let actual_suffix = &size_smt[SIZE_OF_LOGIC_PREFIX.len()..];
        assert_eq!(
            actual_suffix, expected_suffix,
            "SMT suffix for {ty}: expected {expected_suffix:?}, got {actual_suffix:?}"
        );
    }
}

/// After asserting layout axioms, `size_of_logic__NonZero<u32>()` should equal
/// `size_of_logic__u32()` because NonZero<T> is #[repr(transparent)].
#[test]
#[ntest::timeout(10000)]
fn test_nonzero_generic_size_equals_inner_type() {
    let mut encoder = AYEncoder::new();

    let nz_expr = logic_fn_call("size_of_logic__NonZero<u32>", vec![]);
    let u32_expr = logic_fn_call("size_of_logic__u32", vec![]);
    let nz_term = encoder
        .encode_pure(&nz_expr)
        .expect("encode size_of_logic__NonZero<u32>");
    let u32_term = encoder
        .encode_pure(&u32_expr)
        .expect("encode size_of_logic__u32");

    encoder.assert_layout_axioms();

    // Assert they differ -- should be UNSAT because NonZero<u32> == u32
    let neq = encoder.solver.neq(nz_term, u32_term);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__NonZero<u32>() != size_of_logic__u32() should be UNSAT (#2669)"
    );
}

/// After asserting layout axioms, `size_of_logic__NonZero<u32>()` should be
/// pinned to 4 (transitively through the u32 concrete axiom).
#[test]
#[ntest::timeout(10000)]
fn test_nonzero_generic_size_pinned_to_concrete() {
    let mut encoder = AYEncoder::new();

    let nz_expr = logic_fn_call("size_of_logic__NonZero<u32>", vec![]);
    let u32_expr = logic_fn_call("size_of_logic__u32", vec![]);
    let nz_term = encoder
        .encode_pure(&nz_expr)
        .expect("encode size_of_logic__NonZero<u32>");
    let _u32_term = encoder
        .encode_pure(&u32_expr)
        .expect("encode size_of_logic__u32");

    encoder.assert_layout_axioms();

    // NonZero<u32> size should be 4 (same as u32)
    let four = encoder.solver.int_const(4);
    let neq = encoder.solver.neq(nz_term, four);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__NonZero<u32>() != 4 should be UNSAT (#2669)"
    );
}

/// After asserting layout axioms, `align_of_logic__NonZero<u32>()` should
/// equal `align_of_logic__u32()`.
#[test]
#[ntest::timeout(10000)]
fn test_nonzero_generic_align_equals_inner_type() {
    let mut encoder = AYEncoder::new();

    let nz_expr = logic_fn_call("align_of_logic__NonZero<u32>", vec![]);
    let u32_expr = logic_fn_call("align_of_logic__u32", vec![]);
    let nz_term = encoder
        .encode_pure(&nz_expr)
        .expect("encode align_of_logic__NonZero<u32>");
    let u32_term = encoder
        .encode_pure(&u32_expr)
        .expect("encode align_of_logic__u32");

    encoder.assert_layout_axioms();

    let neq = encoder.solver.neq(nz_term, u32_term);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "align_of_logic__NonZero<u32>() != align_of_logic__u32() should be UNSAT (#2669)"
    );
}

/// After asserting layout axioms, legacy `size_of_logic__NonZeroU32()` should
/// equal `size_of_logic__u32()`.
#[test]
#[ntest::timeout(10000)]
fn test_nonzero_legacy_size_equals_inner_type() {
    let mut encoder = AYEncoder::new();

    let nz_expr = logic_fn_call("size_of_logic__NonZeroU32", vec![]);
    let u32_expr = logic_fn_call("size_of_logic__u32", vec![]);
    let nz_term = encoder
        .encode_pure(&nz_expr)
        .expect("encode size_of_logic__NonZeroU32");
    let u32_term = encoder
        .encode_pure(&u32_expr)
        .expect("encode size_of_logic__u32");

    encoder.assert_layout_axioms();

    let neq = encoder.solver.neq(nz_term, u32_term);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__NonZeroU32() != size_of_logic__u32() should be UNSAT (#2669)"
    );
}

/// After asserting layout axioms, legacy `align_of_logic__NonZeroI64()` should
/// equal `align_of_logic__i64()`.
#[test]
#[ntest::timeout(10000)]
fn test_nonzero_legacy_align_equals_inner_type() {
    let mut encoder = AYEncoder::new();

    let nz_expr = logic_fn_call("align_of_logic__NonZeroI64", vec![]);
    let i64_expr = logic_fn_call("align_of_logic__i64", vec![]);
    let nz_term = encoder
        .encode_pure(&nz_expr)
        .expect("encode align_of_logic__NonZeroI64");
    let i64_term = encoder
        .encode_pure(&i64_expr)
        .expect("encode align_of_logic__i64");

    encoder.assert_layout_axioms();

    let neq = encoder.solver.neq(nz_term, i64_term);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "align_of_logic__NonZeroI64() != align_of_logic__i64() should be UNSAT (#2669)"
    );
}

/// When the inner type declaration is absent but is a known primitive,
/// `size_of_logic__NonZeroU8()` should fall back to the concrete value 1.
#[test]
#[ntest::timeout(10000)]
fn test_nonzero_legacy_fallback_to_concrete() {
    let mut encoder = AYEncoder::new();

    // Only declare NonZeroU8, NOT u8 — triggers concrete fallback
    let nz_expr = logic_fn_call("size_of_logic__NonZeroU8", vec![]);
    let nz_term = encoder
        .encode_pure(&nz_expr)
        .expect("encode size_of_logic__NonZeroU8");

    encoder.assert_layout_axioms();

    // Should be pinned to 1 (u8 size) via fallback
    let one = encoder.solver.int_const(1);
    let neq = encoder.solver.neq(nz_term, one);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__NonZeroU8() != 1 should be UNSAT via concrete fallback (#2669)"
    );
}

/// When the inner type declaration is absent but is a known primitive,
/// `size_of_logic__NonZero<u64>()` should fall back to the concrete value 8.
#[test]
#[ntest::timeout(10000)]
fn test_nonzero_generic_fallback_to_concrete() {
    let mut encoder = AYEncoder::new();

    // Only declare NonZero<u64>, NOT u64 — triggers concrete fallback
    let nz_expr = logic_fn_call("size_of_logic__NonZero<u64>", vec![]);
    let nz_term = encoder
        .encode_pure(&nz_expr)
        .expect("encode size_of_logic__NonZero<u64>");

    encoder.assert_layout_axioms();

    // Should be pinned to 8 (u64 size) via fallback
    let eight = encoder.solver.int_const(8);
    let neq = encoder.solver.neq(nz_term, eight);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__NonZero<u64>() != 8 should be UNSAT via concrete fallback (#2669)"
    );
}

/// `size_of_logic__NonZeroUsize()` should equal `size_of_logic__usize()` (8 on 64-bit).
#[test]
#[ntest::timeout(10000)]
fn test_nonzero_legacy_usize_size() {
    let mut encoder = AYEncoder::new();

    let nz_expr = logic_fn_call("size_of_logic__NonZeroUsize", vec![]);
    let usize_expr = logic_fn_call("size_of_logic__usize", vec![]);
    let nz_term = encoder
        .encode_pure(&nz_expr)
        .expect("encode size_of_logic__NonZeroUsize");
    let usize_term = encoder
        .encode_pure(&usize_expr)
        .expect("encode size_of_logic__usize");

    encoder.assert_layout_axioms();

    let neq = encoder.solver.neq(nz_term, usize_term);
    encoder.assert_term(neq);

    assert_eq!(
        encoder.check_sat(),
        SolveResult::unsat(),
        "size_of_logic__NonZeroUsize() != size_of_logic__usize() should be UNSAT (#2669)"
    );
}

/// The old body sliced off `RESULT_TYPE_PREFIX.len()` bytes without checking
/// the input began with that prefix — or was that long — so anything shorter
/// panicked on a byte range. These inputs reach this function from encoded SMT
/// type suffixes, which are not guaranteed to be Result types at all.
#[test]
fn extract_result_inner_types_answers_none_instead_of_panicking_on_short_input() {
    use super::extract_result_inner_types;
    assert_eq!(extract_result_inner_types(""), None);
    assert_eq!(extract_result_inner_types("__"), None);
    assert_eq!(extract_result_inner_types("____Option_LT_u32_GT_"), None);
    // A well-formed Result suffix still splits exactly as before.
    assert_eq!(
        extract_result_inner_types("____Result_LT_u32_C__S_String_GT_"),
        Some(("u32", "String"))
    );
}
