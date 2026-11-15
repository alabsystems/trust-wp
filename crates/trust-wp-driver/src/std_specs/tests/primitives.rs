// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use super::{super::*, helpers::*};

#[test]
fn test_lookup_bool_then() {
    let spec = lookup_std_spec("bool::then").unwrap();
    assert!(spec.requires.is_empty());
    assert_eq!(spec.ensures.len(), 1);
    assert!(spec.ensures[0].contains("match"));
}

#[test]
fn test_lookup_bool_then_some() {
    let spec = lookup_std_spec("bool::then_some").unwrap();
    assert!(spec.requires.is_empty());
    assert_eq!(spec.ensures.len(), 1);
    assert!(spec.ensures[0].contains("match"));
}
#[test]
fn test_lookup_checked_add_all_types() {
    // Verify all integer types map to checked_add spec.
    // Implication-style postconditions: 3 ensures per spec (#1296).
    for path in &[
        "i8::checked_add",
        "i32::checked_add",
        "i128::checked_add",
        "u8::checked_add",
        "u32::checked_add",
        "usize::checked_add",
    ] {
        let spec = lookup_std_spec(path)
            .unwrap_or_else(|| panic!("{path} should have a checked_add spec"));
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 3, "{path} should have 3 ensures");
        assert!(spec.ensures[0].contains("result.is_some()"));
    }
}

#[test]
fn test_lookup_checked_sub() {
    let spec = lookup_std_spec("i32::checked_sub").unwrap();
    assert!(spec.requires.is_empty());
    assert_eq!(spec.ensures.len(), 3);
    assert!(spec.ensures[1].contains("self@ - rhs@"));
}

#[test]
fn test_lookup_checked_mul() {
    let spec = lookup_std_spec("u64::checked_mul").unwrap();
    assert!(spec.requires.is_empty());
    assert_eq!(spec.ensures.len(), 3);
    assert!(spec.ensures[1].contains("self@ * rhs@"));
}

#[test]
fn test_lookup_saturating_add() {
    let spec = lookup_std_spec("i32::saturating_add").unwrap();
    assert!(spec.requires.is_empty());
    assert_eq!(spec.ensures.len(), 3);
    // In-range: result == self + rhs
    assert!(
        spec.ensures[0].contains("self@ + rhs@"),
        "saturating_add ensures[0] should reference self@ + rhs@: {}",
        spec.ensures[0]
    );
    assert!(
        spec.ensures[0].contains("result@"),
        "saturating_add ensures[0] should reference result@: {}",
        spec.ensures[0]
    );
    // Underflow clamp to MIN
    assert!(
        spec.ensures[1].contains("Self::MIN@") || spec.ensures[1].contains("i32::MIN"),
        "saturating_add ensures[1] should clamp to MIN: {}",
        spec.ensures[1]
    );
    // Overflow clamp to MAX
    assert!(
        spec.ensures[2].contains("Self::MAX@") || spec.ensures[2].contains("i32::MAX"),
        "saturating_add ensures[2] should clamp to MAX: {}",
        spec.ensures[2]
    );
}

#[test]
fn test_lookup_saturating_sub() {
    let spec = lookup_std_spec("u8::saturating_sub").unwrap();
    assert!(spec.requires.is_empty());
    assert_eq!(spec.ensures.len(), 3);
    // In-range: result == self - rhs
    assert!(
        spec.ensures[0].contains("self@ - rhs@"),
        "saturating_sub ensures[0] should reference self@ - rhs@: {}",
        spec.ensures[0]
    );
    assert!(
        spec.ensures[0].contains("result@"),
        "saturating_sub ensures[0] should reference result@: {}",
        spec.ensures[0]
    );
    // Underflow clamp to MIN
    assert!(
        spec.ensures[1].contains("Self::MIN@") || spec.ensures[1].contains("u8::MIN"),
        "saturating_sub ensures[1] should clamp to MIN: {}",
        spec.ensures[1]
    );
    // Overflow clamp to MAX
    assert!(
        spec.ensures[2].contains("Self::MAX@") || spec.ensures[2].contains("u8::MAX"),
        "saturating_sub ensures[2] should clamp to MAX: {}",
        spec.ensures[2]
    );
}

#[test]
fn test_lookup_char_is_ascii() {
    let spec = lookup_std_spec("char::is_ascii").unwrap();
    assert!(spec.requires.is_empty());
    assert_eq!(spec.ensures.len(), 1);
    assert!(spec.ensures[0].contains("127"));
}

#[test]
fn test_lookup_char_is_ascii_digit() {
    let spec = lookup_std_spec("char::is_ascii_digit").unwrap();
    assert!(spec.requires.is_empty());
    assert_eq!(spec.ensures.len(), 1);
    // '0' = 48, '9' = 57
    assert!(spec.ensures[0].contains("48"));
    assert!(spec.ensures[0].contains("57"));
}

#[test]
fn test_lookup_char_is_ascii_alphabetic() {
    let spec = lookup_std_spec("char::is_ascii_alphabetic").unwrap();
    assert!(spec.requires.is_empty());
    assert_eq!(spec.ensures.len(), 1);
    // 'A'=65, 'Z'=90, 'a'=97, 'z'=122
    assert!(spec.ensures[0].contains("65"));
    assert!(spec.ensures[0].contains("122"));
}

// Wrapping arithmetic (#380)

#[test]
fn test_lookup_wrapping_add_all_types() {
    for path in &[
        "i8::wrapping_add",
        "i32::wrapping_add",
        "i128::wrapping_add",
        "u8::wrapping_add",
        "u32::wrapping_add",
        "usize::wrapping_add",
    ] {
        let spec = lookup_std_spec(path)
            .unwrap_or_else(|| panic!("{path} should have a wrapping_add spec"));
        assert!(spec.requires.is_empty());
        assert_eq!(
            spec.ensures.len(),
            3,
            "{path} should have 3 ensures (three-case implication encoding)"
        );
        assert!(
            spec.ensures[0].contains("self@ + rhs@"),
            "{path} ensures should contain 'self@ + rhs@'"
        );
    }
}

/// Regression test: MIR paths use `core::num::<impl i8>::wrapping_add` which
/// normalizes to `core::num::wrapping_add` (the `<impl i8>` generic is stripped).
/// Verify that all integer arithmetic ops have the normalized alias. (#967)
#[test]
fn test_lookup_normalized_mir_paths_for_integer_ops() {
    for op in &[
        "checked_add",
        "checked_sub",
        "checked_mul",
        "checked_div",
        "saturating_add",
        "saturating_sub",
        "saturating_mul",
        "saturating_div",
        "wrapping_add",
        "wrapping_sub",
        "wrapping_mul",
        "wrapping_div",
        "wrapping_neg",
        "overflowing_add",
        "overflowing_sub",
        "overflowing_mul",
        "overflowing_div",
    ] {
        // This is the normalized form of `core::num::<impl i8>::{op}`
        let normalized = format!("core::num::{op}");
        let spec = lookup_std_spec(&normalized)
            .unwrap_or_else(|| panic!("{normalized} should match (MIR normalized alias)"));

        // Semantic: every integer op spec should have at least one ensures clause
        assert!(
            !spec.ensures.is_empty(),
            "{normalized} spec should have non-empty ensures"
        );
        // Semantic: every integer op ensures should reference the operation result
        // (checked_* use `match result`, overflowing_* use `result.0@`, others use `result@`)
        assert!(
            spec.ensures[0].contains("result"),
            "{normalized} ensures[0] should reference result: {}",
            spec.ensures[0]
        );

        // Also verify that the normalize_path function produces this form
        let mir_path = format!("core::num::<impl i8>::{op}");
        assert_eq!(
            normalize_path(&mir_path),
            normalized,
            "normalize_path({mir_path}) should produce {normalized}"
        );
    }
}

#[test]
fn test_lookup_checked_neg() {
    // Checked negation — Some(-self) when no overflow, None otherwise.
    // Signed: overflow at MIN. Unsigned: overflow at any nonzero value.
    for path in &[
        "i8::checked_neg",
        "i32::checked_neg",
        "i128::checked_neg",
        "isize::checked_neg",
        "u8::checked_neg",
        "u32::checked_neg",
        "u128::checked_neg",
        "usize::checked_neg",
    ] {
        let spec = lookup_std_spec(path)
            .unwrap_or_else(|| panic!("{path} should have a checked_neg spec"));
        assert!(spec.requires.is_empty());
        assert_eq!(
            spec.ensures.len(),
            3,
            "{path} should have 3 ensures (in-range Some, in-range value, out-of-range None)"
        );
        assert!(
            spec.ensures[0].contains("0 - self@") && spec.ensures[0].contains("result.is_some()"),
            "{path} ensures[0] should map in-range to is_some via `0 - self@`: {}",
            spec.ensures[0]
        );
        assert!(
            spec.ensures[2].contains("result.is_none()"),
            "{path} ensures[2] should be the out-of-range is_none clause: {}",
            spec.ensures[2]
        );
    }
}

#[test]
fn test_lookup_checked_rem() {
    // Checked remainder — Some(self % rhs) when rhs != 0, None on rhs == 0.
    for path in &[
        "i8::checked_rem",
        "i32::checked_rem",
        "i128::checked_rem",
        "u8::checked_rem",
        "u32::checked_rem",
        "usize::checked_rem",
    ] {
        let spec = lookup_std_spec(path)
            .unwrap_or_else(|| panic!("{path} should have a checked_rem spec"));
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 3, "{path} should have 3 ensures");
        assert!(
            spec.ensures[1].contains("self@ % rhs@"),
            "{path} ensures[1] should compute `self@ % rhs@`: {}",
            spec.ensures[1]
        );
        assert!(
            spec.ensures[2].contains("rhs@ == 0") && spec.ensures[2].contains("result.is_none()"),
            "{path} ensures[2] should encode rhs == 0 => is_none: {}",
            spec.ensures[2]
        );
    }
}

#[test]
fn test_lookup_wrapping_rem() {
    // Wrapping remainder — `self % rhs` (requires rhs != 0).
    for path in &[
        "i8::wrapping_rem",
        "i32::wrapping_rem",
        "u8::wrapping_rem",
        "u32::wrapping_rem",
        "usize::wrapping_rem",
    ] {
        let spec = lookup_std_spec(path)
            .unwrap_or_else(|| panic!("{path} should have a wrapping_rem spec"));
        assert_eq!(
            spec.requires.len(),
            1,
            "{path} should require rhs@ != 0 (single precondition)"
        );
        assert!(
            spec.requires[0].contains("rhs@ != 0"),
            "{path} requires[0] should be `rhs@ != 0`: {}",
            spec.requires[0]
        );
        assert_eq!(spec.ensures.len(), 1);
        assert!(
            spec.ensures[0].contains("self@ % rhs@"),
            "{path} ensures[0] should compute `self@ % rhs@`: {}",
            spec.ensures[0]
        );
    }
}

#[test]
fn test_lookup_signum() {
    // Signed integer signum — returns -1/0/1 as Self. Only signed types
    // are registered (mirrors abs()).
    for path in &[
        "i8::signum",
        "i16::signum",
        "i32::signum",
        "i64::signum",
        "i128::signum",
        "isize::signum",
    ] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should have a signum spec"));
        assert!(spec.requires.is_empty());
        assert_eq!(
            spec.ensures.len(),
            3,
            "{path} should have 3 ensures (negative, zero, positive)"
        );
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("self@ < 0") && e.contains("result@ == 0 - 1")),
            "{path} should map self < 0 to result == -1: {spec:?}"
        );
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("self@ > 0") && e.contains("result@ == 1")),
            "{path} should map self > 0 to result == 1: {spec:?}"
        );
    }
    // Unsigned types do NOT have signum (compile error in Rust); lookup
    // should miss to avoid mis-resolving foreign symbols.
    assert!(
        lookup_std_spec("u32::signum").is_none(),
        "u32::signum should not resolve — only signed integers have signum"
    );
}

#[test]
fn test_lookup_is_positive_and_is_negative() {
    // Signed integer sign predicates. Both are total, bool-returning.
    for path in &[
        "i8::is_positive",
        "i32::is_positive",
        "i128::is_positive",
        "isize::is_positive",
    ] {
        let spec = lookup_std_spec(path)
            .unwrap_or_else(|| panic!("{path} should have an is_positive spec"));
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(
            spec.ensures[0].contains("(self@ > 0)"),
            "{path} ensures should encode `self > 0`: {}",
            spec.ensures[0]
        );
    }
    for path in &[
        "i8::is_negative",
        "i32::is_negative",
        "i128::is_negative",
        "isize::is_negative",
    ] {
        let spec = lookup_std_spec(path)
            .unwrap_or_else(|| panic!("{path} should have an is_negative spec"));
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(
            spec.ensures[0].contains("(self@ < 0)"),
            "{path} ensures should encode `self < 0`: {}",
            spec.ensures[0]
        );
    }
    // Unsigned types do NOT have is_positive/is_negative (compile error).
    assert!(
        lookup_std_spec("u32::is_positive").is_none(),
        "u32::is_positive should not resolve — only signed integers"
    );
    assert!(
        lookup_std_spec("u64::is_negative").is_none(),
        "u64::is_negative should not resolve — only signed integers"
    );
}

#[test]
fn test_lookup_abs_diff() {
    // Absolute difference — total on signed AND unsigned types.
    for path in &[
        "i8::abs_diff",
        "i32::abs_diff",
        "i128::abs_diff",
        "isize::abs_diff",
        "u8::abs_diff",
        "u32::abs_diff",
        "u128::abs_diff",
        "usize::abs_diff",
    ] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should have an abs_diff spec"));
        assert!(spec.requires.is_empty());
        assert_eq!(
            spec.ensures.len(),
            2,
            "{path} should have 2 ensures (>= and < branches)"
        );
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("self@ >= rhs@") && e.contains("self@ - rhs@")),
            "{path} should map self >= rhs to self - rhs: {spec:?}"
        );
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("self@ < rhs@") && e.contains("rhs@ - self@")),
            "{path} should map self < rhs to rhs - self: {spec:?}"
        );
    }
}

#[test]
fn test_lookup_saturating_neg() {
    // Saturating negation — only signed types. MIN saturates to MAX.
    for path in &[
        "i8::saturating_neg",
        "i32::saturating_neg",
        "i128::saturating_neg",
        "isize::saturating_neg",
    ] {
        let spec = lookup_std_spec(path)
            .unwrap_or_else(|| panic!("{path} should have a saturating_neg spec"));
        assert!(spec.requires.is_empty());
        assert_eq!(
            spec.ensures.len(),
            2,
            "{path} should have 2 ensures (MIN saturates, else 0 - self)"
        );
        assert!(
            spec.ensures.iter().any(|e| e.contains("0 - self@")),
            "{path} should reference `0 - self@`: {spec:?}"
        );
    }
    // Unsigned types do NOT have saturating_neg in the stable API.
    assert!(
        lookup_std_spec("u32::saturating_neg").is_none(),
        "u32::saturating_neg should not resolve — only signed integers"
    );
}

#[test]
fn test_lookup_wrapping_abs() {
    // Wrapping absolute value — only signed types. MIN wraps to MIN.
    for path in &[
        "i8::wrapping_abs",
        "i32::wrapping_abs",
        "i128::wrapping_abs",
        "isize::wrapping_abs",
    ] {
        let spec = lookup_std_spec(path)
            .unwrap_or_else(|| panic!("{path} should have a wrapping_abs spec"));
        assert!(spec.requires.is_empty());
        assert_eq!(
            spec.ensures.len(),
            3,
            "{path} should have 3 ensures (MIN -> MIN, nonneg, neg)"
        );
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("self@ >= 0") && e.contains("result@ == self@")),
            "{path} should map nonneg self to self: {spec:?}"
        );
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("self@ < 0") && e.contains("0 - self@")),
            "{path} should map negative self to 0 - self: {spec:?}"
        );
    }
    // Unsigned types do NOT have wrapping_abs.
    assert!(
        lookup_std_spec("u32::wrapping_abs").is_none(),
        "u32::wrapping_abs should not resolve — only signed integers"
    );
}

#[test]
fn test_lookup_count_ones() {
    // Bit-population count — defined on every primitive integer type.
    for path in &[
        "i8::count_ones",
        "i32::count_ones",
        "i128::count_ones",
        "isize::count_ones",
        "u8::count_ones",
        "u32::count_ones",
        "u128::count_ones",
        "usize::count_ones",
    ] {
        let spec =
            lookup_std_spec(path).unwrap_or_else(|| panic!("{path} should have a count_ones spec"));
        assert!(spec.requires.is_empty());
        assert_eq!(
            spec.ensures.len(),
            2,
            "{path} should have 2 ensures (nonneg + zero-case)"
        );
        assert!(
            spec.ensures.iter().any(|e| e.contains("result@ >= 0")),
            "{path} should ensure result@ >= 0: {spec:?}"
        );
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("self@ == 0") && e.contains("result@ == 0")),
            "{path} should map self == 0 to result == 0: {spec:?}"
        );
    }
}

#[test]
fn test_lookup_count_zeros() {
    // Bit-zero count — defined on every primitive integer type.
    for path in &[
        "i8::count_zeros",
        "i32::count_zeros",
        "i128::count_zeros",
        "isize::count_zeros",
        "u8::count_zeros",
        "u32::count_zeros",
        "u128::count_zeros",
        "usize::count_zeros",
    ] {
        let spec = lookup_std_spec(path)
            .unwrap_or_else(|| panic!("{path} should have a count_zeros spec"));
        assert!(spec.requires.is_empty());
        assert_eq!(
            spec.ensures.len(),
            2,
            "{path} should have 2 ensures (nonneg + zero-case)"
        );
        assert!(
            spec.ensures.iter().any(|e| e.contains("result@ >= 0")),
            "{path} should ensure result@ >= 0: {spec:?}"
        );
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("self@ == 0") && e.contains("result@ > 0")),
            "{path} should map self == 0 to result > 0: {spec:?}"
        );
    }
}

#[test]
fn test_lookup_next_power_of_two() {
    // Smallest power of two >= self — only unsigned integer types.
    for path in &[
        "u8::next_power_of_two",
        "u16::next_power_of_two",
        "u32::next_power_of_two",
        "u64::next_power_of_two",
        "u128::next_power_of_two",
        "usize::next_power_of_two",
    ] {
        let spec = lookup_std_spec(path)
            .unwrap_or_else(|| panic!("{path} should have a next_power_of_two spec"));
        assert_eq!(spec.requires.len(), 1, "{path} owes its overflow panic");
        assert!(
            !spec.requires[0].contains("Self::MAX"),
            "{path}: Self::MAX must be resolved to the receiver type: {:?}",
            spec.requires
        );
        assert_eq!(
            spec.ensures.len(),
            3,
            "{path} should have 3 ensures (>= 1, >= self, <=1 case)"
        );
        assert!(
            spec.ensures.iter().any(|e| e.contains("result@ >= 1")),
            "{path} should ensure result@ >= 1: {spec:?}"
        );
        assert!(
            spec.ensures.iter().any(|e| e.contains("result@ >= self@")),
            "{path} should ensure result@ >= self@: {spec:?}"
        );
        assert!(
            spec.ensures
                .iter()
                .any(|e| e.contains("self@ <= 1") && e.contains("result@ == 1")),
            "{path} should map self <= 1 to result == 1: {spec:?}"
        );
    }
    // Signed types do NOT have next_power_of_two in the stable API.
    assert!(
        lookup_std_spec("i32::next_power_of_two").is_none(),
        "i32::next_power_of_two should not resolve — only unsigned integers"
    );
}

#[test]
fn test_lookup_wrapping_neg() {
    // Wrapping negation — unary op used by rightmostbit.rs (#2674)
    for path in &[
        "i8::wrapping_neg",
        "i32::wrapping_neg",
        "u8::wrapping_neg",
        "u32::wrapping_neg",
        "usize::wrapping_neg",
    ] {
        let spec = lookup_std_spec(path)
            .unwrap_or_else(|| panic!("{path} should have a wrapping_neg spec"));
        assert!(spec.requires.is_empty());
        assert_eq!(
            spec.ensures.len(),
            3,
            "{path} should have 3 ensures (three-case wrapping encoding)"
        );
        assert!(
            spec.ensures[0].contains("0 - self@"),
            "{path} ensures[0] should reference '0 - self@': {}",
            spec.ensures[0]
        );
    }
}

#[test]
fn test_lookup_wrapping_sub() {
    let spec = lookup_std_spec("i32::wrapping_sub").unwrap();
    assert!(spec.requires.is_empty());
    assert_eq!(spec.ensures.len(), 3);
    assert!(spec.ensures[0].contains("self@ - rhs@"));
}

#[test]
fn test_lookup_wrapping_mul() {
    let spec = lookup_std_spec("u64::wrapping_mul").unwrap();
    assert!(spec.requires.is_empty());
    assert_eq!(spec.ensures.len(), 1);
    assert!(spec.ensures[0].contains("self@ * rhs@"));
    // The reduction is EUCLIDEAN and must be spelled explicitly: pearlite `%`
    // truncates (Creusot `int.ComputerDivision.mod`) and would be wrong for a
    // negative `self * rhs - MIN`.
    assert!(spec.ensures[0].contains(".rem_euclid("));
    assert!(!spec.ensures[0].contains('%'));
}

// Self::MIN/Self::MAX resolution at lookup time (#967)

#[test]
fn test_lookup_resolves_self_min_max_to_qualified() {
    let spec = lookup_std_spec("u8::wrapping_add").unwrap();
    assert_eq!(spec.ensures.len(), 3);
    // Self::MIN should be resolved to u8::MIN at lookup time.
    // The three-case encoding references MIN@ and MAX@ in all clauses.
    let all_ensures = spec.ensures.join(" ");
    assert!(
        all_ensures.contains("u8::MIN"),
        "Self::MIN should be resolved to u8::MIN, got: {}",
        all_ensures
    );
    assert!(
        all_ensures.contains("u8::MAX"),
        "Self::MAX should be resolved to u8::MAX, got: {}",
        all_ensures
    );
    assert!(
        !all_ensures.contains("Self::MIN"),
        "Self::MIN should not remain unresolved: {}",
        all_ensures
    );

    // Signed type: i32
    let spec_i32 = lookup_std_spec("i32::wrapping_add").unwrap();
    let all_ensures_i32 = spec_i32.ensures.join(" ");
    assert!(
        all_ensures_i32.contains("i32::MIN"),
        "Self::MIN should be resolved to i32::MIN, got: {}",
        all_ensures_i32
    );
}

#[test]
fn test_resolve_self_type_constants_non_integer_unchanged() {
    // Non-integer lookups should not be affected by Self:: constant resolution
    let spec =
        lookup_std_spec("core::option::Option::unwrap").expect("Option::unwrap should exist");
    assert!(
        !spec
            .ensures
            .iter()
            .any(|e| e.contains("::MIN") || e.contains("::MAX")),
        "Non-integer spec should not have MIN/MAX constants: {:?}",
        spec.ensures
    );
}
#[test]
fn test_lookup_ptr_addr() {
    let spec = lookup_std_spec("<*const T>::addr").expect("ptr::addr spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "self.addr_logic()", "ptr::addr");
}

#[test]
fn test_lookup_ptr_is_null() {
    let spec = lookup_std_spec("<*const T>::is_null").expect("ptr::is_null spec should exist");
    assert!(spec.requires.is_empty());
    assert_ensures_contains(&spec, "self.is_null_logic()", "ptr::is_null");
}
