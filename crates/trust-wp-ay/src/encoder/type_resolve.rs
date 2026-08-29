// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Type constant resolution and solver panic isolation.
//!
//! This module provides:
//! - Resolution of qualified integer constants (`u32::MAX`, `i32::MIN`, etc.)
//! - Generation of type constant maps for integer types (`Self::MIN`/`Self::MAX`)
//! - Panic-safe wrappers for ay solver operations

use std::{collections::HashMap, panic::AssertUnwindSafe};

use tracing::debug;
use trust_wp_core::formula::{
    int_bounds::{signed_bounds_expr, unsigned_max_expr},
    PureExpr,
};

use super::unsoundness;

/// Resolve a qualified integer constant name to its exact symbolic value.
///
/// Handles `u32::MAX`, `i32::MIN`, etc. — the qualified forms that appear
/// directly in user contracts (as opposed to `Self::MIN`/`Self::MAX` which
/// are resolved via the `type_constants` map set by the driver).
///
/// Returns exact `PureExpr` values for all Rust integer bounds, including
/// types wider than 64 bits. For `u64::MAX`, `u128::MAX`, etc., the returned
/// expression is a symbolic arithmetic tree (e.g., `2^64 - 1`) that the
/// encoder can evaluate exactly in SMT's unbounded Int sort.
pub(crate) fn resolve_qualified_int_constant(name: &str) -> Option<PureExpr> {
    match name {
        "i8::MIN" => Some(PureExpr::Int(i64::from(i8::MIN))),
        "i8::MAX" => Some(PureExpr::Int(i64::from(i8::MAX))),
        "i16::MIN" => Some(PureExpr::Int(i64::from(i16::MIN))),
        "i16::MAX" => Some(PureExpr::Int(i64::from(i16::MAX))),
        "i32::MIN" => Some(PureExpr::Int(i64::from(i32::MIN))),
        "i32::MAX" => Some(PureExpr::Int(i64::from(i32::MAX))),
        "i64::MIN" => Some(PureExpr::Int(i64::MIN)),
        "i64::MAX" => Some(PureExpr::Int(i64::MAX)),
        "isize::MIN" => Some(PureExpr::Int(i64::MIN)),
        "isize::MAX" => Some(PureExpr::Int(i64::MAX)),
        // Exact symbolic bounds for types wider than i64.
        "i128::MIN" => {
            let (min, _) = signed_bounds_expr(128);
            Some(min)
        }
        "i128::MAX" => {
            let (_, max) = signed_bounds_expr(128);
            Some(max)
        }
        "u64::MAX" => Some(unsigned_max_expr(64)),
        "usize::MAX" => Some(unsigned_max_expr(64)), // assume 64-bit
        "u128::MAX" => Some(unsigned_max_expr(128)),
        "u8::MIN" | "u16::MIN" | "u32::MIN" | "u64::MIN" | "u128::MIN" | "usize::MIN" => {
            Some(PureExpr::Int(0))
        }
        "u8::MAX" => Some(PureExpr::Int(i64::from(u8::MAX))),
        "u16::MAX" => Some(PureExpr::Int(i64::from(u16::MAX))),
        "u32::MAX" => Some(PureExpr::Int(i64::from(u32::MAX))),
        _ => None,
    }
}

/// Generate type constants map for a given Rust integer type name.
///
/// Returns a map with `Self::MIN` and `Self::MAX` entries for the named
/// integer type as exact `PureExpr` values. The driver calls this when
/// injecting specs for integer methods like `i32::checked_add`. (#688)
///
/// For types wider than 64 bits (`u64`, `u128`, `usize`, `i128`), the
/// returned expressions use symbolic arithmetic (e.g., `2^64 - 1`) instead
/// of truncating to `i64::MAX`.
///
/// Returns `None` if the type name is not a recognized integer type.
///
/// # Examples
/// ```text
/// type_constants_for_int("i32") => {"Self::MIN" => Int(-2147483648), "Self::MAX" => Int(2147483647)}
/// type_constants_for_int("u8") => {"Self::MIN" => Int(0), "Self::MAX" => Int(255)}
/// type_constants_for_int("u64") => {"Self::MIN" => Int(0), "Self::MAX" => BinOp(pow2(64), Sub, Int(1))}
/// type_constants_for_int("String") => None
/// ```
pub fn type_constants_for_int(type_name: &str) -> Option<HashMap<String, PureExpr>> {
    let (min, max) = match type_name {
        "i8" => (
            PureExpr::Int(i64::from(i8::MIN)),
            PureExpr::Int(i64::from(i8::MAX)),
        ),
        "i16" => (
            PureExpr::Int(i64::from(i16::MIN)),
            PureExpr::Int(i64::from(i16::MAX)),
        ),
        "i32" => (
            PureExpr::Int(i64::from(i32::MIN)),
            PureExpr::Int(i64::from(i32::MAX)),
        ),
        "i64" => (PureExpr::Int(i64::MIN), PureExpr::Int(i64::MAX)),
        "i128" => signed_bounds_expr(128),
        "isize" => (PureExpr::Int(i64::MIN), PureExpr::Int(i64::MAX)),
        "u8" => (PureExpr::Int(0), PureExpr::Int(i64::from(u8::MAX))),
        "u16" => (PureExpr::Int(0), PureExpr::Int(i64::from(u16::MAX))),
        "u32" => (PureExpr::Int(0), PureExpr::Int(i64::from(u32::MAX))),
        "u64" => (PureExpr::Int(0), unsigned_max_expr(64)),
        "u128" => (PureExpr::Int(0), unsigned_max_expr(128)),
        "usize" => (PureExpr::Int(0), unsigned_max_expr(64)),
        _ => return None,
    };
    let mut map = HashMap::new();
    map.insert("Self::MIN".to_string(), min);
    map.insert("Self::MAX".to_string(), max);
    Some(map)
}

/// Run a solver operation with ay panic isolation.
///
/// ay APIs can panic on internal assertion failures. This wrapper keeps the
/// verification pipeline alive by converting ay panics into
/// [`SolverPanicError`] while re-raising unrelated programmer bugs. Callers
/// decide how to handle the error — there is no implicit fallback value.
/// (#903, #1663)
pub(super) fn catch_solver_panic_with_reason<T, F>(
    operation: &str,
    op: F,
) -> Result<T, crate::error::SolverPanicError>
where
    F: FnOnce() -> T,
{
    crate::verify::catch_ay_panics_tightened(AssertUnwindSafe(|| Ok(op())), |reason| {
        unsoundness::increment(unsoundness::UnsoundnessCategory::CatchUnwindFallback);
        debug!("ay solver panic during {operation}: {reason}");
        Err(crate::error::SolverPanicError::Panic {
            operation: operation.to_string(),
            reason,
        })
    })
}

#[cfg(test)]
mod catch_unwind_tests;
#[cfg(test)]
mod type_constants_tests;

#[cfg(test)]
mod tests {
    use ntest::timeout;
    use trust_wp_core::formula::PureExpr;

    use super::*;

    // ── resolve_qualified_int_constant edge cases ─────────────────────────

    #[test]
    #[timeout(5000)]
    fn test_resolve_all_signed_types_have_min_and_max() {
        for ty in &["i8", "i16", "i32", "i64", "i128", "isize"] {
            let min_key = format!("{ty}::MIN");
            let max_key = format!("{ty}::MAX");
            assert!(
                resolve_qualified_int_constant(&min_key).is_some(),
                "{min_key} should resolve to a value"
            );
            assert!(
                resolve_qualified_int_constant(&max_key).is_some(),
                "{max_key} should resolve to a value"
            );
        }
    }

    #[test]
    #[timeout(5000)]
    fn test_resolve_all_unsigned_types_have_min_and_max() {
        for ty in &["u8", "u16", "u32", "u64", "u128", "usize"] {
            let min_key = format!("{ty}::MIN");
            let max_key = format!("{ty}::MAX");
            let min_val = resolve_qualified_int_constant(&min_key);
            assert!(min_val.is_some(), "{min_key} should resolve");
            assert_eq!(min_val, Some(PureExpr::Int(0)), "{min_key} should be 0");
            assert!(
                resolve_qualified_int_constant(&max_key).is_some(),
                "{max_key} should resolve"
            );
        }
    }

    #[test]
    #[timeout(5000)]
    fn test_resolve_signed_min_less_than_max() {
        // For i8 through i64, MIN and MAX are both PureExpr::Int so we can compare directly.
        for (ty, min_val, max_val) in &[
            ("i8", i64::from(i8::MIN), i64::from(i8::MAX)),
            ("i16", i64::from(i16::MIN), i64::from(i16::MAX)),
            ("i32", i64::from(i32::MIN), i64::from(i32::MAX)),
            ("i64", i64::MIN, i64::MAX),
        ] {
            let min = resolve_qualified_int_constant(&format!("{ty}::MIN"));
            let max = resolve_qualified_int_constant(&format!("{ty}::MAX"));
            assert_eq!(min, Some(PureExpr::Int(*min_val)), "{ty}::MIN value");
            assert_eq!(max, Some(PureExpr::Int(*max_val)), "{ty}::MAX value");
            assert!(
                min_val < max_val,
                "{ty}::MIN ({min_val}) should be less than {ty}::MAX ({max_val})"
            );
        }
    }

    // ── type_constants_for_int consistency ────────────────────────────────

    #[test]
    #[timeout(5000)]
    fn test_type_constants_all_int_types_present() {
        let all_types = [
            "i8", "i16", "i32", "i64", "i128", "isize", "u8", "u16", "u32", "u64", "u128", "usize",
        ];
        for ty in &all_types {
            let map = type_constants_for_int(ty);
            assert!(
                map.is_some(),
                "type_constants_for_int(\"{ty}\") should return Some"
            );
            let map = map.unwrap();
            assert!(
                map.contains_key("Self::MIN"),
                "{ty} map should contain Self::MIN"
            );
            assert!(
                map.contains_key("Self::MAX"),
                "{ty} map should contain Self::MAX"
            );
        }
    }

    #[test]
    #[timeout(5000)]
    fn test_type_constants_non_integer_returns_none() {
        for ty in &["String", "bool", "Vec", "f32", "f64", "char", ""] {
            assert!(
                type_constants_for_int(ty).is_none(),
                "type_constants_for_int(\"{ty}\") should return None"
            );
        }
    }

    #[test]
    #[timeout(5000)]
    fn test_type_constants_consistent_with_resolve_qualified() {
        // For types that both functions cover, the values must agree.
        for ty in &["i8", "i16", "i32", "i64", "u8", "u16", "u32"] {
            let map = type_constants_for_int(ty).unwrap();
            let min_key = format!("{ty}::MIN");
            let max_key = format!("{ty}::MAX");
            assert_eq!(
                resolve_qualified_int_constant(&min_key),
                Some(map["Self::MIN"].clone()),
                "{min_key} must match type_constants_for_int(\"{ty}\")[\"Self::MIN\"]"
            );
            assert_eq!(
                resolve_qualified_int_constant(&max_key),
                Some(map["Self::MAX"].clone()),
                "{max_key} must match type_constants_for_int(\"{ty}\")[\"Self::MAX\"]"
            );
        }
    }

    #[test]
    #[timeout(5000)]
    fn test_type_constants_map_has_exactly_two_entries() {
        for ty in &["i32", "u64", "i128"] {
            let map = type_constants_for_int(ty).unwrap();
            assert_eq!(
                map.len(),
                2,
                "type_constants_for_int(\"{ty}\") should return exactly 2 entries (Self::MIN, Self::MAX)"
            );
        }
    }
}
