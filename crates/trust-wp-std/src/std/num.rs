// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Stable helper traits for integer primitives and NonZero type specifications.
//!
//! Reference: Creusot `creusot-std/src/std/num.rs`

// Allow raw string hashes for spec string literals (consistency over optimization)
#![allow(clippy::needless_raw_string_hashes)]

/// Extra methods for machine integers.
pub trait NumExt {
    fn leading_zeros_logic(self) -> u32;
    fn trailing_zeros_logic(self) -> u32;
    fn leading_ones_logic(self) -> u32;
    fn trailing_ones_logic(self) -> u32;
}

macro_rules! impl_num_ext {
    ($($ty:ty),* $(,)?) => {
        $(
            impl NumExt for $ty {
                fn leading_zeros_logic(self) -> u32 {
                    self.leading_zeros()
                }

                fn trailing_zeros_logic(self) -> u32 {
                    self.trailing_zeros()
                }

                fn leading_ones_logic(self) -> u32 {
                    self.leading_ones()
                }

                fn trailing_ones_logic(self) -> u32 {
                    self.trailing_ones()
                }
            }
        )*
    };
}

impl_num_ext!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);

/// Specification constants for `NonZero{U,I}{8,16,32,64,128,size}` methods.
///
/// NonZero types are newtypes wrapping an integer with the invariant that
/// the inner value is not zero. In MIR, these appear as:
/// - `core::num::NonZero<u32>::new` (Rust 1.79+)
/// - `core::num::NonZeroU32::new` (legacy type aliases)
/// - `std::num::NonZeroU32::new` (re-export)
///
/// # Methods covered
///
/// ## `new(value) -> Option<Self>`
/// Returns `Some(NonZero(value))` if `value != 0`, `None` otherwise.
/// The `@` (view/deep_model) of the result unwraps to the inner integer.
///
/// ## `get(self) -> integer`
/// Returns the inner non-zero value. The result is guaranteed != 0.
///
/// # Part of #2669
#[doc(hidden)]
pub mod specs {
    // ── NonZero::new ────────────────────────────────────────────
    //
    // `NonZero<T>::new(value: T) -> Option<NonZero<T>>`
    //
    // The spec uses `value@` (view operator) because the driver extracts
    // parameter values through the view/deep_model layer for integer types.
    // When value@ != 0, the result is Some and the inner value equals value@.
    // When value@ == 0, the result is None.
    //
    // All NonZero types share the same spec because the @ operator
    // normalizes to unbounded Int at the SMT level.

    /// Contract for `NonZero{U,I}{8..128,size}::new`
    ///
    /// Returns `Some(v)` where `v@ == value@` when value is non-zero,
    /// `None` when value is zero.
    pub const NONZERO_NEW: &str = r#"
        params: value
        ensures: value@ != 0 ==> result.is_some()
        ensures: value@ != 0 ==> result.unwrap()@ == value@
        ensures: value@ == 0 ==> result.is_none()
    "#;

    // ── NonZero::get ────────────────────────────────────────────
    //
    // `NonZero<T>::get(self) -> T`
    //
    // The inner value is guaranteed non-zero by the type invariant.
    // result@ == self@ (identity through the newtype wrapper) and
    // result@ != 0 (the NonZero guarantee).

    /// Contract for `NonZero{U,I}{8..128,size}::get`
    ///
    /// Returns the inner value which is guaranteed non-zero.
    pub const NONZERO_GET: &str = r#"
        ensures: result@ == self@
        ensures: result@ != 0
    "#;

    // ── NonZero::new_unchecked ──────────────────────────────────
    //
    // `unsafe NonZero<T>::new_unchecked(value: T) -> NonZero<T>`
    //
    // Caller promises value != 0. Models the safety precondition.

    /// Contract for `NonZero{U,I}{8..128,size}::new_unchecked`
    ///
    /// Unsafe: caller must ensure `value != 0`.
    pub const NONZERO_NEW_UNCHECKED: &str = r#"
        params: value
        requires: value@ != 0
        ensures: result@ == value@
    "#;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_unsigned_num_ext() {
        let value = 0b0011_0000_u8;
        assert_eq!(value.leading_zeros_logic(), value.leading_zeros());
        assert_eq!(value.trailing_zeros_logic(), value.trailing_zeros());
        assert_eq!(value.leading_ones_logic(), value.leading_ones());
        assert_eq!(value.trailing_ones_logic(), value.trailing_ones());
    }

    #[test]
    fn test_signed_num_ext() {
        let value = -2_i8;
        assert_eq!(value.leading_zeros_logic(), value.leading_zeros());
        assert_eq!(value.trailing_zeros_logic(), value.trailing_zeros());
        assert_eq!(value.leading_ones_logic(), value.leading_ones());
        assert_eq!(value.trailing_ones_logic(), value.trailing_ones());
    }

    // ── NonZero spec parsing tests ─────────────────────────────────

    #[test]
    fn test_nonzero_new_spec_parses() {
        let spec = super::super::test_shim::parse_spec_string(super::specs::NONZERO_NEW);
        assert!(spec.requires.is_empty(), "new() has no preconditions");
        assert_eq!(spec.ensures.len(), 3, "new() should have 3 ensures clauses");
    }

    #[test]
    fn test_nonzero_get_spec_parses() {
        let spec = super::super::test_shim::parse_spec_string(super::specs::NONZERO_GET);
        assert!(spec.requires.is_empty(), "get() has no preconditions");
        assert_eq!(spec.ensures.len(), 2, "get() should have 2 ensures clauses");
    }

    #[test]
    fn test_nonzero_new_unchecked_spec_parses() {
        let spec = super::super::test_shim::parse_spec_string(super::specs::NONZERO_NEW_UNCHECKED);
        assert_eq!(spec.requires.len(), 1, "new_unchecked() has 1 precondition");
        assert_eq!(
            spec.ensures.len(),
            1,
            "new_unchecked() should have 1 ensures clause"
        );
    }
}
