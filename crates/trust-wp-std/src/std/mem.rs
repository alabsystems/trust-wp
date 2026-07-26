// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Specification-level memory layout functions.
//!
//! These are logic functions that provide compile-time type layout information
//! for use in specifications.
//!
//! Source: Creusot `creusot-std/src/std/mem.rs`

use crate::logic::Int;

/// Returns the size of type `T` in bytes as a logical `Int`.
///
/// This is the specification-level counterpart to `std::mem::size_of::<T>()`.
pub fn size_of_logic<T>() -> Int {
    Int::from(std::mem::size_of::<T>() as i128)
}

/// Returns the alignment of type `T` in bytes as a logical `Int`.
///
/// This is the specification-level counterpart to `std::mem::align_of::<T>()`.
pub fn align_of_logic<T>() -> Int {
    Int::from(std::mem::align_of::<T>() as i128)
}

/// Internal specification definitions used by the driver's hardcoded fallback
/// tables and local tests. Builtin registry loading happens separately.
#[doc(hidden)]
pub mod specs {
    /// Contract for `mem::replace`
    ///
    /// Replaces the value at `dest` with `src`, returning the old value.
    pub const REPLACE: &str = r"
        params: dest, src
        ensures: result == old(*dest)
        ensures: (^dest) == src
    ";

    /// Contract for `mem::swap`
    ///
    /// Swaps the values at two mutable references.
    pub const SWAP: &str = r"
        params: x, y
        ensures: (^x) == old(*y)
        ensures: (^y) == old(*x)
    ";

    /// Contract for `mem::take`
    ///
    /// Takes the value from `dest`, replacing with `Default::default()`.
    /// The `Default::default()` postcondition encodes the T: Default bound:
    /// after take, the destination holds the default value for type T.
    ///
    /// At the encoder level, `Default::default()` is currently an uninterpreted
    /// function (unconstrained constant) — the solver knows `^dest` equals a
    /// fixed value but not which value. Full type-aware resolution (mapping
    /// `Default::default()` to 0/false/None per concrete T) requires type-
    /// parametric spec application in the driver. (#2169)
    pub const TAKE: &str = r"
        params: dest
        ensures: result == old(*dest)
        ensures: (^dest) == Default::default()
    ";
}

#[cfg(test)]
mod tests {
    #[test]
    fn test_replace_spec_format() {
        let spec = super::specs::REPLACE;
        assert!(spec.contains("ensures:"), "REPLACE should have ensures");
        assert!(
            spec.contains("result == old(*dest)"),
            "REPLACE should return old value"
        );
        assert!(
            spec.contains("(^dest) == src"),
            "REPLACE should set dest to src"
        );
    }

    #[test]
    fn test_swap_spec_format() {
        let spec = super::specs::SWAP;
        assert!(
            spec.contains("(^x) == old(*y)"),
            "SWAP should set x to old y"
        );
        assert!(
            spec.contains("(^y) == old(*x)"),
            "SWAP should set y to old x"
        );
    }

    #[test]
    fn test_take_spec_format() {
        let spec = super::specs::TAKE;
        assert!(
            spec.contains("result == old(*dest)"),
            "TAKE should return old value"
        );
        assert!(
            spec.contains("(^dest) == Default::default()"),
            "TAKE should set dest to Default::default()"
        );
    }
}
