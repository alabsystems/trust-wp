// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Re-export of `std::clone` for Creusot compatibility and generic Clone spec.
//!
//! Creusot tests import `creusot_std::std::clone::Clone`. This module
//! re-exports the standard library's `Clone` trait so those imports resolve.
//!
//! The `specs` submodule provides the generic `Clone::clone` postcondition
//! fallback for non-primitive types, plus the Creusot-compatible equality law
//! used by callers that reason through `T::clone.postcondition`.

pub use std::clone::Clone;

#[doc(hidden)]
pub mod specs {
    /// Generic `Clone::clone()` fallback contract.
    ///
    /// This does not rewrite the extracted result to `*self`. It records the
    /// `T::clone.postcondition` predicate and a ground equality law guarded by
    /// that predicate, so callers can keep the synthesized `call_N` result
    /// while still proving structural equalities from clone facts.
    ///
    /// Uses `T::clone` (not `core::clone::Clone::clone`) as the receiver path
    /// to match Creusot contract syntax: `T::clone.postcondition((s,), r)`.
    pub const POSTCONDITION_ONLY: &str = r"
        params: self
        ensures: T::clone.postcondition((self,), result)
        ensures: T::clone.postcondition((self,), result) ==> result == *self
    ";
}

#[cfg(test)]
mod tests {
    use super::super::test_shim;

    #[test]
    fn test_clone_postcondition_only_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::POSTCONDITION_ONLY);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
        assert_eq!(spec.ensures[0], "T::clone.postcondition((self,), result)");
        assert_eq!(
            spec.ensures[1],
            "T::clone.postcondition((self,), result) ==> result == *self"
        );
    }
}
