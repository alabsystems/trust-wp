// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `Default` derive surface and shared contract snippets.

pub use crate::Default;

#[doc(hidden)]
pub mod specs {
    /// Numeric primitive `Default::default()` contract.
    ///
    /// `params:` is empty because `default()` takes no arguments. This
    /// suppresses "no parameter names" warnings from cross-crate MIR lookup.
    pub const ZERO: &str = r"
        params:
        ensures: result == 0
        ensures: core::default::Default::default.postcondition((), result)
    ";

    /// `bool::default()` contract.
    pub const FALSE: &str = r"
        params:
        ensures: result == false
        ensures: core::default::Default::default.postcondition((), result)
    ";

    /// Generic `Default::default()` fallback contract.
    ///
    /// This does not commit to a concrete value. It only records the
    /// postcondition predicate so callers can thread field-wise default facts
    /// through constructors, matching the Creusot derive pattern.
    pub const POSTCONDITION_ONLY: &str = r"
        params:
        ensures: core::default::Default::default.postcondition((), result)
    ";

    /// `Vec::default()` contract — equivalent to `Vec::new()`.
    ///
    /// Instantiates the generic Default postcondition to the concrete
    /// `result@.len() == 0` fact so the solver sees a usable clause
    /// instead of an uninterpreted predicate. (#2256)
    pub const VEC_EMPTY: &str = r"
        params:
        ensures: result@.len() == 0
        ensures: core::default::Default::default.postcondition((), result)
    ";

    /// `String::default()` contract — equivalent to `String::new()`.
    pub const STRING_EMPTY: &str = r"
        params:
        ensures: result@.len() == 0
        ensures: core::default::Default::default.postcondition((), result)
    ";

    /// `Option::default()` contract — returns `None`.
    pub const OPTION_NONE: &str = r"
        params:
        ensures: result == None()
        ensures: core::default::Default::default.postcondition((), result)
    ";

    /// `HashMap::default()` contract — equivalent to `HashMap::new()`.
    pub const HASHMAP_EMPTY: &str = r"
        params:
        ensures: result@.len() == 0
        ensures: core::default::Default::default.postcondition((), result)
    ";

    /// `HashSet::default()` contract — equivalent to `HashSet::new()`.
    pub const HASHSET_EMPTY: &str = r"
        params:
        ensures: result@.len() == 0
        ensures: core::default::Default::default.postcondition((), result)
    ";

    /// `BTreeMap::default()` contract — equivalent to `BTreeMap::new()`.
    pub const BTREEMAP_EMPTY: &str = r"
        params:
        ensures: result@.len() == 0
        ensures: core::default::Default::default.postcondition((), result)
    ";

    /// `BTreeSet::default()` contract — equivalent to `BTreeSet::new()`.
    pub const BTREESET_EMPTY: &str = r"
        params:
        ensures: result@.len() == 0
        ensures: core::default::Default::default.postcondition((), result)
    ";

    /// `VecDeque::default()` contract — equivalent to `VecDeque::new()`.
    pub const VECDEQUE_EMPTY: &str = r"
        params:
        ensures: result@.len() == 0
        ensures: core::default::Default::default.postcondition((), result)
    ";

    /// `char::default()` contract — default char is '\0'.
    pub const CHAR_NUL: &str = r"
        params:
        ensures: core::default::Default::default.postcondition((), result)
    ";
}

#[cfg(test)]
mod tests {
    use super::super::test_shim;

    #[test]
    fn test_default_zero_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::ZERO);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
        assert!(spec
            .ensures
            .iter()
            .any(|clause| clause.contains("result == 0")));
        assert!(spec
            .ensures
            .iter()
            .any(|clause| clause.contains("Default::default.postcondition")));
    }

    #[test]
    fn test_default_false_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::FALSE);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
        assert!(spec
            .ensures
            .iter()
            .any(|clause| clause.contains("result == false")));
        assert!(spec
            .ensures
            .iter()
            .any(|clause| clause.contains("Default::default.postcondition")));
    }

    #[test]
    fn test_default_postcondition_only_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::POSTCONDITION_ONLY);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert_eq!(
            spec.ensures[0],
            "core::default::Default::default.postcondition((), result)"
        );
    }

    #[test]
    fn test_default_vec_empty_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::VEC_EMPTY);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
        assert!(spec
            .ensures
            .iter()
            .any(|clause| clause.contains("result@.len() == 0")));
        assert!(spec
            .ensures
            .iter()
            .any(|clause| clause.contains("Default::default.postcondition")));
    }

    #[test]
    fn test_default_string_empty_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::STRING_EMPTY);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
        assert!(spec
            .ensures
            .iter()
            .any(|clause| clause.contains("result@.len() == 0")));
        assert!(spec
            .ensures
            .iter()
            .any(|clause| clause.contains("Default::default.postcondition")));
    }

    #[test]
    fn test_default_option_none_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::OPTION_NONE);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
        assert!(spec
            .ensures
            .iter()
            .any(|clause| clause.contains("result == None()")));
        assert!(spec
            .ensures
            .iter()
            .any(|clause| clause.contains("Default::default.postcondition")));
    }

    #[test]
    fn test_default_hashmap_empty_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::HASHMAP_EMPTY);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
        assert!(spec
            .ensures
            .iter()
            .any(|clause| clause.contains("result@.len() == 0")));
        assert!(spec
            .ensures
            .iter()
            .any(|clause| clause.contains("Default::default.postcondition")));
    }

    #[test]
    fn test_default_hashset_empty_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::HASHSET_EMPTY);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
        assert!(spec
            .ensures
            .iter()
            .any(|clause| clause.contains("result@.len() == 0")));
        assert!(spec
            .ensures
            .iter()
            .any(|clause| clause.contains("Default::default.postcondition")));
    }

    #[test]
    fn test_default_btreemap_empty_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::BTREEMAP_EMPTY);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
        assert!(spec
            .ensures
            .iter()
            .any(|clause| clause.contains("result@.len() == 0")));
        assert!(spec
            .ensures
            .iter()
            .any(|clause| clause.contains("Default::default.postcondition")));
    }

    #[test]
    fn test_default_btreeset_empty_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::BTREESET_EMPTY);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
        assert!(spec
            .ensures
            .iter()
            .any(|clause| clause.contains("result@.len() == 0")));
        assert!(spec
            .ensures
            .iter()
            .any(|clause| clause.contains("Default::default.postcondition")));
    }

    #[test]
    fn test_default_vecdeque_empty_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::VECDEQUE_EMPTY);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 2);
        assert!(spec
            .ensures
            .iter()
            .any(|clause| clause.contains("result@.len() == 0")));
        assert!(spec
            .ensures
            .iter()
            .any(|clause| clause.contains("Default::default.postcondition")));
    }

    #[test]
    fn test_default_char_nul_spec_parses() {
        let spec = test_shim::parse_spec_string(super::specs::CHAR_NUL);
        assert!(spec.requires.is_empty());
        assert_eq!(spec.ensures.len(), 1);
        assert!(spec
            .ensures
            .iter()
            .any(|clause| clause.contains("Default::default.postcondition")));
    }
}
