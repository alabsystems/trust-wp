// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Workspace-internal helper APIs for formula lowering.
//!
//! These modules are intentionally exposed so `trust-wp-driver` and `trust-wp-ay`
//! can share encoding conventions with `trust-wp-core`, but they are not part of
//! the stable semantic AST API. External users should prefer
//! `trust_wp_core::formula::{Formula, PureExpr, Pattern, ...}` and treat
//! `formula::internal::*` as unstable implementation detail.

/// Synthetic builtin logic-function names shared across crates.
pub mod builtins {
    /// Synthetic logic-function name for the floor primitive (`real_to_int`).
    pub const REAL_TO_INT_FLOOR_LOGIC_FN: &str = super::super::types::REAL_TO_INT_FLOOR_LOGIC_FN;
}

/// Synthetic symbol naming helpers used by tuple lowering.
pub mod tuple_lowering {
    /// Prefix used for synthetic logic-function encodings of tuple literals.
    pub const TUPLE_LOGIC_FN_PREFIX: &str = super::super::types::TUPLE_LOGIC_FN_PREFIX;

    /// Prefix used for synthetic logic-function encodings of tuple field access.
    pub const TUPLE_FIELD_LOGIC_FN_PREFIX: &str = super::super::types::TUPLE_FIELD_LOGIC_FN_PREFIX;

    /// Prefix used for synthetic logic-function encodings of named struct field access.
    pub const NAMED_FIELD_LOGIC_FN_PREFIX: &str = super::super::types::NAMED_FIELD_LOGIC_FN_PREFIX;

    /// Build the synthetic logic-function name for an N-ary tuple literal.
    #[must_use]
    pub fn tuple_logic_fn_name(arity: usize) -> String {
        super::super::types::tuple_logic_fn_name(arity)
    }

    /// Parse a synthetic tuple logic-function name and recover its arity.
    #[must_use]
    pub fn tuple_logic_fn_arity(name: &str) -> Option<usize> {
        super::super::types::tuple_logic_fn_arity(name)
    }

    /// Build the synthetic logic-function name for tuple field access.
    #[must_use]
    pub fn tuple_field_logic_fn_name(index: usize) -> String {
        super::super::types::tuple_field_logic_fn_name(index)
    }

    /// Parse a synthetic tuple field logic-function name and recover its field index.
    #[must_use]
    pub fn tuple_field_logic_fn_index(name: &str) -> Option<usize> {
        super::super::types::tuple_field_logic_fn_index(name)
    }
}
