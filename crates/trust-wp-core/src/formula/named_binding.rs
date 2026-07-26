// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sort-carrying synthetic binding payload for named values.
//!
//! `NamedBindingValue` couples a right-hand-side expression with the known
//! sort of the symbolic binding name, so that loop pre-state bindings and
//! similar transport maps preserve type information across the driver -> ay
//! boundary. (#2053)

use super::pure_expr::{ExprSort, PureExpr};

/// A named binding value that carries the sort of the left-hand symbolic
/// variable alongside the right-hand expression.
///
/// Used in loop pre-state transport maps to prevent sort erasure at the
/// driver -> ay boundary. The `sort` field records the MIR-derived sort
/// of the symbolic variable named by the map key.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct NamedBindingValue {
    /// The MIR-derived sort of the symbolic variable (the map key).
    /// `None` falls back to the default `Int` sort at encode time.
    pub sort: Option<ExprSort>,
    /// The right-hand-side expression (the value at loop entry).
    pub value: PureExpr,
}

impl NamedBindingValue {
    /// Create a new binding value with an explicit sort.
    #[must_use]
    pub fn new(sort: Option<ExprSort>, value: PureExpr) -> Self {
        Self { sort, value }
    }

    /// Create a binding from a bare expression with no sort annotation.
    #[must_use]
    pub fn untyped(value: PureExpr) -> Self {
        Self { sort: None, value }
    }

    /// Reconstruct the left-hand symbolic variable with the stored sort.
    ///
    /// This is the primary consumer API: instead of rebuilding
    /// `PureExpr::Var(name, None)` at each equality site, callers use
    /// `binding.lhs_var(name)` to get a typed variable.
    #[must_use]
    pub fn lhs_var(&self, name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), self.sort.clone())
    }
}
