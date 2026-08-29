// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Residual FMap, FSet, and deep_model axiom assertions.
//!
//! Other axiom modules live alongside this directory:
//! - `closure_axioms`
//! - `adt_axioms`
//! - `produces_axioms`
//!
//! # Panic isolation bypass (#1806)
//!
//! Axiom calls in this module use `self.solver.assert_term()` directly rather
//! than the panic-isolated `self.assert_solver_term()` wrapper from `solver.rs`.
//! This is acceptable because:
//!
//! 1. Axiom terms are built from solver-constructed sorts with no user-supplied
//!    sort inference, so sort mismatches are programming errors.
//! 2. Axioms are asserted once during theory initialization, not on per-expression
//!    encoding paths where user contracts can trigger sort bugs.
//! 3. Revision ordering is irrelevant because setup happens before any `check_sat`
//!    calls.

mod deep_model;
pub(crate) mod demand;
mod fmap;
mod fset;
mod layout;
mod trait_postcondition;
mod type_invariant;
