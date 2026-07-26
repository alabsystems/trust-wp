// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SMT-LIB2 output generation
//!
//! Generates SMT-LIB2 format text for verification conditions.
//! This can be piped to ay or any SMT-LIB2 compatible solver.
//!
//! # Example Output
//!
//! ```text
//! ; VC for function: increment
//! (declare-const x Int)
//! (declare-const result Int)
//! (assert (> x (- 2147483648)))  ; precondition: x > i32::MIN
//! (assert (= result (+ x 1)))    ; function body
//! (assert (not (= result (+ x 1))))  ; negated postcondition
//! (check-sat)  ; unsat means postcondition holds
//! ```
//!
//! # Module Structure
//!
//! - `VarSort`: SMT sort for variables (Int, Bool, Seq)
//! - `SmtGenerator`: High-level API for generating SMT queries
//! - Expression encoding: `expr_to_smt`
//! - Formula encoding: `formula_to_smt`
//! - Preambles: `generate_heap_preamble`, `generate_seq_preamble`,
//!   `generate_bitwise_preamble`

mod encoding;
mod sorts;

#[cfg(test)]
mod sorts_tests;
#[cfg(test)]
mod tests;

// Re-export for tests (used in tests.rs via `use super::*`)
#[cfg(test)]
pub(crate) use encoding::{
    collect_vars_expr, collect_vars_formula, collect_vars_with_sorts, extract_footprint_names,
    generate_bitwise_preamble, generate_heap_preamble, generate_seq_preamble, infer_var_sorts,
    infer_var_sorts_multi, is_seq_var, needs_bitwise_preamble, needs_heap_preamble,
    needs_seq_preamble,
};
pub use encoding::{expr_to_smt, formula_to_smt, SmtGenerator};
#[cfg(test)]
pub(crate) use sorts::SortConversionError;
pub use sorts::VarSort;
