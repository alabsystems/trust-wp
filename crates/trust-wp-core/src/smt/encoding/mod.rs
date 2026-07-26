// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! SMT encoding for pure expressions and separation logic formulas.
//!
//! This module is decomposed into focused submodules:
//! - [`context`]: `SmtContext` enum and pattern binding helpers
//! - [`sort_inference`]: Variable sort inference (Int/Bool/Seq)
//! - [`expr_printer`]: `PureExpr` → SMT-LIB2 text
//! - [`formula_printer`]: Formula → SMT-LIB2 text (separation logic)
//! - [`preamble`]: SMT preamble generation (heap, seq, bitwise)
//! - [`var_collect`]: Free variable collection walkers
//! - [`generator`]: High-level `SmtGenerator` API

mod context;
mod expr_printer;
mod formula_printer;
mod generator;
mod preamble;
mod sort_inference;
mod var_collect;

// Re-export the `sorts` module from the parent so submodules can use `super::sorts::VarSort`
// === Public API (consumed by smt/mod.rs and downstream crates) ===
// These re-exports are consumed by the parent module; allow(unused) suppresses
// the false-positive warnings from the facade pattern.
#[allow(unused_imports)]
pub use expr_printer::expr_to_smt;
#[cfg(test)]
pub(crate) use formula_printer::extract_footprint_names;
#[allow(unused_imports)]
pub use formula_printer::formula_to_smt;
pub use generator::SmtGenerator;
#[allow(unused_imports)]
pub(crate) use preamble::generate_bitwise_preamble;
#[allow(unused_imports)]
pub(crate) use preamble::generate_seq_preamble;
// === Test-only exports ===
#[cfg(test)]
pub(crate) use preamble::{
    generate_heap_preamble, needs_bitwise_preamble, needs_heap_preamble, needs_seq_preamble,
};
#[cfg(test)]
pub(crate) use sort_inference::infer_var_sorts_multi;
#[allow(unused_imports)]
pub(crate) use sort_inference::is_seq_var;
#[allow(unused_imports)]
pub(crate) use sort_inference::{collect_vars_with_sorts, infer_var_sorts};
#[allow(unused_imports)]
pub(crate) use var_collect::{collect_vars_expr, collect_vars_formula};

use super::sorts;

/// Maximum recursion depth for PureExpr walker functions.
///
/// Guards against stack overflow on deeply nested expression trees from MIR
/// lowering. Mirrors `MAX_ENCODING_DEPTH` (128) in trust-wp-ay.
pub(super) const MAX_RECURSION_DEPTH: usize = 128;
