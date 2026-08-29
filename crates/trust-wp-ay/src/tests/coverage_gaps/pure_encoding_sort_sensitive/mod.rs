// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for sort-sensitive match arms in `pure_encoding.rs`.
//!
//! These tests target the core encoding logic that depends on sort inference
//! and sort-sensitive dispatch. Each test verifies semantic correctness (not
//! just "doesn't panic") by checking SAT/UNSAT outcomes via `encode_pure`.
//!
//! Coverage targets:
//! - Bool-valued Ite encoding (implication form vs SMT ite)
//! - Eq/Ne mixed-sort operand encoding (Bool vs non-Bool dispatch)
//! - Eq sort resolution with `prefer_specific_sort` integration
//! - `encode_unop` (Not / Neg encoding)
//! - `seed_bool_context_hints` (invoked by Not and Ite condition)
//! - Old expression encoding (old_prefix, old-deref identity)
//! - MAX_ENCODING_DEPTH guard
//! - Quantifier-bound variable old() collapse
//! - Let binding substitution
//! - Closure unsupported error
//!
//! Note: standalone unit tests for `prefer_specific_sort`, `peel_deref_depth`,
//! `peel_final_depth`, `wrap_with_deref`, and `wrap_with_final` belong in
//! `pure_encoding.rs` inline `#[cfg(test)]` module (requires Worker commit for
//! `pub(crate)` visibility changes). See #1946 handoff.
//!
//! Part of #1946 (pure_encoding.rs unit tests).

pub(super) use super::*;

mod bool_iff;
mod bool_ite;
mod closure;
mod eq_ne_mixed_sort;
mod let_binding;
mod max_encoding_depth;
mod old_expr;
mod quantifier_bound_var;
mod seq_eq_decomposition;
mod seq_ne_no_propagation;
mod unop_and_bool_hints;
mod var_annotations;
