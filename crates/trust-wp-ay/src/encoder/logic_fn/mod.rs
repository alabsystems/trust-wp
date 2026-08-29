// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Logic function registration, axiom assertion, and call encoding.
//!
//! This module handles:
//! - Declaring and registering user-defined `#[logic]` functions as SMT uninterpreted functions
//! - Asserting defining axioms (with E-matching triggers) for non-opaque logic functions
//! - Type invariant registration and container element invariant assertions
//! - Logic function call encoding (resolve, seq, tuple, datatype constructors)
//!
//! Quantifier encoding (`forall`/`exists`, Bool expansion, `resolve(x)`) is in
//! `quantifier.rs`. Trigger synthesis is in `trigger.rs`.
//!
//! Submodules:
//! - `batch`: Prescan and batch registration wrappers
//! - `call_encoding`: Call-site encoding, sort coercion, and builtin dispatch
//! - `ground_instances`: Recursive logic-function ground-instance assertion
//! - `param_sort_infer`: Pure PureExpr walkers for parameter sort inference
//! - `registration`: Logic-function registration and axiom emission
//! - `signature`: Logic-function signature declaration and preseeding
//! - `type_invariant`: Type invariant axiom registration and container element invariants

mod batch;
mod call_encoding;
mod ground_instances;
mod param_sort_infer;
mod registration;
mod signature;
mod type_invariant;

pub(crate) use call_encoding::transparent_adapter_inner;
