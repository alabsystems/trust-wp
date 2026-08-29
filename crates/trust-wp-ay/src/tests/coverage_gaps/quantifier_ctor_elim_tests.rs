// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Unit tests for `encoder/quantifier_ctor_elim.rs` (#1946 Phase 3).
//!
//! Coverage targets:
//! - `arg_is_qvar_reference`: quantifier variable detection through wrappers
//! - `extract_scrutinee_var_name`: scrutinee variable extraction through wrappers
//! - `detect_constructor_eq` + `eliminate_constructor_eq_quantifier`: integration
//!   tests via the quantifier encoding path
//!
//! The pure utility functions (`arg_is_qvar_reference`, `extract_scrutinee_var_name`)
//! are tested directly. Encoder-dependent functions (`detect_constructor_eq`,
//! `infer_constructor_arg_sort`, `eliminate_constructor_eq_quantifier`) are tested
//! indirectly through quantifier encoding with registered datatypes.

use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};

use super::*;

mod multi_variable;
mod nullary_and_reversed;
mod option_some_patterns;
mod wrappers;

/// Build and register an Option<Int> datatype with the encoder.
fn register_option_int(encoder: &mut AYEncoder) -> DatatypeSort {
    let dt = DatatypeSort {
        name: "OptionInt".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "option_some_value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    encoder.ensure_datatype_declared(&dt);
    dt
}
