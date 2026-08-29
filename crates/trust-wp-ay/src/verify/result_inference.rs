// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Result type inference from postconditions.
//!
//! This module is split into small submodules:
//! - `shared`: result-variable walkers shared by multiple inference passes
//! - `bool_inference`: Bool-result inference from postconditions
//! - `datatype`: Option/Result datatype inference
//! - `collection`: Seq/FMap and constructor-name inference

mod bool_inference;
mod collection;
mod datatype;
mod shared;

pub(crate) use bool_inference::result_is_bool_by_postcondition_with_context;
#[cfg(test)]
pub(crate) use bool_inference::{expr_requires_result_bool, result_is_bool_by_postcondition};
#[cfg(test)]
pub(crate) use collection::result_collection_sort_from_postcondition;
pub(crate) use collection::result_collection_sort_from_postcondition_with_context;
#[cfg(test)]
pub(crate) use datatype::expr_match_datatype_for_result;
pub(crate) use datatype::{
    detect_body_constructor_name, option_datatype_from_constructor_expr,
    result_match_datatype_from_postcondition,
};
pub(crate) use shared::expr_contains_result_var;
