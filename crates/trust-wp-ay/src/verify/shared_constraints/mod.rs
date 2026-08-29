// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Shared verification constraint utilities.
//!
//! Contains helper functions shared across verification submodules, including
//! ghost implication flattening, path-condition propagation, and alias
//! constraint utilities.

mod alias_constraints;
mod ghost_flatten;
mod path_conditions;

pub(in crate::verify) use alias_constraints::{
    assert_current_chain_alias_constraints, infer_result_sort,
};
pub(crate) use ghost_flatten::{
    assert_ghost_alias_method_congruence, assert_known_ghost_precondition_implications,
    flatten_ghost_implications, instantiate_precondition_foralls_for_ghost,
};
#[cfg(test)]
pub(super) use ghost_flatten::{is_ground_constant, is_substitutable_expr, substitute_constants};
pub(in crate::verify) use path_conditions::assert_body_let_assume_path_conditions;
