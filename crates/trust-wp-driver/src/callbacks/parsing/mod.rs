// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Contract parsing and body extraction.
//!
//! Handles parsing of contract strings into `PureExpr` values,
//! extraction of MIR bodies, and HIR utility functions.

mod arg_names;
mod clauses;
mod extraction;
mod handback;
mod spec_tables;
#[cfg(test)]
mod tests;
mod types;

pub(crate) use arg_names::closure_capture_index_names;
pub(in crate::callbacks) use arg_names::get_arg_names_from_def_id;
pub(in crate::callbacks) use clauses::{conjoin_exprs, parse_contract_clauses, ClauseParseError};
pub(in crate::callbacks) use extraction::{parse_and_extract_contract, ExtractionContext};
pub(in crate::callbacks) use spec_tables::{
    build_positional_param_renaming, build_trait_spec_table, build_user_spec_table,
    only_type_param_invariants, param_invariant_grant,
};
#[allow(unused_imports)]
// LoopFields/MutBorrowFields are part of the test-facing parsing surface.
pub(in crate::callbacks) use types::{
    LoopFields, LoopObligationGroup, MutBorrowFields, ParsedContract,
};
