// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Fail-closed guard: a named-field pattern whose declared field positions
//! cannot be established.
//!
//! The contract parser reads TEXT, so `E::C { b: bb, a: aa }` reaches the
//! driver as a list of field names and a list of sub-patterns in the order
//! they were WRITTEN. The encoder binds those sub-patterns POSITIONALLY
//! against the declared datatype, so the written order has to be translated
//! into the DECLARED order before it gets there.
//!
//! Leaving a field name that cannot be resolved where it was written would be
//! a guess: on `E::C { a: u32, b: A }` the guess binds `aa` to the `A` field,
//! `A::view()` answers for it, and a postcondition about a `u32` is reported
//! proved (`s82_structpat_reorder_nested.rs`). There is no fallback (D-31):
//! `rewrite_parsed_contract_structure` either places every named field at its
//! declared index or refuses, and this guard turns the refusal into a counted,
//! named error on the function (`s82_structpat_unresolvable_ctor_refused.rs`).
//!
//! Creusot cannot have this shape: it reads THIR, where rustc has already
//! resolved each pattern field to a `FieldIdx`.

use super::{
    super::{contract_rewrite::rewrite_parsed_contract_structure, parsing::ParsedContract},
    per_contract::SharedVerificationState,
};
use crate::contracts::FunctionContract;

/// Apply the structural contract rewrites, reporting and counting a
/// field-order refusal instead of verifying on a guessed field order.
///
/// Returns `false` when the contract was refused; the caller must stop.
pub(super) fn rewrite_contract_structure_or_refuse(
    shared: &SharedVerificationState<'_, '_>,
    contract: &FunctionContract,
    parsed: &mut ParsedContract,
    def_path: &str,
    errors: &mut usize,
) -> bool {
    let outcome = rewrite_parsed_contract_structure(
        shared.tcx,
        contract.def_id,
        parsed,
        shared.config.type_invariant_defs,
        &shared.prep.logic_method_names,
        &shared.prep.user_shadowed_builtins,
    );
    match outcome {
        Ok(()) => true,
        Err(why) => {
            eprintln!(
                "trust-wp: {def_path} error: {why}; refusing instead of binding the fields \
                 in the order they were written, which would bind one field as another"
            );
            *errors += 1;
            false
        }
    }
}
