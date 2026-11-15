// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The effective clause pair the function-level VC is built from.
//!
//! Two post-transform rewrites sit between `contract_transform`'s output and
//! the function-level VC, and both must run on exactly the clauses that VC
//! discharges. They live here so `per_contract.rs` states the lane structure
//! and nothing else.

use trust_wp_core::formula::PureExpr;

use super::{
    super::{
        super::{super::contracts::FunctionContract, parsing::ParsedContract},
        contract_transform::TransformedContract,
    },
    stale_entry_facts,
    state::SharedVerificationState,
};

/// Consume the transformed contract and return the `(requires, ensures)` pair
/// the function-level VC is discharged against.
pub(super) fn effective_clauses_for_function_vc(
    shared: &SharedVerificationState<'_, '_>,
    contract: &FunctionContract,
    parsed: &ParsedContract,
    def_path: &str,
    tc: TransformedContract,
) -> (Vec<PureExpr>, Vec<PureExpr>) {
    let TransformedContract {
        mut effective_requires,
        mut effective_ensures,
        base_requires_count,
        call_assumption_derived_count,
        ..
    } = tc;

    // The ENSURES half of the stale-entry-fact rule (D-38): a `#[requires]`
    // clause names the ENTRY pointee of a by-reference parameter with the same
    // encoder symbol as its CURRENT value, and a write inside a loop body is
    // not walked by the extraction, so without this drop the entry fact
    // survives the loop and discharges the postcondition
    // (`s59_ens_stale_param_pointee_after_loop.rs`). See `stale_entry_facts`
    // for the mechanism and the program point.
    stale_entry_facts::drop_loop_invalidated_entry_facts(
        shared,
        contract,
        parsed,
        def_path,
        &mut effective_requires,
        base_requires_count,
        call_assumption_derived_count,
    );

    // Re-rewrite synthesized `inv(x)` LogicFnCalls into type-qualified
    // MethodCalls so the synthesized `&mut`-param preconditions share the same
    // type-qualified invariant symbol as `^x.invariant()` postconditions
    // (partially_opaque #1), then discharge any residual bare `inv(arg)` reborrow
    // side-conditions on roots with no registered invariant to `true` (#8373).
    // See `rewrite_synthesized_invariant_calls`.
    super::super::super::type_invariants::rewrite_synthesized_invariant_calls(
        shared.tcx,
        contract.def_id,
        &parsed.arg_names,
        shared.config.type_invariant_defs,
        &mut effective_requires,
        &mut effective_ensures,
    );

    (effective_requires, effective_ensures)
}
