// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Pre-`transform_contract` rewrites for one parsed contract.

use tracing::trace;

use super::{trace::trace_parsed_contract_state, SharedVerificationState};
use crate::{
    callbacks::{
        integer_range::build_unsigned_range_preconditions,
        logic_fn_scope::{
            build_scoped_self_logic_fn_path_map, inline_scoped_self_logic_fn_calls,
            normalize_logic_fn_names,
        },
        parsing::ParsedContract,
        verification::{
            clause_enrichment::apply_const_item_substitutions_to_loop_invariants,
            nested_reborrow_transfer::apply_nested_transfer_resolutions, store_prophecy_repair,
        },
    },
    contracts::FunctionContract,
};

/// Apply the ordered rewrites that must precede `transform_contract`.
pub(super) fn apply_pre_transform_rewrites(
    shared: &SharedVerificationState<'_, '_>,
    contract: &FunctionContract,
    parsed: &mut ParsedContract,
    def_path: &str,
    loc: &str,
    qualified_def_path: &str,
) {
    trace_parsed_contract_state(parsed, def_path, loc);

    // SMT Int is unbounded, so inject source-language integer ranges before
    // either the loop or function verification path consumes the clauses.
    let int_range_preconditions =
        build_unsigned_range_preconditions(shared.tcx, contract.def_id, &parsed.arg_names);
    if !int_range_preconditions.is_empty() {
        trace!(
            count = int_range_preconditions.len(),
            "integer range preconditions injected",
        );
        parsed.requires.extend(int_range_preconditions);
    }

    // Inline same-parent, precondition-free `Self::` logic calls and normalize
    // the remaining names before solver encoding.
    let self_logic_fn_path_map =
        build_scoped_self_logic_fn_path_map(shared.logic_fns, qualified_def_path);
    if !shared.logic_fns.is_empty() {
        parsed.rewrite_all_exprs(|expr| {
            let inlined = inline_scoped_self_logic_fn_calls(
                expr.clone(),
                shared.logic_fns,
                qualified_def_path,
            );
            normalize_logic_fn_names(inlined, &self_logic_fn_path_map)
        });
    }

    apply_const_item_substitutions_to_loop_invariants(
        parsed,
        &shared.prep.const_item_substitutions,
    );

    // These prophecy repairs must precede `transform_contract` so their
    // repaired assumptions flow into `effective_requires`.
    store_prophecy_repair::repair_superseded_prophecy_pins(shared.tcx, contract.def_id, parsed);
    // The raw `LetAssume { *p == <rhs>, .. }` deref-store hypothesis pins the
    // ENTRY carrier, not the post-state, so it is false in general and
    // contradictory whenever `<rhs>` reads `*p`. Delete it for plain `&mut`
    // params; the per-borrow carrier expiry facts already carry the store.
    store_prophecy_repair::neutralize_plain_mut_ref_entry_store_facts(
        shared.tcx,
        contract.def_id,
        parsed,
    );
    apply_nested_transfer_resolutions(parsed);
}
