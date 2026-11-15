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
            nested_reborrow_transfer::apply_nested_transfer_resolutions,
            stale_call_final::drop_stale_call_final_assumptions, store_prophecy_repair,
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
    // Before both resolution sets, which are exact and must not be filtered:
    // the filter withdraws what a CALL credited, while the nested-slot and
    // lent resolutions are the mut-borrow traversal's own exit values, read
    // after every write it saw, and it emits none where it lost a write
    // (a havoc, an unrecognized call on a slot, a lent slot). Filtered, the
    // nested-slot set left `inc_max_3` (nested_transfer_soundness.rs) with no
    // final value for any slot.
    drop_stale_call_final_assumptions(parsed);
    name_by_value_param_finals_apart(shared, contract, parsed);
    apply_nested_transfer_resolutions(parsed);
    apply_lent_path_resolutions(parsed);
}

/// The symbol the value a by-value ADT parameter holds after a `&mut`
/// borrow of it ends is read by (D-241).
fn by_value_param_final_name(name: &str) -> String {
    format!("{name}{BY_VALUE_PARAM_FINAL_SUFFIX}")
}

const BY_VALUE_PARAM_FINAL_SUFFIX: &str = "__final_value";

/// Give the value a by-value struct or enum parameter holds after a `&mut`
/// borrow of the WHOLE parameter a name of its own (D-241).
///
/// The mut-borrow lane advances `s` past `reset(&mut s)` to `^s`, the final
/// value of the borrow, and reads `s.a` after the call as
/// `tuple_get_0(^s)`. The encoder collapses `^v` of a plain datatype value
/// onto `v` (a call result has no post-state), and for a parameter `v` is
/// its ENTRY value, which the `#[requires]` and the type invariant
/// constrain: the call did nothing
/// (struct_param_whole_mut_borrow_call_keeps_entry_value.rs). An integer
/// parameter keeps a distinct final symbol and was never affected. Renamed,
/// `^s` is a value only the callee's postcondition about `^t` speaks of,
/// which is what the borrow hands back; a second borrow's `^^s` is a symbol of
/// its own again, which only that callee's postcondition speaks of. Only a
/// parameter whose own storage the body lends mutably is renamed; a `^s` of
/// any other is left to the collapse, as before.
fn name_by_value_param_finals_apart(
    shared: &SharedVerificationState<'_, '_>,
    contract: &FunctionContract,
    parsed: &mut ParsedContract,
) {
    use trust_wp_core::formula::{ExprSort, PureExpr};

    if shared.tcx.is_closure_like(contract.def_id) {
        return;
    }
    let Some(body_with_facts) =
        crate::callbacks::try_get_body_with_context(shared.tcx, contract.local_def_id)
    else {
        return;
    };
    let body = crate::mir_analysis::get_mir_body(&body_with_facts);
    let lent = crate::mir_analysis::params_written_before(body, None);
    let names: std::collections::HashSet<String> = lent
        .into_iter()
        .filter(|local| {
            let ty = body.local_decls[*local].ty;
            ty.is_adt() && !ty.is_box()
        })
        .filter_map(|local| parsed.arg_names.get(local.as_usize() - 1).cloned())
        .collect();
    if names.is_empty() {
        return;
    }
    // A later borrow of the parameter reads the value the earlier one handed
    // back: `^^s` after two calls, each level a value of its own.
    let roots_at_a_lent_param = |name: &str| {
        let mut root = name;
        while let Some(stripped) = root.strip_suffix(BY_VALUE_PARAM_FINAL_SUFFIX) {
            root = stripped;
        }
        names.contains(root)
    };
    let rename = |expr: &PureExpr| -> PureExpr {
        expr.rewrite_bottom_up(|node| {
            if let PureExpr::Final(inner) = &node {
                if let PureExpr::Var(name, sort @ Some(ExprSort::Datatype(_))) = inner.as_ref() {
                    if roots_at_a_lent_param(name) {
                        return PureExpr::Var(by_value_param_final_name(name), sort.clone());
                    }
                }
            }
            node
        })
    };
    parsed.rewrite_all_exprs(rename);
}

/// Append the path-gated resolutions for `&mut` params lent into the return
/// value on some paths (`path ==> ^p == <pointee at exit>` on paths where `p`
/// is not returned). Exact RustHorn semantics for a borrow that expires at
/// function exit on that path; premises.
fn apply_lent_path_resolutions(parsed: &mut ParsedContract) {
    let Some(mut_borrow) = parsed.mut_borrow.mut_borrow_body.as_ref() else {
        return;
    };
    if mut_borrow.lent_path_resolutions.is_empty() {
        return;
    }
    let resolutions = mut_borrow.lent_path_resolutions.clone();
    parsed.call_assumptions.extend(resolutions);
}
