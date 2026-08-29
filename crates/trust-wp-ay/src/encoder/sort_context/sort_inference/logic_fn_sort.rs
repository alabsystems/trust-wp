// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::Sort;
use tracing::debug;
use trust_wp_core::formula::{
    internal::{
        builtins::REAL_TO_INT_FLOOR_LOGIC_FN,
        tuple_lowering::{
            tuple_logic_fn_arity, NAMED_FIELD_LOGIC_FN_PREFIX, TUPLE_FIELD_LOGIC_FN_PREFIX,
        },
    },
    PureExpr,
};

use super::{fmap_sort, unit_sort};
use crate::encoder::{
    match_enc::{stdlib_constructor_target, stdlib_option_datatype_for_payload, SwitchTarget},
    pure_encoding::{
        parse_int_truncate_name, parse_shift_amount_in_range_name,
        parse_unsigned_to_signed_same_width_cast_name,
    },
    unsoundness,
};

pub(super) fn infer_logic_fn_sort(
    name: &str,
    args: &[PureExpr],
    infer_expr_sort: &mut impl FnMut(&PureExpr) -> Sort,
) -> Sort {
    if matches!(name, "seq" | "Seq::singleton" | "seq_empty" | "Seq::empty") {
        return Sort::seq(Sort::Int);
    }
    if matches!(
        name,
        "fmap_insert" | "fmap_merge" | "fmap_empty" | "FMap::empty" | "__trust_wp_fmap_iter_view"
    ) {
        return fmap_sort();
    }
    // IterMut view projector returns Seq (analogous to fmap_iter_view returning FMap).
    if name == "__trust_wp_iter_mut_view" {
        return Sort::seq(Sort::Int);
    }
    if args.is_empty() && name == "__trust_wp_tuple0" {
        return unit_sort();
    }
    if let Some(arity) = tuple_logic_fn_arity(name) {
        return Sort::Uninterpreted(format!("Tuple{arity}"));
    }
    if name == "resolve" {
        return Sort::Bool;
    }
    // `Int::min` / `Int::max` are creusot-std logic builtins that return `Int`
    // and are dispatched to ay's native min/max (`ite(a<=b,a,b)`). The Int
    // return is the genuine, definite result sort — not a fallback for an
    // unknown UF — so it must not trigger a SortFallbackToIntFromLogicFn
    // demotion (which would otherwise downgrade every loop VC that mentions
    // `Int::min` from Verified to Unknown). (#2702)
    if matches!(name, "Int::min" | "Int::max") {
        return Sort::Int;
    }
    if name == "inv"
        || name.ends_with("_inv")
        || trust_wp_core::logic::is_invariant_method_name(name)
    {
        return Sort::Bool;
    }
    // User logic methods may reach raw AST sort inference by their unqualified
    // method name before declaration context is available. These are common
    // collection/hashmap contracts whose return carriers are part of trust-wp's
    // canonical encoding, not an Int fallback.
    if name == "get" && args.len() == 2 {
        return Sort::Uninterpreted(SwitchTarget::OptionInt.datatype().name);
    }
    if name == "bucket_ix" {
        return Sort::Int;
    }
    if matches!(name, "no_double_binding" | "good_bucket") {
        return Sort::Bool;
    }
    if name.starts_with(TUPLE_FIELD_LOGIC_FN_PREFIX) {
        return Sort::Int;
    }
    if let Some(field_name) = name.strip_prefix(NAMED_FIELD_LOGIC_FN_PREFIX) {
        // View resource-algebra projections. The trust-wp-std `View<R>` stub
        // exposes the authority/fragment halves as named struct fields, so the
        // `auth()` and `frag()` logic methods lower to named-field accessors.
        // For the FMap view RA used by `fmap_view_view`, the fragment is an
        // `FMap<K, Ag<V>>` (so `frag → FMap`, already handled) and the authority
        // is an `Option<FMap<K, V>>`. Encoding `auth()` as the Option-of-FMap
        // carrier (instead of the `Int` fallback) lets obligations such as
        // `view.auth() != None` and `view.auth().unwrap_logic()` discharge
        // against the same option datatype the rest of the proof uses, rather
        // than thrashing over an Int-sorted placeholder. (RA view frag/auth)
        if field_name == "frag" {
            return fmap_sort();
        }
        if field_name == "auth" {
            return Sort::Uninterpreted(stdlib_option_datatype_for_payload(fmap_sort()).name);
        }
        return Sort::Int;
    }
    if name == "fmap_contains" {
        return Sort::Bool;
    }
    if name == "fmap_into_seq" {
        return Sort::seq(Sort::Int);
    }
    if matches!(name, "fmap_len" | "fmap_lookup") {
        return Sort::Int;
    }
    // Mapping logic functions: Mapping is a total function (K -> V).
    // mapping_cst, mapping_set produce Mapping, mapping_get returns Int,
    // mapping_contains returns Bool. (#2663)
    if matches!(
        name,
        "mapping_cst" | "mapping_set" | "mapping_empty" | "Mapping::cst"
    ) {
        return super::mapping_sort();
    }
    if name == "mapping_get" {
        return Sort::Int;
    }
    if name == "mapping_contains" {
        return Sort::Bool;
    }
    // Ghost helper methods from Seq, FMap, FSet — used inside `ghost!` blocks.
    // These appear as bare method names (e.g., "len_ghost") in LogicFnCall nodes
    // after ghost-block substitution extraction. Without recognition here, they
    // fall through to SortFallbackToIntFromLogicFn, causing ghost_vec/ghost_map
    // verification failures. (#2671)
    if matches!(name, "len_ghost") {
        return Sort::Int;
    }
    if matches!(name, "is_empty_ghost" | "contains_ghost") {
        return Sort::Bool;
    }
    if matches!(
        name,
        "get_ghost" | "get_mut_ghost" | "pop_back_ghost" | "pop_front_ghost"
    ) {
        // These return Option<T> in all collection types (Seq, FMap).
        // Use OptionInt as the canonical sort — matches stdlib_constructor_target.
        return Sort::Uninterpreted(SwitchTarget::OptionInt.datatype().name);
    }
    // insert_ghost: returns Option<V> on FMap, bool on FSet.
    // remove_ghost: returns Option<V> on FMap, bool on FSet.
    // Disambiguate via receiver sort when possible; default to OptionInt (FMap
    // is more common in ghost_map tests and OptionInt subsumes bool via coercion).
    if matches!(name, "insert_ghost" | "remove_ghost") {
        if let Some(receiver) = args.first() {
            let receiver_sort = infer_expr_sort(receiver);
            // FSet uses Bool-valued membership, so its sort is not fmap_sort.
            // If the receiver is recognizably an FSet, return Bool.
            if receiver_sort == Sort::Bool {
                return Sort::Bool;
            }
        }
        // Default: FMap path returns Option<V>
        return Sort::Uninterpreted(SwitchTarget::OptionInt.datatype().name);
    }
    // push_back_ghost, push_front_ghost: mutate Seq in-place, return ().
    // The result of the LogicFnCall is typically discarded, but if it appears
    // in an expression context the sort should be unit (empty tuple).
    if matches!(name, "push_back_ghost" | "push_front_ghost") {
        return unit_sort();
    }
    if name == "final_value" {
        return args.first().map_or(Sort::Int, infer_expr_sort);
    }
    if name == REAL_TO_INT_FLOOR_LOGIC_FN {
        return Sort::Int;
    }
    // Synthetic Int cast/truncation functions emitted by the driver are
    // intercepted by pure encoding and encoded with exact BV semantics. Their
    // return sort is always Int, so AST-level sort probes should not count
    // them as unknown logic functions.
    if parse_int_truncate_name(name).is_some()
        || parse_unsigned_to_signed_same_width_cast_name(name).is_some()
    {
        return Sort::Int;
    }
    // Shift-amount-in-range marker (ledger int-shift-full): identity on its
    // Int argument; pure encoding intercepts it to collect the range side
    // obligation. Same reasoning as the truncation intrinsics above.
    if parse_shift_amount_in_range_name(name).is_some() {
        return Sort::Int;
    }
    // Layout intrinsics (size_of_logic, align_of_logic, and their
    // type-specialized variants like size_of_logic__bool) genuinely
    // return Int — sizes and alignments are integers. (#2324)
    if name.starts_with("size_of_logic") || name.starts_with("align_of_logic") {
        return Sort::Int;
    }
    // Turbofish wrapper is a type-level marker eliminated during
    // encoding normalization. Return Int to avoid a false-positive
    // sort fallback counter increment. (#2324)
    if name == trust_wp_core::contract_parser::TURBOFISH_ARG_WRAPPER_NAME {
        return args.first().map_or(Sort::Int, infer_expr_sort);
    }
    match stdlib_constructor_target(name) {
        Some(SwitchTarget::OptionInt) => {
            if name.rsplit_once("::").map_or(name, |(_, short)| short) == "Some" {
                if let Some(payload) = args.first() {
                    let payload_sort = infer_expr_sort(payload);
                    return Sort::Uninterpreted(
                        stdlib_option_datatype_for_payload(payload_sort).name,
                    );
                }
            }
            return Sort::Uninterpreted(SwitchTarget::OptionInt.datatype().name);
        }
        Some(SwitchTarget::ResultIntInt) => {
            return Sort::Uninterpreted(SwitchTarget::ResultIntInt.datatype().name);
        }
        _ => {}
    }
    if name
        .rsplit_once("::")
        .is_some_and(|(_, short)| short.starts_with(char::is_uppercase))
    {
        let (prefix, _) = name
            .rsplit_once("::")
            .expect("guard ensures :: separator exists");
        return Sort::Uninterpreted(prefix.replace("::", "_"));
    }
    // Zero-argument logic functions with no `::` separator that are
    // all-uppercase match the `declare_namespace!` macro pattern
    // (e.g., `PERMCELL` from `declare_namespace! { PERMCELL }`).
    // These functions return `usize` which maps to Int. The fallback
    // to Int is correct and should not trigger a demotion. (#2701)
    if args.is_empty()
        && !name.contains("::")
        && !name.is_empty()
        && name.chars().all(|c| c.is_ascii_uppercase() || c == '_')
    {
        return Sort::Int;
    }

    debug!("[TRUST_WP_DEBUG] SortFallbackToIntFromLogicFn: \"{name}\"");

    unsoundness::increment(unsoundness::UnsoundnessCategory::SortFallbackToIntFromLogicFn);
    Sort::Int
}
