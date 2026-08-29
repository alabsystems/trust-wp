// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Resolve assertion emission for dataflow-precise borrow resolution (#2124).
//!
//! For each `&mut` parameter with a precise resolve point (determined by the
//! driver's resolve analysis), emits `v_final == v_current` as an SMT assumption.
//! This is the Creusot-style backward prophecy closure: the borrow's final value
//! equals its current value at the point where the borrow goes out of scope.
//!
//! Sound because the resolve analysis (trust-wp-driver) verified that the borrow
//! is dead at the resolve point. The assumption enables the solver to work
//! backward from call postconditions (already injected by `call_assumptions`).

use std::collections::{HashMap, HashSet};

use trust_wp_core::formula::{
    internal::tuple_lowering::tuple_field_logic_fn_name, BorrowFinality, BorrowIdOrigin,
    BorrowIdStep, PureExpr,
};

use crate::{
    encoder::{unsoundness, AYEncoder, MutRefVarNames},
    error::EncodingError,
};

const INHERIT_FIELD_STEP_KIND: i64 = 0;
const INHERIT_INDEX_STEP_KIND: i64 = 1;

/// Emit resolve assertions for parameters in the resolve list.
///
/// For each `&mut` parameter with a precise resolve point, emits
/// `v_final == v_current` — UNLESS the parameter is in `mutation_continued_params`
/// or `final_values` contains a non-identity expression for the parameter.
///
/// Mutation-continued params already have their `v_final` constrained by
/// `call_assumptions` (merged into requires). Emitting `v_final == v_current`
/// for these would contradict the call assumption (which says `v_final` is the
/// POST-mutation state, not the entry-time `v_current`). (#2124 Phase 5b)
///
/// Similarly, params with non-identity final values (e.g., `*a + 1` for `*a += 1`)
/// already have `v_final` constrained by `bind_final_values`. Emitting
/// `v_final == v_current` would contradict the final value constraint, making
/// the base assertions UNSAT and triggering vacuous proof detection. (#2663)
///
/// # Conditional resolve gating (Phase 3/4)
///
/// When the postcondition has the shape `if cond { ... && ^p == *p } else { ... }`
/// (or symmetric), the resolve for `p` is *path-dependent* — `^p == *p` only
/// holds when `cond` is true. This pattern arises in functions like
/// `proj_toggle(toggle, a, b) -> &mut T`:
///
/// ```text
/// #[ensures(if toggle { result == a && ^b == *b } else { result == b && ^a == *a })]
/// ```
///
/// Emitting `b_final == b_current` *unconditionally* over-constrains: in the
/// `toggle == false` branch, `b` is the returned borrow and the caller may
/// mutate `*b` after the call, so `b_final != b_current` in general. When the
/// conditional pattern is detected, we emit a gated resolve
/// `gate ==> (p_final == p_current)` instead. (Phase 3/4)
/// Emit slice-length-preservation assumptions for `&mut [T]` parameters.
///
/// A `&mut [T]` slice cannot change its length — the length lives in the fat
/// pointer and only the elements are mutable (unlike `&mut Vec<T>`). So
/// `seq_len` of every program-point state of the slice (loop-head `v_view`,
/// call-site `v_current_view`, prophecy `v_final_view` / `v_final`) is equal,
/// EVEN when the borrow is not resolved as identity (the elements differ).
/// The encoder otherwise links these symbols only on the resolved path, so a
/// slice param mutated across an inner call has its prophecy length left free,
/// admitting spurious counterexamples (bitvectors/bitwalker). This links them
/// at the length level only (not full view equality), driven by the driver's
/// `&mut [T]` detection. Soundness: the equality holds for every well-typed
/// `&mut [T]`; it removes only spurious models.
pub(super) fn emit_slice_length_preservation(encoder: &mut AYEncoder, var_name: &str) {
    // Enumerate ALL currently-declared symbols that are program-point states of
    // this slice param — `var_name` with any combination of view/current/final
    // decorations (suffixes `_view`/`_current`/`_final` and prefix `final_`,
    // possibly nested, e.g. `final_addr_final_view`). For a `&mut [T]` slice all
    // such states have equal `seq_len` (the length is immutable), so we chain
    // every one to a single length term. Enumeration (vs a fixed candidate
    // list) is required because the proof_assert goal introduces deeply-nested
    // prophecy states (`final_addr_final_final_view`) that a fixed list misses.
    fn normalize_slice_state_base(name: &str) -> String {
        let mut n = name;
        loop {
            if let Some(s) = n.strip_prefix("final_") {
                n = s;
                continue;
            }
            if let Some(s) = n
                .strip_suffix("_view")
                .or_else(|| n.strip_suffix("_current"))
                .or_else(|| n.strip_suffix("_final"))
            {
                n = s;
                continue;
            }
            break;
        }
        n.to_string()
    }
    let mut len_terms: Vec<ay_dpll::api::Term> = Vec::new();
    for name in encoder.var_names() {
        if normalize_slice_state_base(&name) != var_name {
            continue;
        }
        let Some(term) = encoder.var_term(&name) else {
            continue;
        };
        if let Ok(len_term) = encoder.seq_len_term(term) {
            len_terms.push(len_term);
        }
    }
    // Chain-assert all equal to the first.
    if let Some((&first, rest)) = len_terms.split_first() {
        for &other in rest {
            encoder.assert_eq(other, first);
        }
    }
}

pub(super) fn emit_resolve_assertions(
    encoder: &mut AYEncoder,
    resolve_assumptions: Option<&Vec<String>>,
    mutation_continued: Option<&HashSet<String>>,
    final_values: &HashMap<String, PureExpr>,
    ensures: &[PureExpr],
) {
    let Some(resolve_names) = resolve_assumptions else {
        return;
    };
    for var_name in resolve_names {
        // Skip resolve for mutation-continued params: call_assumptions already
        // constrain v_final. Emitting v_final == v_current would contradict
        // the call postcondition that advanced v_final. (#2124 Phase 5b)
        if mutation_continued.is_some_and(|mcp| mcp.contains(var_name)) {
            continue;
        }
        // Skip resolve for params whose final value is non-identity. The body
        // analysis already extracted the correct final expression (e.g., `*a + 1`
        // for `*a += 1`), and `bind_final_values` constrains `v_final` to that
        // expression. Asserting `v_final == v_current` on top would create a
        // contradiction (`v_current + 1 == v_current` is UNSAT), causing the
        // vacuity guard to demote an otherwise valid proof. (#2663)
        if let Some(final_expr) = final_values.get(var_name) {
            if !is_identity_final_value(var_name, final_expr) {
                continue;
            }
        }

        // Detect conditional resolve gating (Phase 3/4). When the postcondition
        // expresses `^p == *p` only inside one branch of an ITE, the path
        // predicate of that branch becomes the resolve gate.
        let resolve_gate = detect_conditional_resolve_gate(var_name, ensures);

        let names = MutRefVarNames::new(var_name);
        if let (Some(current_term), Some(final_term)) = (
            encoder.var_term(&names.current),
            encoder.var_term(&names.final_val),
        ) {
            let _current_sort = encoder
                .var_sort(&names.current)
                .cloned()
                .unwrap_or_else(|| {
                    unsoundness::increment(
                        unsoundness::UnsoundnessCategory::SortFallbackToIntFromVar,
                    );
                    ay_dpll::api::Sort::Int
                });
            if let Some(gate_expr) = resolve_gate.as_ref() {
                // Emit gated resolve: `gate ==> (p_final == p_current)`.
                //
                // Skip propagation helpers (view/tuple/current_final): they
                // would also need to be gated, and over-emission could
                // over-constrain the un-resolved branch. The postcondition,
                // when proven, carries the conditional equality for those
                // projections via standard congruence.
                if let Ok(gate_term) = encoder.encode_pure(gate_expr) {
                    let eq_term = encoder.eq_term(final_term, current_term);
                    let implication = encoder.solver.implies(gate_term, eq_term);
                    encoder.assert_term(implication);
                    continue;
                }
                // Encoding the gate failed; fall through to the unconditional
                // path so we still emit *something* (matches prior behavior).
            }
            encoder.assert_eq(final_term, current_term);

            // Propagate resolve equality to view-level aliases. (#2673)
            //
            // When `v_final == v_current`, any derived property should also
            // be equal: `v_final_view == v_current_view`. The AUFLIA solver
            // can sometimes derive this via UF congruence, but making it
            // explicit avoids "incomplete" results on contracts that mix
            // `(*v)@` and `(^v)@` comparisons for resolved borrows.
            emit_resolve_view_propagation(encoder, var_name);

            // Propagate resolve equality to the _current_final scalar variable.
            // (#2673 strengthened)
            //
            // For resolved borrows with identity final values, bindings.rs
            // already sets v_current_final == v_final_term. But the resolve
            // assertion v_final == v_current provides the additional constraint
            // that v_current_final == v_current. Making this explicit helps
            // the solver close chains like:
            //   ^(*x) == ... where ^(*x) resolves to x_current_final
            //   and x_current_final should equal x_current (from resolve)
            emit_resolve_current_final_propagation(encoder, var_name);

            // Propagate resolve equality through tuple field projections. (#2673)
            //
            // When `v_final == v_current`, the AUFLIA solver should derive
            // `tuple_get_N(v_final) == tuple_get_N(v_current)` by UF congruence,
            // but sometimes cannot within the timeout for deeply nested ITE
            // expressions or when sort coercion is active. Making this explicit
            // enables patterns like:
            //   ^_x.0 == *_x.0  →  tuple_get_0(v_final) == tuple_get_0(v_current)
            // without relying on the solver's congruence closure.
            emit_resolve_tuple_field_propagation(encoder, var_name);

            // Propagate resolve equality through tuple field projections for
            // the _current_final variable. (#2673 strengthened)
            //
            // When the postcondition uses the Deref(Var) form (from
            // transform_postcondition_for_mut_refs), `Final(tuple_get_N(Deref(Var)))`
            // encodes as `tuple_get_N(v_current_final)`. The resolve says
            // `v_final == v_current` and bindings says `v_current_final == v_final`,
            // so `tuple_get_N(v_current_final) == tuple_get_N(v_current)`. Making
            // this explicit avoids multi-step congruence chains that the AUFLIA
            // solver may not close, especially for patterns like `drop_pair` where
            // the postcondition tests multiple tuple field projections.
            emit_resolve_current_final_tuple_field_propagation(encoder, var_name);
        }
    }
}

/// Propagate resolve equality to the `_current_final` scalar variable. (#2673)
///
/// When `v_final == v_current` (resolve assertion), and `v_current_final` exists
/// (declared by `bind_final_values` for the `Final(Deref(Var("v")))` pattern),
/// assert `v_current_final == v_current`. This is sound because:
///   v_current_final = v_final_term (from bindings.rs)
///   v_final_term = Deref(Var("v")) = v_current (for identity)
///   v_final == v_current (from resolve)
/// So v_current_final == v_current.
///
/// Also propagate to `v_final_final` if it exists, asserting
/// `v_final_final == v_current`. For the unnest pattern, this enables
/// `^^x == *x` when x is resolved.
fn emit_resolve_current_final_propagation(encoder: &mut AYEncoder, var_name: &str) {
    use crate::encoder::sort_context::DerivedKind;

    let current_name = DerivedKind::Current.format_name(var_name);
    let current_final_name =
        DerivedKind::format_chain(var_name, &[DerivedKind::Current, DerivedKind::Final]);

    if let (Some(current_term), Some(current_final_term)) = (
        encoder.var_term(&current_name),
        encoder.var_term(&current_final_name),
    ) {
        let compatible = match (
            encoder.var_sort(&current_name),
            encoder.var_sort(&current_final_name),
        ) {
            (Some(a), Some(b)) => sorts_compatible_for_writeback(a, b),
            _ => false,
        };
        if compatible {
            encoder.assert_eq(current_final_term, current_term);
        }
    }

    // Also propagate v_final_final == v_current for resolved identity borrows.
    // This is sound: v_final_final == v_current_final (from bindings.rs identity
    // alias) and v_current_final == v_current (from above), so
    // v_final_final == v_current.
    let final_final_name =
        DerivedKind::format_chain(var_name, &[DerivedKind::Final, DerivedKind::Final]);
    if let (Some(current_term), Some(final_final_term)) = (
        encoder.var_term(&current_name),
        encoder.var_term(&final_final_name),
    ) {
        let compatible = match (
            encoder.var_sort(&current_name),
            encoder.var_sort(&final_final_name),
        ) {
            (Some(a), Some(b)) => sorts_compatible_for_writeback(a, b),
            _ => false,
        };
        if compatible {
            encoder.assert_eq(final_final_term, current_term);
        }
    }

    // Propagate v_final_current == v_current for resolved identity borrows. (#2673)
    //
    // When a postcondition uses `Deref(Final(Var("v")))` (= `*^v`), the encoder
    // creates `v_final_current`. The resolve assertion says `v_final == v_current`,
    // so dereferencing both sides gives `Deref(v_final) == Deref(v_current)`,
    // i.e., `v_final_current == v_current_current`. Since `v_current_current`
    // typically aliases `v_current` or doesn't exist (for non-reference inner
    // types), we propagate `v_final_current == v_current` directly.
    //
    // This is critical for `pair_bor_mut` where the postcondition says:
    //   `*^p1 == *p1` (untouched field's final deref equals current deref)
    // Without this, `p1_final_current` is unconstrained and the solver cannot
    // prove the equality.
    let final_current_name =
        DerivedKind::format_chain(var_name, &[DerivedKind::Final, DerivedKind::Current]);
    if let (Some(current_term), Some(final_current_term)) = (
        encoder.var_term(&current_name),
        encoder.var_term(&final_current_name),
    ) {
        let compatible = match (
            encoder.var_sort(&current_name),
            encoder.var_sort(&final_current_name),
        ) {
            (Some(a), Some(b)) => sorts_compatible_for_writeback(a, b),
            _ => false,
        };
        if compatible {
            encoder.assert_eq(final_current_term, current_term);
        }
    }

    // Also propagate v_current_current == v_current if it exists. (#2673)
    //
    // For non-reference inner types, `Deref(Deref(Var("v")))` (= `**v`) creates
    // `v_current_current`. This should be the same as `v_current` since dereferencing
    // a non-reference type is an identity operation.
    let current_current_name =
        DerivedKind::format_chain(var_name, &[DerivedKind::Current, DerivedKind::Current]);
    if let (Some(current_term), Some(current_current_term)) = (
        encoder.var_term(&current_name),
        encoder.var_term(&current_current_name),
    ) {
        let compatible = match (
            encoder.var_sort(&current_name),
            encoder.var_sort(&current_current_name),
        ) {
            (Some(a), Some(b)) => sorts_compatible_for_writeback(a, b),
            _ => false,
        };
        if compatible {
            encoder.assert_eq(current_current_term, current_term);
        }
    }
}

/// Propagate resolve equality to view-level aliases. (#2673)
///
/// When `v_final == v_current` is asserted (the borrow was not mutated), the
/// view/model projections should also be equal. The AUFLIA solver can sometimes
/// derive `v_final_view == v_current_view` from `v_final == v_current` via UF
/// congruence, but this requires the solver to reason through the view encoding
/// function, which is not always possible within the solver's timeout.
///
/// This function explicitly asserts:
/// - `v_current_final_view == v_current_view` (if both exist)
/// - `v_final_view == v_current_view` (if both exist)
/// - `final_v_view == v_view` (if both exist)
///
/// These are sound consequences of the resolve assertion and the identity final
/// value binding: `v_final == v_current` implies any function of `v_final` equals
/// the same function of `v_current`.
fn emit_resolve_view_propagation(encoder: &mut AYEncoder, var_name: &str) {
    use crate::encoder::sort_context::DerivedKind;

    let current_view_name =
        DerivedKind::View.format_name(&DerivedKind::Current.format_name(var_name));
    // v_current_final is the "what does the current value become after the borrow ends"
    // variable. For resolved borrows (identity), v_current_final == v_final == v_current.
    // Propagating to the view level: v_current_final_view == v_current_view.
    let current_final_view_name = DerivedKind::View.format_name(&DerivedKind::format_chain(
        var_name,
        &[DerivedKind::Current, DerivedKind::Final],
    ));
    if let (Some(current_view), Some(current_final_view)) = (
        encoder.var_term(&current_view_name),
        encoder.var_term(&current_final_view_name),
    ) {
        let views_compatible = match (
            encoder.var_sort(&current_view_name),
            encoder.var_sort(&current_final_view_name),
        ) {
            (Some(a), Some(b)) => sorts_compatible_for_writeback(a, b),
            _ => false,
        };
        if views_compatible {
            encoder.assert_eq(current_final_view, current_view);
        }
    }

    // Also propagate v_final_view == v_current_view directly.
    // This covers postconditions using `(^v)@` and `(*v)@`.
    let final_view_name = DerivedKind::View.format_name(&DerivedKind::Final.format_name(var_name));
    if let (Some(current_view), Some(final_view)) = (
        encoder.var_term(&current_view_name),
        encoder.var_term(&final_view_name),
    ) {
        let views_compatible = match (
            encoder.var_sort(&current_view_name),
            encoder.var_sort(&final_view_name),
        ) {
            (Some(a), Some(b)) => sorts_compatible_for_writeback(a, b),
            _ => false,
        };
        if views_compatible {
            encoder.assert_eq(final_view, current_view);
        }
    }

    // Propagate v_final_current_view == v_current_view. (#2673)
    //
    // When a postcondition uses `View(Deref(Final(Var("v"))))` (= `(*^v)@`),
    // the encoder creates `v_final_current_view`. The resolve says
    // `v_final == v_current`, so `Deref(v_final) == Deref(v_current)`, and
    // applying View gives `v_final_current_view == v_current_view`.
    let final_current_view_name = DerivedKind::View.format_name(&DerivedKind::format_chain(
        var_name,
        &[DerivedKind::Final, DerivedKind::Current],
    ));
    if let (Some(current_view), Some(final_current_view)) = (
        encoder.var_term(&current_view_name),
        encoder.var_term(&final_current_view_name),
    ) {
        let views_compatible = match (
            encoder.var_sort(&current_view_name),
            encoder.var_sort(&final_current_view_name),
        ) {
            (Some(a), Some(b)) => sorts_compatible_for_writeback(a, b),
            _ => false,
        };
        if views_compatible {
            encoder.assert_eq(final_current_view, current_view);
        }
    }

    // Propagate to base-level view: v_view (which aliases v_current_view in
    // bind_view_aliases) should also match the final-prefixed view.
    let base_view_name = DerivedKind::View.format_name(var_name);
    let final_prefix_view_name =
        DerivedKind::format_chain(var_name, &[DerivedKind::FinalPrefix, DerivedKind::View]);
    if let (Some(base_view), Some(final_prefix_view)) = (
        encoder.var_term(&base_view_name),
        encoder.var_term(&final_prefix_view_name),
    ) {
        let views_compatible = match (
            encoder.var_sort(&base_view_name),
            encoder.var_sort(&final_prefix_view_name),
        ) {
            (Some(a), Some(b)) => sorts_compatible_for_writeback(a, b),
            _ => false,
        };
        if views_compatible {
            encoder.assert_eq(final_prefix_view, base_view);
        }
    }
}

/// Propagate resolve equality through declared tuple field projections. (#2673)
///
/// When `v_final == v_current` is asserted (resolve), and tuple field accessor
/// functions `__trust_wp_tuple_get_N` have been declared by the encoder, emit
/// explicit constraints:
///   `tuple_get_N(v_final) == tuple_get_N(v_current)` for each declared get_N
///
/// These are logical consequences of the resolve equality (by UF congruence:
/// if a == b then f(a) == f(b)). However, the AUFLIA solver's congruence
/// closure may not always close these equalities within the timeout, especially
/// when:
/// - The v_final/v_current terms have deeply nested ITE subexpressions
/// - Sort coercion is active between the operands
/// - Multiple tuple accessors are used (e.g., drop_pair with both get_0, get_1)
///
/// Making them explicit is sound and helps patterns like `drop_pair` and
/// `pair_bor_mut` where the postcondition directly references
/// `tuple_get_N(^v)` and `tuple_get_N(*v)`.
fn emit_resolve_tuple_field_propagation(encoder: &mut AYEncoder, var_name: &str) {
    use trust_wp_core::formula::internal::tuple_lowering::TUPLE_FIELD_LOGIC_FN_PREFIX;

    use crate::encoder::sort_context::DerivedKind;

    let current_name = DerivedKind::Current.format_name(var_name);
    let final_name = DerivedKind::Final.format_name(var_name);

    let (Some(current_term), Some(final_term)) = (
        encoder.var_term(&current_name),
        encoder.var_term(&final_name),
    ) else {
        return;
    };

    let current_sort = encoder
        .var_sort(&current_name)
        .cloned()
        .unwrap_or(ay_dpll::api::Sort::Int);
    let final_sort = encoder
        .var_sort(&final_name)
        .cloned()
        .unwrap_or(ay_dpll::api::Sort::Int);

    // Only propagate if the sorts are compatible (same sort or one is Int fallback).
    if !sorts_compatible_for_writeback(&current_sort, &final_sort) {
        return;
    }

    // Scan declared logic functions for tuple field accessors.
    let smt_field_prefix = trust_wp_core::logic::logic_fn_smt_name(TUPLE_FIELD_LOGIC_FN_PREFIX);

    let accessors: Vec<(usize, ay_dpll::api::FuncDecl)> = encoder
        .decls()
        .logic_funcs_iter()
        .filter_map(|(name, decl)| {
            let suffix = name.strip_prefix(&smt_field_prefix)?;
            let index = suffix.parse::<usize>().ok()?;
            Some((index, decl.clone()))
        })
        .collect();

    for (index, accessor_decl) in accessors {
        let fn_name =
            trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(index);

        // Apply the accessor to both current and final terms.
        // Use safe_apply which handles sort mismatches gracefully.
        let projected_current = encoder.safe_apply(&fn_name, &accessor_decl, &[current_term]);
        let projected_final = encoder.safe_apply(&fn_name, &accessor_decl, &[final_term]);

        if let (Ok(proj_current), Ok(proj_final)) = (projected_current, projected_final) {
            encoder.assert_eq(proj_final, proj_current);
        }
    }
}

/// Propagate resolve equality through tuple field projections for `_current_final`. (#2673)
///
/// Analogous to [`emit_resolve_tuple_field_propagation`] but operates on the
/// `v_current_final` variable instead of `v_final`. When the postcondition uses
/// the `Deref(Var)` form (from `transform_postcondition_for_mut_refs`), field
/// projections like `Final(tuple_get_N(Deref(Var("v"))))` encode as
/// `tuple_get_N(v_current_final)`. The resolve says `v_final == v_current` and
/// bindings says `v_current_final == v_final`, so:
///
///   `tuple_get_N(v_current_final) == tuple_get_N(v_current)`
///
/// Making this explicit avoids a multi-step congruence chain the AUFLIA solver
/// may not close, especially for patterns like `drop_pair` and `pair_bor_mut`
/// where the postcondition tests multiple tuple field projections through the
/// `Deref(Var)` form.
fn emit_resolve_current_final_tuple_field_propagation(encoder: &mut AYEncoder, var_name: &str) {
    use trust_wp_core::formula::internal::tuple_lowering::TUPLE_FIELD_LOGIC_FN_PREFIX;

    use crate::encoder::sort_context::DerivedKind;

    let current_name = DerivedKind::Current.format_name(var_name);
    let current_final_name =
        DerivedKind::format_chain(var_name, &[DerivedKind::Current, DerivedKind::Final]);

    let (Some(current_term), Some(current_final_term)) = (
        encoder.var_term(&current_name),
        encoder.var_term(&current_final_name),
    ) else {
        return;
    };

    let current_sort = encoder
        .var_sort(&current_name)
        .cloned()
        .unwrap_or(ay_dpll::api::Sort::Int);
    let current_final_sort = encoder
        .var_sort(&current_final_name)
        .cloned()
        .unwrap_or(ay_dpll::api::Sort::Int);

    // Only propagate if the sorts are compatible.
    if !sorts_compatible_for_writeback(&current_sort, &current_final_sort) {
        return;
    }

    // Scan declared logic functions for tuple field accessors.
    let smt_field_prefix = trust_wp_core::logic::logic_fn_smt_name(TUPLE_FIELD_LOGIC_FN_PREFIX);

    let accessors: Vec<(usize, ay_dpll::api::FuncDecl)> = encoder
        .decls()
        .logic_funcs_iter()
        .filter_map(|(name, decl)| {
            let suffix = name.strip_prefix(&smt_field_prefix)?;
            let index = suffix.parse::<usize>().ok()?;
            Some((index, decl.clone()))
        })
        .collect();

    for (index, accessor_decl) in accessors {
        let fn_name =
            trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(index);

        // Apply the accessor to both current and current_final terms.
        let projected_current = encoder.safe_apply(&fn_name, &accessor_decl, &[current_term]);
        let projected_current_final =
            encoder.safe_apply(&fn_name, &accessor_decl, &[current_final_term]);

        if let (Ok(proj_current), Ok(proj_current_final)) =
            (projected_current, projected_current_final)
        {
            encoder.assert_eq(proj_current_final, proj_current);
        }
    }
}

/// Check whether a final value expression is the identity `Deref(Var(name))`.
///
/// Identity final values mean the body didn't mutate the parameter, so the
/// resolve assertion `v_final == v_current` is correct and non-contradictory.
///
/// Recognizes `Ite(_, identity, identity)` as identity (Phase 3/4): functions
/// like `proj_toggle(toggle, a, b)` whose body is `if toggle { a } else { b }`
/// produce per-param `final_values` of the form
/// `Ite(toggle, Deref(p), Deref(p))` — semantically identical to `Deref(p)`
/// but not literal-equal. Without this recursion, every conditional return
/// inside a non-mutating body would skip the resolve assertion.
pub(super) fn is_identity_final_value(var_name: &str, final_expr: &PureExpr) -> bool {
    match final_expr {
        PureExpr::Deref(inner) => {
            matches!(inner.as_ref(), PureExpr::Var(name, _) if name == var_name)
        }
        PureExpr::Ite(_, then_branch, else_branch) => {
            is_identity_final_value(var_name, then_branch)
                && is_identity_final_value(var_name, else_branch)
        }
        _ => false,
    }
}

/// Detect a conditional resolve gate from postcondition shape. (Phase 3/4)
///
/// Returns `Some(gate_expr)` when the postcondition contains `^v == *v` inside
/// exactly one branch of an `Ite` (not both, not at top level). For
/// `proj_toggle`'s shape:
///
/// ```text
/// if toggle { result == a && ^b == *b } else { result == b && ^a == *a }
/// ```
///
/// For `var_name = "b"` the gate is `toggle`; for `var_name = "a"` it is
/// `!toggle`. Returns `None` when the resolve clause is missing, appears
/// unconditionally, or multiple distinct gates are inferred (ambiguous).
fn detect_conditional_resolve_gate(var_name: &str, ensures: &[PureExpr]) -> Option<PureExpr> {
    let mut gates: Vec<PureExpr> = Vec::new();
    for expr in ensures {
        collect_conditional_resolve_gates(var_name, expr, &mut gates);
    }
    let first = gates.first()?.clone();
    if gates.iter().all(|g| g == &first) {
        Some(first)
    } else {
        None
    }
}

/// Walk an expression looking for `^v == *v` inside an `Ite` arm and collect
/// the path predicate of that arm.
fn collect_conditional_resolve_gates(var_name: &str, expr: &PureExpr, gates: &mut Vec<PureExpr>) {
    match expr {
        PureExpr::Ite(cond, then_branch, else_branch) => {
            let then_has = expr_contains_resolve_clause(var_name, then_branch);
            let else_has = expr_contains_resolve_clause(var_name, else_branch);
            match (then_has, else_has) {
                (true, false) => gates.push((**cond).clone()),
                (false, true) => gates.push(PureExpr::UnOp(
                    trust_wp_core::formula::UnOp::Not,
                    cond.clone(),
                )),
                _ => {
                    collect_conditional_resolve_gates(var_name, then_branch, gates);
                    collect_conditional_resolve_gates(var_name, else_branch, gates);
                }
            }
        }
        PureExpr::BinOp(lhs, op, rhs) if matches!(op, trust_wp_core::formula::BinOp::And) => {
            collect_conditional_resolve_gates(var_name, lhs, gates);
            collect_conditional_resolve_gates(var_name, rhs, gates);
        }
        _ => {}
    }
}

/// Check whether an expression contains `^v == *v` (or `*v == ^v`).
fn expr_contains_resolve_clause(var_name: &str, expr: &PureExpr) -> bool {
    match expr {
        PureExpr::BinOp(lhs, op, rhs) if matches!(op, trust_wp_core::formula::BinOp::Eq) => {
            is_final_deref_pair(var_name, lhs, rhs) || is_final_deref_pair(var_name, rhs, lhs)
        }
        PureExpr::BinOp(lhs, op, rhs) if matches!(op, trust_wp_core::formula::BinOp::And) => {
            expr_contains_resolve_clause(var_name, lhs)
                || expr_contains_resolve_clause(var_name, rhs)
        }
        PureExpr::Ite(_, then_branch, else_branch) => {
            // Counts only when BOTH arms have it (unconditional within the
            // nested ITE). Otherwise the outer detection logic handles gating.
            expr_contains_resolve_clause(var_name, then_branch)
                && expr_contains_resolve_clause(var_name, else_branch)
        }
        _ => false,
    }
}

/// Check whether (lhs, rhs) is `(Final(Var(var)), Deref(Var(var)))`.
fn is_final_deref_pair(var_name: &str, lhs: &PureExpr, rhs: &PureExpr) -> bool {
    matches!(
        (lhs, rhs),
        (PureExpr::Final(inner_l), PureExpr::Deref(inner_r))
            if matches!(inner_l.as_ref(), PureExpr::Var(n, _) if n == var_name)
                && matches!(inner_r.as_ref(), PureExpr::Var(n, _) if n == var_name)
    )
}

/// Check whether two sorts are compatible for writeback equality assertions.
///
/// Previously, writebacks required exact sort equality, which silently dropped
/// constraints when sort fallback produced `Int` for one side and a concrete
/// sort (e.g., `__trust_wp_mutref::int`) for the other. This function relaxes
/// the gate to also allow:
///
/// 1. Exact sort match (same as before)
/// 2. One side is `Int` (sort fallback) — the `assert_eq` coercion layer
///    (`harmonize_eq_or_ite_terms`) will bridge via `coerce_ite_sorts`
/// 3. Structurally compatible sorts (same family, different strength) —
///    handled by `select_structural_sort_target` inside coercion
///
/// The only case we still skip is when both sides are non-Int AND from
/// different sort families (e.g., Seq vs Datatype), where asserting equality
/// would be semantically meaningless.
///
/// (#2673: relaxed sort gate for mut-borrow writeback propagation)
fn sorts_compatible_for_writeback(a: &ay_dpll::api::Sort, b: &ay_dpll::api::Sort) -> bool {
    use crate::encoder::sort_context::select_structural_sort_target;

    // Exact match — always compatible.
    if a == b {
        return true;
    }
    // Int on either side — sort fallback produced Int, coercion will bridge.
    if *a == ay_dpll::api::Sort::Int || *b == ay_dpll::api::Sort::Int {
        return true;
    }
    // Structurally compatible sorts (e.g., MutRef carrier vs inner sort).
    if select_structural_sort_target(a, b).is_some() {
        return true;
    }
    false
}

/// Emit prophecy writeback constraints for intermediate reborrows (#2124 Phase 3).
///
/// For each reborrow `z = &mut *y`, asserts `y_current == z_final`. This is the
/// Creusot-style prophecy writeback: at borrow creation, the parent's current
/// value is constrained to equal the child's (unknown) final value. When the
/// child borrow resolves (`z_final == z_current`), the parent transitively
/// inherits the child's accumulated mutations.
///
/// When finality data is available (#2181), final borrows get an additional
/// constraint: `parent_final == child_final`, directly propagating the prophecy
/// without requiring the solver to chain through `current` variables.
///
/// When `resolve_set` is provided (#2673), resolved parents also get the
/// `parent_final == child_final` constraint. This is the transitive closure
/// optimization: `parent_final == parent_current` (resolve) and
/// `parent_current == child_final` (writeback) imply `parent_final == child_final`,
/// but the AUFLIA solver cannot always close this chain. Making it explicit
/// avoids "incomplete" results on tests like `take_first_mut` and `unnest`.
///
/// # Soundness
///
/// The writeback `y_current = z_final` is sound because:
/// - `z = &mut *y` creates an exclusive reborrow — `y` cannot be used while `z` is live
/// - When `z` resolves, its final value IS `y`'s new current value (by Rust's borrow semantics)
/// - The prophecy variable `z_final` is unconstrained at creation time and becomes
///   constrained when `emit_resolve_assertions` fires for `z`
///
/// The final-borrow optimization `parent_final == child_final` is sound because:
/// - The parent borrow is never used after the reborrow (finality analysis guarantee)
/// - Therefore the child's final value IS the parent's final value
///
/// The transitive closure optimization is sound because it is a logical
/// consequence of the resolve assertion and the writeback constraint — it adds
/// no new information, only makes an existing implication explicit. (#2673)
///
/// # Projection-aware writebacks (#2673, strengthened)
///
/// When `borrow_id_origins` contains a `Derived` entry with `Field(n)` steps
/// for a child reborrow, the writeback emits field-projected equalities:
/// - `child_current == tuple_get_N(parent_current)` instead of skipping
/// - `child_final == tuple_get_N(parent_final)` for final propagation
///
/// This enables proofs of patterns like:
/// ```text
/// fn reborrow_field(r: &mut (T, T)) -> &mut T { &mut r.0 }
/// #[ensures(result == &mut r.0)]
/// ```
pub(super) fn emit_prophecy_writebacks(
    encoder: &mut AYEncoder,
    writebacks: Option<&HashMap<String, String>>,
    finality: Option<&HashMap<String, BorrowFinality>>,
    resolve_set: Option<&Vec<String>>,
    borrow_id_origins: Option<&HashMap<String, BorrowIdOrigin>>,
    mutation_continued: Option<&HashSet<String>>,
    final_values: Option<&HashMap<String, PureExpr>>,
) {
    let Some(writebacks) = writebacks else {
        return;
    };
    for (child_name, parent_name) in writebacks {
        let child_names = MutRefVarNames::new(child_name);
        let parent_names = MutRefVarNames::new(parent_name);

        // When the parent borrow is mutation-continued, the `call_assumption`
        // already advances `parent_final` through the child's final, and the
        // encoder uses a single SSA-style `<parent>_current` name for the
        // parent's *entry-time* current value. Asserting
        // `parent_current == child_final` here fuses the entry-time current
        // with the post-call value, which (combined with a precondition that
        // pins `*parent` to a concrete value) collapses base premises to
        // UNSAT and trips vacuity detection. See bug/682 / #5 / sibling of
        // #2663 (which fixed the analogous `emit_resolve_assertions` case).
        let parent_is_mutation_continued =
            mutation_continued.is_some_and(|mcp| mcp.contains(parent_name.as_str()));

        // Same hazard when the parent's final value was SPEC-ADVANCED to a
        // non-identity post-state (e.g. `v.push(x)` through a two-phase
        // reborrow carrier: `bind_final_values` asserts
        // `v_final == push_back(v_current_view, ..)`). The child carrier's
        // final IS that post-call state, so `parent_current == child_final`
        // fuses the entry-time current with the post-mutation value and
        // collapses base premises to UNSAT (bug/two_phase: `len == len + 1`).
        // This is the prophecy-writeback analogue of the #2663
        // `emit_resolve_assertions` gate.
        let parent_final_is_advanced = final_values
            .and_then(|fv| fv.get(parent_name.as_str()))
            .is_some_and(|expr| !is_identity_final_value(parent_name, expr));
        let suppress_current_writeback = parent_is_mutation_continued || parent_final_is_advanced;

        // Look up whether this child has a field projection derivation.
        let field_steps = borrow_id_origins
            .and_then(|origins| origins.get(child_name.as_str()))
            .and_then(extract_field_projection_steps);

        // Child current is the parent's current value at reservation time.
        // For identity reborrows (`z = &mut *y`): z_current == y_current.
        // For field projection reborrows (`z = &mut (*y).0`):
        //   z_current == tuple_get_0(y_current). (#2673, strengthened)
        //
        // Projection takes priority over identity: when field_steps is Some,
        // ALWAYS emit the projected equality even if sorts match (both may
        // fall back to Int due to sort_fallback_to_int). Emitting the identity
        // equality on top would force `parent == tuple_get_N(parent)` which
        // is generally UNSAT.
        if let (Some(child_current), Some(parent_current)) = (
            encoder.var_term(&child_names.current),
            encoder.var_term(&parent_names.current),
        ) {
            let child_sort = encoder
                .var_sort(&child_names.current)
                .cloned()
                .unwrap_or(ay_dpll::api::Sort::Int);
            let parent_sort = encoder
                .var_sort(&parent_names.current)
                .cloned()
                .unwrap_or_else(|| {
                    unsoundness::increment(
                        unsoundness::UnsoundnessCategory::SortFallbackToIntFromVar,
                    );
                    ay_dpll::api::Sort::Int
                });
            if let Some(ref steps) = field_steps {
                // Field projection reborrow: emit projected equality.
                // child_current == tuple_get_N(parent_current)
                emit_projected_equality(
                    encoder,
                    child_current,
                    parent_current,
                    steps,
                    &child_sort,
                    &parent_sort,
                );
            } else if sorts_compatible_for_writeback(&child_sort, &parent_sort) {
                // Identity reborrow: child_current == parent_current.
                // assert_eq handles sort coercion internally via
                // harmonize_eq_or_ite_terms when sorts differ (e.g., Int
                // vs MutRef carrier due to sort_fallback_to_int). (#2673)
                encoder.assert_eq(child_current, parent_current);
            }
        }

        // Standard writeback: parent_current == child_final.
        // For identity reborrows: y_current == z_final.
        // For field projections: child_final == tuple_get_N(y_current). (#2673)
        //
        // Same priority rule: projection over identity when field_steps present.
        //
        // SKIP this writeback when the parent is mutation-continued OR its
        // final value was spec-advanced to a non-identity post-state: the
        // `call_assumption` / `bind_final_values` already constrains
        // `parent_final` through the post-call state, while
        // `<parent>_current` is the entry-time current. Fusing them here
        // causes vacuous-UNSAT collapse — sibling of #2663. See bug/682 /
        // #5 / bug/two_phase.
        if !suppress_current_writeback {
            if let (Some(child_final), Some(parent_current)) = (
                encoder.var_term(&child_names.final_val),
                encoder.var_term(&parent_names.current),
            ) {
                let child_final_sort = encoder
                    .var_sort(&child_names.final_val)
                    .cloned()
                    .unwrap_or(ay_dpll::api::Sort::Int);
                let parent_current_sort = encoder
                    .var_sort(&parent_names.current)
                    .cloned()
                    .unwrap_or_else(|| {
                        unsoundness::increment(
                            unsoundness::UnsoundnessCategory::SortFallbackToIntFromVar,
                        );
                        ay_dpll::api::Sort::Int
                    });
                if let Some(ref steps) = field_steps {
                    // Field projection reborrow: projected writeback.
                    // child_final == tuple_get_N(parent_current)
                    emit_projected_equality(
                        encoder,
                        child_final,
                        parent_current,
                        steps,
                        &child_final_sort,
                        &parent_current_sort,
                    );
                } else if sorts_compatible_for_writeback(&child_final_sort, &parent_current_sort) {
                    // Identity writeback: parent_current == child_final.
                    // assert_eq handles sort coercion when sorts differ. (#2673)
                    encoder.assert_eq(parent_current, child_final);
                }
            }
        }

        // Final-borrow optimization (#2181) + transitive closure optimization (#2673):
        // Assert parent_final == child_final (or projected version for field reborrows)
        // when either:
        // (a) the parent borrow is final at the reborrow site (finality analysis), OR
        // (b) the parent is in the resolve set (will get parent_final == parent_current), OR
        // (c) the parent is mutation-continued (bug/682 / #5): the call_assumption
        //     advances `parent_final` through the child's final via the prophecy
        //     chain on the *final* side, and the per-edge writeback on the
        //     `_current` side is skipped above to avoid vacuous-UNSAT collapse.
        //
        // For field projection reborrows, emits:
        //   child_final == tuple_get_N(parent_final)
        // This is the projected version of the propagation. (#2673, strengthened)
        let is_final = finality
            .and_then(|f| f.get(child_name))
            .is_some_and(|b| matches!(b, BorrowFinality::Final { .. }));
        let parent_is_resolved =
            resolve_set.is_some_and(|rs| rs.iter().any(|name| name == parent_name));
        let should_propagate_final = is_final || parent_is_resolved || parent_is_mutation_continued;
        if should_propagate_final {
            if let (Some(child_final), Some(parent_final)) = (
                encoder.var_term(&child_names.final_val),
                encoder.var_term(&parent_names.final_val),
            ) {
                let child_final_sort = encoder
                    .var_sort(&child_names.final_val)
                    .cloned()
                    .unwrap_or(ay_dpll::api::Sort::Int);
                let parent_final_sort = encoder
                    .var_sort(&parent_names.final_val)
                    .cloned()
                    .unwrap_or_else(|| {
                        unsoundness::increment(
                            unsoundness::UnsoundnessCategory::SortFallbackToIntFromVar,
                        );
                        ay_dpll::api::Sort::Int
                    });
                if let Some(ref steps) = field_steps {
                    // Field projection reborrow: projected final propagation.
                    // child_final == tuple_get_N(parent_final)
                    emit_projected_equality(
                        encoder,
                        child_final,
                        parent_final,
                        steps,
                        &child_final_sort,
                        &parent_final_sort,
                    );
                } else if sorts_compatible_for_writeback(&child_final_sort, &parent_final_sort) {
                    // Direct final propagation: parent_final == child_final.
                    // assert_eq handles sort coercion when sorts differ. (#2673)
                    encoder.assert_eq(parent_final, child_final);
                }
            }
        }

        // View-level writeback propagation for identity reborrows. (#2673)
        //
        // For `z = &mut *y` (identity reborrow, no field projection), the child
        // and parent share the same underlying value. Propagating the writeback
        // to the view level enables proofs that involve `(*z)@` and `(*y)@`
        // comparisons, which the AUFLIA solver cannot always derive from the
        // scalar-level writeback alone via UF congruence.
        //
        // Only emit for identity reborrows (field_steps is None) since projected
        // reborrows have different view structures.
        if field_steps.is_none() {
            emit_writeback_view_propagation(
                encoder,
                child_name,
                parent_name,
                should_propagate_final,
                suppress_current_writeback,
            );
        }
    }

    // Transitive writeback chain closure (#2673 strengthened).
    //
    // When we have reborrow chains like a -> b -> c (b writes back to a,
    // c writes back to b), the solver must chain:
    //   a_current == b_final, b_current == c_final, b_final == b_current (resolve)
    // to derive a_current == c_final. For multi-level chains, the AUFLIA solver
    // sometimes cannot close this within timeout.
    //
    // This pass computes transitive ancestors and emits direct constraints
    // between non-adjacent chain members. Only for identity reborrows (no
    // field projection steps) to avoid incorrect direct equalities.
    emit_transitive_writeback_chains(
        encoder,
        writebacks,
        resolve_set,
        borrow_id_origins,
        mutation_continued,
        final_values,
    );
}

/// Propagate writeback constraints to view-level aliases. (#2673)
///
/// For identity reborrows (`z = &mut *y`), emits:
/// - `child_current_view == parent_current_view`
/// - `child_final_view == parent_current_view` (the standard writeback at view level)
/// - `child_final_view == parent_final_view` (when final propagation is active)
///
/// These are the view-level analogs of the scalar writebacks and are sound for the
/// same reasons: an identity reborrow shares the same underlying value, so their
/// views are identical.
fn emit_writeback_view_propagation(
    encoder: &mut AYEncoder,
    child_name: &str,
    parent_name: &str,
    propagate_final: bool,
    suppress_current_writeback: bool,
) {
    use crate::encoder::sort_context::DerivedKind;

    let child_current_view =
        DerivedKind::View.format_name(&DerivedKind::Current.format_name(child_name));
    let parent_current_view =
        DerivedKind::View.format_name(&DerivedKind::Current.format_name(parent_name));

    // child_current_view == parent_current_view
    //
    // Reservation-time equality (analogue of `child_current == parent_current`).
    // Safe to emit even when the parent is mutation-continued — the child is
    // freshly created from the parent's entry-time current value.
    if let (Some(child_cv), Some(parent_cv)) = (
        encoder.var_term(&child_current_view),
        encoder.var_term(&parent_current_view),
    ) {
        let compatible = match (
            encoder.var_sort(&child_current_view),
            encoder.var_sort(&parent_current_view),
        ) {
            (Some(a), Some(b)) => sorts_compatible_for_writeback(a, b),
            _ => false,
        };
        if compatible {
            encoder.assert_eq(child_cv, parent_cv);
        }
    }

    // child_final_view == parent_current_view (writeback at view level)
    //
    // SKIP when the parent is mutation-continued or spec-advanced — view-
    // level analogue of the scalar `parent_current == child_final` writeback
    // that was skipped above. Emitting it would fuse the entry-time
    // `parent_current_view` with the post-call value, mirroring the bug/682
    // / #5 / bug/two_phase contradiction.
    let child_final_view =
        DerivedKind::View.format_name(&DerivedKind::Final.format_name(child_name));
    if !suppress_current_writeback {
        if let (Some(child_fv), Some(parent_cv)) = (
            encoder.var_term(&child_final_view),
            encoder.var_term(&parent_current_view),
        ) {
            let compatible = match (
                encoder.var_sort(&child_final_view),
                encoder.var_sort(&parent_current_view),
            ) {
                (Some(a), Some(b)) => sorts_compatible_for_writeback(a, b),
                _ => false,
            };
            if compatible {
                encoder.assert_eq(parent_cv, child_fv);
            }
        }
    }

    // child_final_view == parent_final_view (when final propagation active)
    if propagate_final {
        let parent_final_view =
            DerivedKind::View.format_name(&DerivedKind::Final.format_name(parent_name));
        if let (Some(child_fv), Some(parent_fv)) = (
            encoder.var_term(&child_final_view),
            encoder.var_term(&parent_final_view),
        ) {
            let compatible = match (
                encoder.var_sort(&child_final_view),
                encoder.var_sort(&parent_final_view),
            ) {
                (Some(a), Some(b)) => sorts_compatible_for_writeback(a, b),
                _ => false,
            };
            if compatible {
                encoder.assert_eq(parent_fv, child_fv);
            }
        }
    }
}

/// Emit transitive writeback chain closures for multi-level reborrow chains. (#2673)
///
/// Given writeback edges {child -> parent}, computes the transitive ancestry
/// for each leaf child and emits direct constraints between the leaf and all
/// non-immediate ancestors in the chain. This helps the AUFLIA solver avoid
/// multi-step reasoning through intermediate variables.
///
/// For a chain `a -> b -> c` (c writes back to b, b writes back to a):
/// - Standard writebacks already emit: `b_current == c_final`, `a_current == b_final`
/// - This function adds: `a_current == c_final` (the transitive closure)
///   and `a_final == c_final` when `a` is in the resolve set.
///
/// Only emits transitive constraints for identity reborrow chains (no field
/// projection steps), since projected reborrows have different value structures.
///
/// # Soundness
///
/// The transitive constraint `ancestor_current == descendant_final` is a logical
/// consequence of the existing per-edge writebacks plus resolve assertions:
///   ancestor_current == intermediate_final  (writeback)
///   intermediate_final == intermediate_current  (resolve)
///   intermediate_current == descendant_final  (writeback)
/// Making it explicit is sound and helps the solver.
fn emit_transitive_writeback_chains(
    encoder: &mut AYEncoder,
    writebacks: &HashMap<String, String>,
    resolve_set: Option<&Vec<String>>,
    borrow_id_origins: Option<&HashMap<String, BorrowIdOrigin>>,
    mutation_continued: Option<&HashSet<String>>,
    final_values: Option<&HashMap<String, PureExpr>>,
) {
    // Build the set of children with field projections (skip these for transitivity).
    let has_field_projection = |child: &str| -> bool {
        borrow_id_origins
            .and_then(|origins| origins.get(child))
            .and_then(extract_field_projection_steps)
            .is_some()
    };

    // For each leaf in the writeback graph, walk up to find all ancestors.
    // Only process chains of length >= 2 (at least one intermediate).
    for (leaf_child, immediate_parent) in writebacks {
        if has_field_projection(leaf_child) {
            continue;
        }

        // Walk up the chain from immediate_parent to find grandparent+.
        let mut ancestor = immediate_parent.clone();
        let mut depth = 0;
        while let Some(next_ancestor) = writebacks
            .iter()
            .find(|(child, _)| *child == &ancestor)
            .map(|(_, parent)| parent.clone())
        {
            // Check that intermediate is also an identity reborrow.
            if has_field_projection(&ancestor) {
                break;
            }
            depth += 1;
            // Safety limit to avoid infinite loops in malformed writeback graphs.
            if depth > 10 {
                break;
            }

            let leaf_names = MutRefVarNames::new(leaf_child);
            let ancestor_names = MutRefVarNames::new(&next_ancestor);

            // Transitive writeback: ancestor_current == leaf_final.
            //
            // SKIP when the transitive ancestor is mutation-continued — same
            // rationale as the per-edge writeback skip above. The call
            // assumption already advances `ancestor_final` through the
            // leaf's final, and fusing `ancestor_current` (entry-time) with
            // `leaf_final` (post-call) collapses base premises to UNSAT
            // when a precondition pins the ancestor's current. See bug/682
            // / #5. The `ancestor_final == leaf_final` edge below is kept.
            let ancestor_is_mutation_continued =
                mutation_continued.is_some_and(|mcp| mcp.contains(next_ancestor.as_str()));
            // Spec-advanced ancestors get the same suppression as the
            // per-edge writeback above (bug/two_phase class).
            let ancestor_final_is_advanced = final_values
                .and_then(|fv| fv.get(next_ancestor.as_str()))
                .is_some_and(|expr| !is_identity_final_value(&next_ancestor, expr));
            if !ancestor_is_mutation_continued && !ancestor_final_is_advanced {
                if let (Some(leaf_final), Some(ancestor_current)) = (
                    encoder.var_term(&leaf_names.final_val),
                    encoder.var_term(&ancestor_names.current),
                ) {
                    let leaf_sort = encoder
                        .var_sort(&leaf_names.final_val)
                        .cloned()
                        .unwrap_or(ay_dpll::api::Sort::Int);
                    let ancestor_sort = encoder
                        .var_sort(&ancestor_names.current)
                        .cloned()
                        .unwrap_or(ay_dpll::api::Sort::Int);
                    if sorts_compatible_for_writeback(&leaf_sort, &ancestor_sort) {
                        encoder.assert_eq(ancestor_current, leaf_final);
                    }
                }
            }

            // Transitive final propagation: ancestor_final == leaf_final
            // when ancestor is resolved (ancestor_final == ancestor_current).
            let ancestor_is_resolved =
                resolve_set.is_some_and(|rs| rs.iter().any(|name| name == &next_ancestor));
            if ancestor_is_resolved {
                if let (Some(leaf_final), Some(ancestor_final)) = (
                    encoder.var_term(&leaf_names.final_val),
                    encoder.var_term(&ancestor_names.final_val),
                ) {
                    let leaf_sort = encoder
                        .var_sort(&leaf_names.final_val)
                        .cloned()
                        .unwrap_or(ay_dpll::api::Sort::Int);
                    let ancestor_sort = encoder
                        .var_sort(&ancestor_names.final_val)
                        .cloned()
                        .unwrap_or(ay_dpll::api::Sort::Int);
                    if sorts_compatible_for_writeback(&leaf_sort, &ancestor_sort) {
                        encoder.assert_eq(ancestor_final, leaf_final);
                    }
                }
            }

            ancestor = next_ancestor;
        }
    }
}

/// Extract field projection steps from a `BorrowIdOrigin::Derived`, returning
/// `Some(indices)` if all steps are `Field(n)` projections, `None` otherwise.
fn extract_field_projection_steps(origin: &BorrowIdOrigin) -> Option<Vec<u32>> {
    match origin {
        BorrowIdOrigin::Derived { steps, .. } => {
            let field_indices: Vec<u32> = steps
                .iter()
                .filter_map(|step| match step {
                    BorrowIdStep::Field(idx) => Some(*idx),
                    _ => None,
                })
                .collect();
            // Only use projection if ALL steps are fields and there is at least one.
            if field_indices.len() == steps.len() && !field_indices.is_empty() {
                Some(field_indices)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Emit `child_var == tuple_get_N(... tuple_get_0(parent_var) ...)` for a
/// chain of field projection steps.
///
/// For a single `Field(0)` step, this emits:
///   `child_var == __trust_wp_tuple_get_0(parent_var)`
///
/// For nested projections like `Field(0), Field(1)`, this emits:
///   `child_var == __trust_wp_tuple_get_1(__trust_wp_tuple_get_0(parent_var))`
///
/// `child_sort` is the sort of the child variable (result of the full projection).
/// `parent_sort` is the sort of the parent variable (source of the projection).
fn emit_projected_equality(
    encoder: &mut AYEncoder,
    child_var: ay_dpll::api::Term,
    parent_var: ay_dpll::api::Term,
    field_steps: &[u32],
    child_sort: &ay_dpll::api::Sort,
    parent_sort: &ay_dpll::api::Sort,
) {
    let mut current_term = parent_var;
    let mut current_sort = parent_sort.clone();
    for (i, &field_idx) in field_steps.iter().enumerate() {
        let fn_name = tuple_field_logic_fn_name(field_idx as usize);
        // For the last step, use the child sort as the result sort.
        // For intermediate steps, use Int as a default (tuple nesting
        // with concrete sorts would need the intermediate tuple type,
        // but Int is a safe fallback for the generic case).
        let result_sort = if i == field_steps.len() - 1 {
            child_sort.clone()
        } else {
            ay_dpll::api::Sort::Int
        };
        let func_decl = encoder.get_or_declare_logic_func(
            &fn_name,
            &[current_sort.clone()],
            result_sort.clone(),
        );
        if let Ok(projected) = encoder.safe_apply(&fn_name, &func_decl, &[current_term]) {
            current_term = projected;
            current_sort = result_sort;
        } else {
            // If we cannot apply the projection, skip this constraint rather
            // than panicking. The constraint is an optimization, not required
            // for soundness.
            return;
        }
    }
    encoder.assert_eq(child_var, current_term);
}

fn inherit_id_decl(encoder: &mut AYEncoder) -> ay_dpll::api::FuncDecl {
    encoder.get_or_declare_logic_func(
        "__trust_wp_inherit_id",
        &[
            ay_dpll::api::Sort::Int,
            ay_dpll::api::Sort::Int,
            ay_dpll::api::Sort::Int,
        ],
        ay_dpll::api::Sort::Int,
    )
}

fn encode_inherit_id_chain(
    encoder: &mut AYEncoder,
    parent_id: ay_dpll::api::Term,
    steps: &[BorrowIdStep],
) -> Result<ay_dpll::api::Term, EncodingError> {
    let inherit = inherit_id_decl(encoder);
    let mut current = parent_id;
    for step in steps {
        let (kind, value) = match step {
            BorrowIdStep::Field(index) => (
                encoder.solver.int_const(INHERIT_FIELD_STEP_KIND),
                encoder.solver.int_const(i64::from(*index)),
            ),
            BorrowIdStep::Index(expr) => (
                encoder.solver.int_const(INHERIT_INDEX_STEP_KIND),
                encoder.encode_pure(expr)?,
            ),
            _ => {
                return Err(EncodingError::unsupported(format!(
                    "unsupported borrow-id step in inherit_id chain: {step:?}"
                )));
            }
        };
        current = encoder.safe_apply("inherit_id", &inherit, &[current, kind, value])?;
    }
    Ok(current)
}

/// Emit borrow-id equalities/disequalities for reborrows. (#2141)
pub(super) fn emit_borrow_id_constraints(
    encoder: &mut AYEncoder,
    origins: Option<&HashMap<String, BorrowIdOrigin>>,
    _writebacks: Option<&HashMap<String, String>>,
) -> Result<(), EncodingError> {
    let Some(origins) = origins else {
        return Ok(());
    };

    let mut fresh_id_terms = Vec::new();

    for (child_name, origin) in origins {
        let child_names = MutRefVarNames::new(child_name);
        let Some(child_id) = encoder.var_term(&child_names.id) else {
            continue;
        };
        match origin {
            BorrowIdOrigin::Fresh { parent } => {
                let parent_names = MutRefVarNames::new(parent);
                if let Some(parent_id) = encoder.var_term(&parent_names.id) {
                    let eq = encoder.eq_term(child_id, parent_id);
                    let neq = encoder.solver.not(eq);
                    encoder.assert_term(neq);
                }
                fresh_id_terms.push(child_id);
            }
            BorrowIdOrigin::SameParent { parent } => {
                let parent_names = MutRefVarNames::new(parent);
                if let Some(parent_id) = encoder.var_term(&parent_names.id) {
                    encoder.assert_eq(child_id, parent_id);
                }
            }
            BorrowIdOrigin::Derived { parent, steps } => {
                let parent_names = MutRefVarNames::new(parent);
                if let Some(parent_id) = encoder.var_term(&parent_names.id) {
                    let derived_id = encode_inherit_id_chain(encoder, parent_id, steps)?;
                    encoder.assert_eq(child_id, derived_id);
                }
            }
            _ => {
                return Err(EncodingError::unsupported(format!(
                    "unsupported borrow-id origin variant: {origin:?}"
                )));
            }
        }
    }

    for (idx, lhs) in fresh_id_terms.iter().enumerate() {
        for rhs in fresh_id_terms.iter().skip(idx + 1) {
            let eq = encoder.eq_term(*lhs, *rhs);
            let neq = encoder.solver.not(eq);
            encoder.assert_term(neq);
        }
    }

    Ok(())
}
