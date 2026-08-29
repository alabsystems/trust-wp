// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Prime variable construction for loop verification.
//!
//! Provides:
//! - [`sort_to_expr_sort`]: ay Sort → PureExpr ExprSort conversion
//! - [`build_prime_substitutions`]: Prime variable proxies for preservation/variant
//! - [`assert_deref_prophecy_bridge`]: Prophecy continuity for deref body effects

use std::collections::HashMap;

use ay_dpll::api::{Sort, Term};
use trust_wp_core::formula::{
    internal::tuple_lowering::tuple_field_logic_fn_name, ExprSort, PureExpr,
};

use super::{encoder_setup::LoopSortPlan, BodyEffects};
use crate::{
    encoder::{sort_context::DerivedKind, AYEncoder},
    error::EncodingError,
};

/// Convert a ay `Sort` to an `ExprSort` annotation for `PureExpr::Var`.
///
/// Returns `None` for `Sort::Int` (the default) to maintain backward compatibility
/// with existing code that treats `None` as Int. Delegates to the shared
/// `ay_sort_to_expr_sort` in sort_inference which handles all ExprSort variants
/// including Datatype, FMap, Tuple, and Unit. (#994 Step 2e, #2040)
pub(in crate::verify::loops) fn sort_to_expr_sort(
    sort: &Sort,
) -> Option<trust_wp_core::formula::ExprSort> {
    crate::encoder::sort_context::ay_sort_to_expr_sort(sort)
}

/// Introduce proxy variables for body effects and return prime substitution map.
///
/// Instead of substituting body effects directly into invariants (creating
/// compound arithmetic terms like `add(i,1)` inside comparisons), we declare
/// named proxy variables: `var_prime = body_effect[var]`. The primed invariant
/// then uses simple variable references that ay's LIA solver handles reliably.
///
/// Source-variable sorts come from the caller-provided [`LoopSortPlan`]. Only
/// derived helper names such as `*_current` still consult encoder fallback
/// resolution inside this helper.
///
/// When a variable is in `modified_vars` but NOT in `body_effect`, we declare
/// an unconstrained (havoced) prime variable. This prevents false accepts where
/// the primed invariant would otherwise reference the original unprimed variable,
/// making preservation trivially true. (#740)
///
/// For deref body effects (`*x = expr`), the variable `x` (a mutable reference)
/// is not itself modified — only the pointed-to value changes. We constrain
/// `x_prime_current = expr` (the SMT name for `Deref(Var("x_prime"))`) so that
/// the primed invariant can reason about the new pointed-to value. (#1295)
pub(in crate::verify::loops) fn build_prime_substitutions(
    encoder: &mut AYEncoder,
    sort_plan: &LoopSortPlan,
    modified_vars: &[&str],
    effects: BodyEffects<'_>,
) -> Result<HashMap<String, PureExpr>, EncodingError> {
    let mut prime_substitutions = HashMap::new();
    let planned_modified_sort = |name: &str, encoder: &mut AYEncoder| {
        sort_plan
            .sort_for(name)
            .cloned()
            .unwrap_or_else(|| encoder.resolve_var_sort_or_int(name))
    };
    for var in modified_vars {
        let prime_name = DerivedKind::Prime.format_name(var);
        // Cons-tail loop-carried `&mut` (`loop_l = next`, lowered to the
        // self-referential reborrow `Deref(tuple_get_1(Deref(Var(loop_l))))`):
        // model the primed cursor as a REFERENCE. The default value-sorted prime
        // var makes `Final(loop_l_prime)` COLLAPSE to the bare current tail, so
        // the primed invariant's prophecy `get(^loop_l, i)` silently becomes
        // `get(current_tail, i)` — inconsistent with the assumed antecedent (which
        // correctly uses the prophecy `^loop_l`), and preservation cannot close.
        // Annotating `loop_l_prime` as `&mut` routes `Final` to the genuine
        // prophecy var `loop_l_prime_final` (linked to `^next` by the driver's G4
        // bridge fact) while current-value uses (`len(loop_l_prime)`) resolve to
        // `loop_l_prime_current`, which we pin to the reborrowed tail value.
        // SOUND: `loop_l_prime_current == current tail` (the new cursor's current
        // value IS the reborrowed tail) and `^loop_l_prime == ^next` (same borrow
        // after the move) are both genuine identities. (#994 all_zero_list)
        if let Some(effect_expr) = effects.direct.get(*var) {
            if is_cons_tail_self_reborrow(effect_expr, var) {
                let value_sort = planned_modified_sort(var, encoder);
                encoder.get_or_declare_var(&prime_name, value_sort.clone())?;
                let cur_name = DerivedKind::Current.format_name(&prime_name);
                let cur_var = encoder.get_or_declare_var(&cur_name, value_sort.clone())?;
                // The Option-layer form (`unwrap(tuple_get_1(*var))`) yields the
                // Box-sorted payload; wrap in Deref (the transparent Box strip)
                // so the pinning equation is value-sorted like the match-shape
                // effect `Deref(tuple_get_1(*var))` — without it the equation
                // coerces to a fresh constant and the primed cursor stays free.
                // (#counter-cons-tail)
                let normalized_effect = if matches!(effect_expr, PureExpr::MethodCall { .. }) {
                    PureExpr::Deref(std::sync::Arc::new(effect_expr.clone()))
                } else {
                    effect_expr.clone()
                };
                let effect_term = encoder.encode_pure(&normalized_effect)?;
                encoder.assert_eq(cur_var, effect_term);
                let inner = sort_to_expr_sort(&value_sort).unwrap_or(ExprSort::Int);
                prime_substitutions.insert(
                    (*var).to_string(),
                    PureExpr::Var(prime_name, Some(ExprSort::MutRef(Box::new(inner)))),
                );
                continue;
            }
        }
        let sort = if let Some(effect_expr) = effects.direct.get(*var) {
            let sort = planned_modified_sort(var, encoder);
            let prime_var = encoder.get_or_declare_var(&prime_name, sort.clone())?;
            let normalized_effect = normalize_direct_body_effect(effect_expr, &sort);
            let effect_term = encoder.encode_pure(&normalized_effect)?;
            encoder.assert_eq(prime_var, effect_term);
            assert_seq_prime_len_bridge(encoder, prime_var, &normalized_effect, &sort)?;
            register_fmap_insert_alias_ground_application(
                encoder,
                prime_var,
                &normalized_effect,
                &sort,
            )?;
            sort
        } else if let Some(deref_effect_expr) = effects.deref.get(*var) {
            // Deref body effect: `*var = expr` in the loop body. (#1295)
            //
            // The reference `var` itself doesn't change, but the pointed-to value
            // does. Declare `var_prime` (the primed reference) and constrain
            // `var_prime_current` (its dereference in SMT) to the written value.
            //
            // After substitution, `Deref(Var("x"))` in the invariant becomes
            // `Deref(Var("x_prime"))`, which the encoder resolves to `x_prime_current`.
            // By constraining `x_prime_current = deref_effect`, preservation can
            // succeed when the invariant talks about `*x`.
            let sort = planned_modified_sort(var, encoder);
            let prime_var = encoder.get_or_declare_var(&prime_name, sort.clone())?;
            // Constrain the dereference of the primed variable
            let deref_prime_name = DerivedKind::Current.format_name(&prime_name);
            let deref_sort = if encoder.is_bool_var(var) {
                Sort::Bool
            } else {
                // Context-aware inference for deref effects. (#1965)
                encoder.infer_expr_sort_with_context(deref_effect_expr, None)
            };
            let deref_prime_var =
                encoder.get_or_declare_var(&deref_prime_name, deref_sort.clone())?;
            let deref_effect_term = encoder.encode_pure(deref_effect_expr)?;
            encoder.assert_eq(deref_prime_var, deref_effect_term);
            // Collection specs can mention `x[index]` directly on an `&mut`
            // parameter. That encodes through the primed receiver `x_prime`,
            // while deref effects constrain `x_prime_current`. In the RustHorn
            // value encoding these have the same carrier sort for collection
            // pointees, so bridge them when the sorts agree.
            let prime_sort = encoder.solver.get_sort(prime_var);
            if prime_sort == deref_sort {
                encoder.assert_eq(prime_var, deref_prime_var);
            } else if crate::encoder::sort_context::same_structural_family(&prime_sort, &deref_sort)
                .is_some()
            {
                // &mut Option / &mut Result final-value bridge. The reference
                // carrier `x_prime` lives in the uninterpreted ref sort (e.g.
                // `Option`) while the written deref value `x_prime_current`
                // lives in the datatype sort (e.g. `OptionInt`). These are the
                // SAME final value seen through two representations; without
                // linking them, loop_preservation has a free
                // `bridge(x_prime)` and the negated goal
                // `bridge(x_prime) != <written value>` stays SAT (a spurious
                // counterexample). `assert_eq` routes through
                // `harmonize_eq_or_ite_terms`, which detects the shared
                // structural family and emits the injective UF bridge equality
                // `bridge(x_prime) == x_prime_current` — the &mut analogue of
                // the already-emitted `bridge(x_current) == <current value>`.
                // This is the missing final-value bridge for Option/Result
                // references in deref body effects (`lang/while_let.rs`). It
                // only ever ADDS a sound equality between two encodings of one
                // Rust value; it cannot make an otherwise-SAT obligation UNSAT
                // unless the goal truly follows from the written value.
                encoder.assert_eq(prime_var, deref_prime_var);
            }
            sort
        } else if let Some(double_deref_effect_expr) = effects.double_deref.get(*var) {
            // Double-deref body effect: `**var = expr` in the loop body. (#1295)
            //
            // For `x: &mut &mut i32` with `**x = 0`, the invariant `**x == 0`
            // becomes `Deref(Deref(Var("x_prime")))` after substitution, which
            // the encoder resolves to `x_prime_current_current`.
            //
            // We need to declare the full chain:
            //   x_prime (reference handle, resolved sort)
            //   x_prime_current (first deref, resolved current sort)
            //   x_prime_current_current (second deref, constrained to effect)
            let sort = planned_modified_sort(var, encoder);
            encoder.get_or_declare_var(&prime_name, sort.clone())?;
            // Intermediate deref level
            let mid_prime_name = DerivedKind::Current.format_name(&prime_name);
            let mid_source_name = DerivedKind::Current.format_name(var);
            let resolved_mid_sort = encoder.resolve_var_sort_or_int(&mid_source_name);
            let mid_sort = if resolved_mid_sort == Sort::Int {
                sort.clone()
            } else {
                resolved_mid_sort
            };
            encoder.get_or_declare_var(&mid_prime_name, mid_sort)?;
            // Constrain the double-dereference of the primed variable
            let double_deref_prime_name =
                DerivedKind::Current.format_name(&DerivedKind::Current.format_name(&prime_name));
            let deref_sort = if encoder.is_bool_var(var) {
                Sort::Bool
            } else {
                // Context-aware inference for double-deref effects. (#1965)
                encoder.infer_expr_sort_with_context(double_deref_effect_expr, None)
            };
            let double_deref_prime_var =
                encoder.get_or_declare_var(&double_deref_prime_name, deref_sort.clone())?;
            let deref_effect_term = encoder.encode_pure(double_deref_effect_expr)?;
            encoder.assert_eq(double_deref_prime_var, deref_effect_term);
            sort
        } else {
            // Havoc: variable is modified but effect is unknown. Declare an
            // unconstrained prime variable so the solver must prove the invariant
            // holds for ANY possible post-iteration value. (#740, #1608)
            let sort = planned_modified_sort(var, encoder);
            encoder.get_or_declare_var(&prime_name, sort.clone())?;
            sort
        };
        // Propagate ExprSort annotation so primed variables in substituted
        // invariants carry correct type information for register_sort_hints
        // and encode_pure. Without this, Seq-typed primed vars default to Int,
        // causing ay sort mismatch panics. (#1301)
        let expr_sort = sort_to_expr_sort(&sort);
        prime_substitutions.insert((*var).to_string(), PureExpr::Var(prime_name, expr_sort));
    }
    Ok(prime_substitutions)
}

/// A loop-carried `&mut` advanced by `loop_l = next` lowers to the
/// self-referential cons-tail reborrow `Deref(tuple_get_1(Deref(Var(var))))`
/// (deref the `&mut`, take the recursive `Cons.1` field, deref the `Box`). Only
/// this exact self-referential shape triggers reference-modeling of the primed
/// cursor, so a non-cons-tail direct effect keeps the original value modeling.
pub(in crate::verify::loops) fn is_cons_tail_self_reborrow(effect: &PureExpr, var: &str) -> bool {
    match effect {
        // `Deref(tuple_get_1(Deref(var)))` — the match-destructuring shape
        // (`while let Cons(v, n) = l { l = n }`, Box field direct).
        PureExpr::Deref(inner) => is_recursive_field_of_self(inner, var),
        // `unwrap(tuple_get_1(Deref(var)))` — the Option-layer counter-driven
        // shape (`l = l.1.as_mut().unwrap()` on `List(u32, Option<Box<List>>)`),
        // produced by the Option-adapter call modeling (#counter-cons-tail).
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == "unwrap" && args.is_empty() => is_recursive_field_of_self(receiver, var),
        _ => false,
    }
}

/// `tuple_get_1(Deref(Var(var)))` — the recursive tail field of the loop
/// cursor's own referent.
fn is_recursive_field_of_self(expr: &PureExpr, var: &str) -> bool {
    let PureExpr::LogicFnCall { name, args } = expr else {
        return false;
    };
    if *name != tuple_field_logic_fn_name(1) || args.len() != 1 {
        return false;
    }
    let PureExpr::Deref(d) = &args[0] else {
        return false;
    };
    matches!(d.as_ref(), PureExpr::Var(v, _) if v == var)
}

fn normalize_direct_body_effect(effect_expr: &PureExpr, effect_sort: &Sort) -> PureExpr {
    if *effect_sort != Sort::Int {
        return effect_expr.clone();
    }
    value_projection_arg(effect_expr)
        .cloned()
        .unwrap_or_else(|| effect_expr.clone())
}

fn value_projection_arg(expr: &PureExpr) -> Option<&PureExpr> {
    let PureExpr::LogicFnCall { name, args } = expr else {
        return None;
    };
    (name == "__trust_wp_tuple_get_0" && args.len() == 1).then_some(&args[0])
}

fn assert_seq_prime_len_bridge(
    encoder: &mut AYEncoder,
    prime_var: Term,
    effect_expr: &PureExpr,
    effect_sort: &Sort,
) -> Result<(), EncodingError> {
    if *effect_sort != Sort::seq(Sort::Int) {
        return Ok(());
    }

    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = effect_expr
    else {
        return Ok(());
    };
    if !matches!(method.as_str(), "push_back" | "push_front") || args.len() != 1 {
        return Ok(());
    }

    let receiver_term = encoder.encode_pure(receiver)?;
    let prime_len = encoder.seq_len_term(prime_var)?;
    let receiver_len = encoder.seq_len_term(receiver_term)?;
    let one = encoder.solver.int_const(1);
    let receiver_len_plus_one = encoder.solver.add(receiver_len, one);
    encoder.assert_eq(prime_len, receiver_len_plus_one);
    Ok(())
}

fn register_fmap_insert_alias_ground_application(
    encoder: &mut AYEncoder,
    alias_term: ay_dpll::api::Term,
    effect_expr: &PureExpr,
    effect_sort: &Sort,
) -> Result<(), EncodingError> {
    if *effect_sort != Sort::Uninterpreted("FMap".to_string()) {
        return Ok(());
    }

    let (receiver_expr, key_expr, value_expr) = match effect_expr {
        PureExpr::MethodCall {
            receiver,
            method,
            args,
        } if method == "insert" && args.len() == 2 => (receiver.as_ref(), &args[0], &args[1]),
        PureExpr::LogicFnCall { name, args } if name == "fmap_insert" && args.len() == 3 => {
            (&args[0], &args[1], &args[2])
        }
        _ => return Ok(()),
    };

    let receiver_term = encoder.encode_pure(receiver_expr)?;
    let key_term = encoder.encode_pure(key_expr)?;
    let value_term = encoder.encode_pure(value_expr)?;
    encoder.register_standard_ground_application(
        "fmap_insert",
        alias_term,
        vec![receiver_term, key_term, value_term],
    );
    Ok(())
}

/// Assert prophecy continuity and loop-body borrow resolution for deref effects (#2116).
///
/// For mutable references with deref body effects (`*var = expr`):
/// 1. **Prophecy continuity**: `var_final == var_prime_final`. A deref write
///    changes the pointee but not the reference identity, so the Final (prophecy)
///    is the same before and after the body step.
/// 2. **Deref-current constraint** (dual-effect variables): When a variable has
///    BOTH a direct body effect (e.g., `k2 = elem.0`) and a deref body effect
///    (e.g., `*k2 = 1`), `build_prime_substitutions` only handles the direct
///    effect. We fill the gap by constraining `var_prime_current = deref_expr`.
/// 3. **Borrow resolution** (loop elements only): `var_prime_final == var_prime_current`.
///    For consuming iterators (e.g., FMap `into_iter`), the yielded element is
///    consumed at end of iteration. The Final equals the last written value.
///
/// Together these give `var_final == var_prime_current == deref_effect_value`,
/// which the FMap identity bridge can connect to pre-loop borrow Finals.
pub(in crate::verify::loops) fn assert_deref_prophecy_bridge(
    encoder: &mut AYEncoder,
    effects: BodyEffects<'_>,
    loop_element_borrow_vars: &[String],
) -> Result<(), EncodingError> {
    for (var, deref_effect_expr) in effects.deref {
        let prime_name = DerivedKind::Prime.format_name(var);
        let final_name = DerivedKind::Final.format_name(var);
        let prime_final_name = DerivedKind::Final.format_name(&prime_name);
        let deref_prime_name = DerivedKind::Current.format_name(&prime_name);

        // Infer the sort from the existing current-of-prime variable (already
        // declared by build_prime_substitutions).
        let sort = encoder.resolve_var_sort_or_int(&deref_prime_name);

        // Prophecy continuity: var_final == var_prime_final
        let final_var = encoder.get_or_declare_var(&final_name, sort.clone())?;
        let prime_final_var = encoder.get_or_declare_var(&prime_final_name, sort.clone())?;
        encoder.assert_eq(final_var, prime_final_var);

        // When a variable has BOTH direct and deref body effects (e.g., FMap
        // destructuring `k2 = elem.0` plus mutation `*k2 = 1`),
        // build_prime_substitutions handles only the direct effect. Ensure
        // var_prime_current is constrained to the deref effect value.
        if effects.direct.contains_key(var) {
            let deref_sort = encoder.infer_expr_sort_with_context(deref_effect_expr, None);
            let deref_prime_var = encoder.get_or_declare_var(&deref_prime_name, deref_sort)?;
            let deref_effect_term = encoder.encode_pure(deref_effect_expr)?;
            encoder.assert_eq(deref_prime_var, deref_effect_term);
        }

        // Borrow resolution for loop element variables:
        // var_prime_final == var_prime_current
        if loop_element_borrow_vars.iter().any(|v| v == var) {
            let deref_prime_var = encoder.get_or_declare_var(&deref_prime_name, sort)?;
            encoder.assert_eq(prime_final_var, deref_prime_var);
        }
    }
    Ok(())
}
