// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ntest::timeout;

use super::*;

// resolve_var_sort_or_int: suffix-based sort propagation (#1608)
// =============================================================================

/// resolve_var_sort_or_int returns Bool when the base var has a Bool hint,
/// even for suffix-derived names like `v_current` or `v_final`. (#1608)
#[test]
#[timeout(30000)]
fn resolve_var_sort_or_int_propagates_bool_from_base() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Register "v" as Bool via sort hint
    let expr = not(var("v"));
    encoder.register_sort_hints(std::slice::from_ref(&expr));

    // Suffix-derived names should inherit Bool from base
    assert_eq!(
        encoder.resolve_var_sort_or_int("v"),
        Sort::Bool,
        "Direct name should resolve to Bool"
    );
    assert_eq!(
        encoder.resolve_var_sort_or_int("v_current"),
        Sort::Bool,
        "v_current should inherit Bool from base v (#1608)"
    );
    assert_eq!(
        encoder.resolve_var_sort_or_int("v_final"),
        Sort::Bool,
        "v_final should inherit Bool from base v (#1608)"
    );
    assert_eq!(
        encoder.resolve_var_sort_or_int("v_current_final"),
        Sort::Bool,
        "v_current_final should strip both suffixes to find Bool base (#1608)"
    );
}

/// resolve_var_sort_or_int prefers already-declared sorts over hints. (#1608)
#[test]
#[timeout(30000)]
fn resolve_var_sort_or_int_prefers_declared_sort() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // Declare "x" with a specific sort
    let sort = Sort::Uninterpreted("UserOption".to_string());
    encoder
        .get_or_declare_var("x", sort.clone())
        .expect("declare x");

    // x_current should inherit from declared "x"
    assert_eq!(
        encoder.resolve_var_sort_or_int("x_current"),
        sort,
        "x_current should inherit a custom uninterpreted sort from x (#1608)"
    );
}

/// Regression for #1805: an exact-name Int declaration is a weak default and
/// should be promoted by a stronger exact-name hint.
#[test]
#[timeout(30000)]
fn resolve_var_sort_or_int_promotes_exact_hint_over_declared_int() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder
        .get_or_declare_var("flag_current", Sort::Int)
        .expect("declare flag_current as Int default");
    encoder.record_sort_hint("flag_current".to_string(), ExprSort::Bool);

    assert_eq!(
        encoder.resolve_var_sort_or_int("flag_current"),
        Sort::Bool,
        "exact Bool hint should override stale declared Int on same name"
    );
}

/// Regression for #1805: `old_`-prefixed names should fall back to unprefixed
/// hints when prefixed aliases only resolve to weak Int defaults.
#[test]
#[timeout(30000)]
fn resolve_var_sort_or_int_old_prefix_falls_back_to_unprefixed_hint_1805() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder
        .get_or_declare_var("old_s", Sort::Int)
        .expect("declare old_s as Int default");
    encoder.record_sort_hint("s".to_string(), ExprSort::Seq);

    assert_eq!(
        encoder.resolve_var_sort_or_int("old_s_current"),
        Sort::seq(Sort::Int),
        "old_s_current should fall back to unprefixed Seq hint when prefixed path is Int-only"
    );
}

/// Regression for #1805: when a prefixed hint is present, it should take
/// precedence over the unprefixed fallback path.
#[test]
#[timeout(30000)]
fn resolve_var_sort_or_int_prefers_prefixed_hint_before_unprefixed_fallback_1805() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder.record_sort_hint("old_s".to_string(), ExprSort::Bool);
    encoder.record_sort_hint("s".to_string(), ExprSort::Seq);

    assert_eq!(
        encoder.resolve_var_sort_or_int("old_s_current"),
        Sort::Bool,
        "prefixed old_s hint should win over unprefixed fallback hints"
    );
}

/// Regression for #1805: stale Int metadata on the derived deref name should
/// be promoted by a stronger base-name hint during declaration.
#[test]
#[timeout(30000)]
fn resolve_deref_sort_promotes_base_hint_over_stale_derived_int_metadata() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    // Simulate stale metadata before SMT declaration (`vars` has no term yet).
    encoder
        .var_sorts_mut_for_test()
        .insert("s_current".to_string(), Sort::Int);
    encoder.record_sort_hint("s".to_string(), ExprSort::Seq);

    let result = encoder.encode_pure(&deref(var("s")));
    assert!(
        result.is_ok(),
        "deref with base Seq hint should encode successfully: {result:?}"
    );
    match encoder.var_sort("s_current") {
        Some(s) if s.is_seq() => {}
        other => {
            panic!("base Seq hint should override stale Int metadata for s_current, got {other:?}")
        }
    }
}

/// Regression for #1805: when the base variable is already declared as Int
/// (untyped default), a stronger Bool hint on the base must still drive the
/// derived deref name sort (`b_current`). Otherwise `mk_eq(Int, Bool)` can panic.
#[test]
#[timeout(30000)]
fn resolve_deref_sort_prefers_base_bool_hint_over_declared_int() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder
        .get_or_declare_var("b", Sort::Int)
        .expect("declare base var b as Int default");
    encoder.record_sort_hint("b".to_string(), ExprSort::Bool);

    let result = encoder.encode_pure(&deref(var("b")));
    assert!(
        result.is_ok(),
        "Deref base with Bool hint should encode without sort mismatch: {result:?}"
    );
    match encoder.var_sort("b_current") {
        Some(Sort::Bool) => {}
        other => panic!("expected b_current to resolve Bool from base hint, got {other:?}"),
    }
}

/// Regression for #1805: Seq hints on a base var must also override a stale
/// declared Int base when deriving `_current` names. This prevents
/// `mk_eq(Int, Seq)` mismatches for deref/view aliases.
#[test]
#[timeout(30000)]
fn resolve_deref_sort_prefers_base_seq_hint_over_declared_int() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder
        .get_or_declare_var("s", Sort::Int)
        .expect("declare base var s as Int default");
    encoder.record_sort_hint("s".to_string(), ExprSort::Seq);

    let result = encoder.encode_pure(&deref(var("s")));
    assert!(
        result.is_ok(),
        "Deref base with Seq hint should encode without sort mismatch: {result:?}"
    );
    match encoder.var_sort("s_current") {
        Some(s) if s.is_seq() => {}
        other => panic!("expected s_current to resolve Seq from base hint, got {other:?}"),
    }
}

/// Regression for #1805: View aliases must honor base Bool hints even when the
/// base variable is already declared as Int. This prevents `mk_eq(Int, Bool)`
/// mismatches on `*_view` names.
#[test]
#[timeout(30000)]
fn resolve_view_sort_prefers_base_bool_hint_over_declared_int() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder
        .get_or_declare_var("b", Sort::Int)
        .expect("declare base var b as Int default");
    encoder.record_sort_hint("b".to_string(), ExprSort::Bool);

    let result = encoder.encode_pure(&view(var("b")));
    assert!(
        result.is_ok(),
        "View base with Bool hint should encode without sort mismatch: {result:?}"
    );
    match encoder.var_sort("b_view") {
        Some(Sort::Bool) => {}
        other => panic!("expected b_view to resolve Bool from base hint, got {other:?}"),
    }
}

/// Regression for #1805: View aliases must also promote Seq hints from the
/// base variable over stale declared Int defaults.
#[test]
#[timeout(30000)]
fn resolve_view_sort_prefers_base_seq_hint_over_declared_int() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder
        .get_or_declare_var("s", Sort::Int)
        .expect("declare base var s as Int default");
    encoder.record_sort_hint("s".to_string(), ExprSort::Seq);

    let result = encoder.encode_pure(&view(var("s")));
    assert!(
        result.is_ok(),
        "View base with Seq hint should encode without sort mismatch: {result:?}"
    );
    match encoder.var_sort("s_view") {
        Some(s) if s.is_seq() => {}
        other => panic!("expected s_view to resolve Seq from base hint, got {other:?}"),
    }
}

/// Regression for #1805/#994: a synthesized view hint must not override a
/// stronger declared carrier on the base variable.
#[test]
#[timeout(30000)]
fn resolve_view_sort_prefers_base_declared_fmap_over_conflicting_seq_hint() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let fmap = Sort::Uninterpreted("FMap".to_string());
    encoder
        .get_or_declare_var("m", fmap.clone())
        .expect("declare base var m as FMap");
    encoder.record_sort_hint("m_view".to_string(), ExprSort::Seq);

    assert_eq!(
        encoder.resolve_var_sort_or_int("m_view"),
        fmap,
        "m_view should resolve to the declared FMap carrier, not the stale Seq hint"
    );
}

/// Regression for #1805: `is_seq_receiver` in prefixed contexts should fall
/// back to unprefixed hints when the prefixed key is absent.
///
/// This covers both bare variables and normalized view names:
/// - `old(s)` should still be treated as Seq if only `s` is hinted Seq.
/// - `old(s@)` should still be treated as Seq if only `s_view` is hinted Seq.
#[test]
#[timeout(30000)]
fn is_seq_receiver_prefixed_context_falls_back_to_unprefixed_hints_1805() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder.record_sort_hint("s".to_string(), ExprSort::Seq);
    encoder.record_sort_hint("s_view".to_string(), ExprSort::Seq);

    assert!(
        encoder.is_seq_receiver(
            &var("s"),
            Some(crate::encoder::sort_context::DerivedKind::Old)
        ),
        "old-prefixed bare var should inherit Seq hint from unprefixed base"
    );
    assert!(
        encoder.is_seq_receiver(
            &view(var("s")),
            Some(crate::encoder::sort_context::DerivedKind::Old)
        ),
        "old-prefixed view var should inherit Seq hint from unprefixed view name"
    );
}

/// resolve_var_sort_or_int falls back to Int for genuinely unknown variables. (#1608)
#[test]
#[timeout(30000)]
fn resolve_var_sort_or_int_falls_back_to_int() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    assert_eq!(
        encoder.resolve_var_sort_or_int("unknown_var"),
        Sort::Int,
        "Unknown variable with no hints should fall back to Int"
    );
}

/// Seq hint propagation: `final_{x}_view` → `{x}_view`, `{x}`. (#994)
///
/// When `(^self).len()` appears in a contract, the prescan tags
/// `final_self_view` as Seq but skips bare `Var("self")` (ambiguous
/// method guard). The propagation in `register_sort_hints` should
/// back-propagate to `self_view` and `self`, so that `self` gets
/// declared as Seq sort instead of defaulting to Int.
#[test]
#[timeout(30000)]
fn register_sort_hints_propagates_final_view_seq_to_base_994() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // (^self).len() → prescan detects Final(Var("self")) as Seq receiver,
    // which normalizes to View(Final(Var("self"))) → "final_self_view" Seq hint.
    // But bare self.len() is excluded by the ambiguous-method guard.
    let exprs = vec![
        method_call(final_expr(var("self")), "len", vec![]),
        method_call(var("self"), "len", vec![]),
    ];
    encoder.register_sort_hints(&exprs);

    // Verify: final_self_view should have Seq hint (direct detection)
    assert!(
        matches!(
            encoder
                .sort_resolver_for_test()
                .get_sort_hint("final_self_view"),
            Some(ExprSort::Seq)
        ),
        "final_self_view should have Seq hint from direct detection"
    );
    // Verify: self_view should have Seq hint (propagated)
    assert!(
        matches!(
            encoder.sort_resolver_for_test().get_sort_hint("self_view"),
            Some(ExprSort::Seq)
        ),
        "self_view should have Seq hint propagated from final_self_view"
    );
    // Verify: self should have Seq hint (propagated)
    assert!(
        matches!(
            encoder.sort_resolver_for_test().get_sort_hint("self"),
            Some(ExprSort::Seq)
        ),
        "bare 'self' should have Seq hint propagated from self_view"
    );

    // Verify: is_seq_receiver now returns true for bare Var("self")
    assert!(
        encoder.is_seq_receiver(&var("self"), None),
        "bare Var(self) should be recognized as Seq receiver after propagation"
    );
}

// ---------------------------------------------------------------------------
// classify_var_name / is_derived_var_name classification (#2020 Slice 3)
// ---------------------------------------------------------------------------

/// Derived-name classifier: known suffixes. (#2020 Slice 3)
#[test]
#[timeout(30000)]
fn is_derived_var_name_recognizes_suffixes() {
    assert!(is_derived_var_name("x_view"), "_view suffix");
    assert!(is_derived_var_name("final_x_view"), "final_ + _view");
    assert!(is_derived_var_name("x_current_view"), "_current + _view");
    assert!(is_derived_var_name("x_current"), "_current suffix");
    assert!(is_derived_var_name("x_final"), "_final suffix");
    assert!(is_derived_var_name("x_prime"), "_prime suffix");
    assert!(
        is_derived_var_name("x_current_final"),
        "chained _current_final"
    );
    assert!(
        is_derived_var_name("x_prime_current"),
        "chained _prime_current"
    );
}

/// Derived-name helper can compose the remaining composite name shapes from
/// #2020 without ad hoc formatting at each call site.
#[test]
#[timeout(30000)]
fn derived_kind_format_chain_supports_composite_names() {
    assert_eq!(
        DerivedKind::format_chain("v", &[DerivedKind::Current, DerivedKind::Final]),
        "v_current_final"
    );
    assert_eq!(
        DerivedKind::format_chain("v", &[DerivedKind::FinalPrefix, DerivedKind::View]),
        "final_v_view"
    );
    assert_eq!(
        DerivedKind::format_chain("v_current", &[DerivedKind::FinalPrefix, DerivedKind::View],),
        "final_v_current_view"
    );
}

/// `strip_from` also peels the intermediate `final_{x}` layer needed by
/// `final_{x}_view` names while leaving top-level classification conservative.
#[test]
#[timeout(30000)]
fn derived_kind_strip_from_peels_final_view_intermediate() {
    assert_eq!(
        DerivedKind::strip_from("final_v_view"),
        Some((DerivedKind::View, "final_v"))
    );
    assert_eq!(
        DerivedKind::strip_from("final_v"),
        Some((DerivedKind::FinalPrefix, "v"))
    );
    assert_eq!(
        classify_var_name("final_v"),
        None,
        "top-level classification should not treat final_ prefix alone as derived"
    );
}

/// View-chain helper strips only the nested `final_` layer while preserving
/// the remaining derived-name suffix chain. (#2020)
#[test]
#[timeout(30000)]
fn derived_kind_peel_final_view_prefix_preserves_inner_suffixes() {
    assert_eq!(
        DerivedKind::peel_final_view_prefix("final_v_view"),
        Some("v_view".to_string())
    );
    assert_eq!(
        DerivedKind::peel_final_view_prefix("final_v_current_view"),
        Some("v_current_view".to_string())
    );
    assert_eq!(
        DerivedKind::peel_final_view_prefix("final_old_v_view"),
        Some("old_v_view".to_string())
    );
    assert_eq!(
        DerivedKind::peel_final_view_prefix("v_current_view"),
        None,
        "non-final view chains should not peel"
    );
}

/// Repeated old-prefix peeling stays inside the derived-name helper boundary.
#[test]
#[timeout(30000)]
fn derived_kind_peel_old_prefixes_supports_nested_old_chains() {
    let peeled: Vec<_> = DerivedKind::peel_old_prefixes("old_old_v_current").collect();
    assert_eq!(peeled, vec!["old_v_current", "v_current"]);

    let single: Vec<_> = DerivedKind::peel_old_prefixes("old_v").collect();
    assert_eq!(single, vec!["v"]);

    let none: Vec<_> = DerivedKind::peel_old_prefixes("v_current").collect();
    assert!(none.is_empty(), "non-old names should not peel");
}

/// Mixed old_ + suffix names must still peel the prefix before the suffix
/// cascade runs. `strip_from` cannot replace this helper because it gives the
/// outer suffix priority. (#2020)
#[test]
#[timeout(30000)]
fn derived_kind_peel_old_prefixes_preserves_suffixed_names() {
    let current: Vec<_> = DerivedKind::peel_old_prefixes("old_v_current").collect();
    assert_eq!(current, vec!["v_current"]);

    let view: Vec<_> = DerivedKind::peel_old_prefixes("old_v_view").collect();
    assert_eq!(view, vec!["v_view"]);
}

/// Derived-name classifier: old_ prefix. (#2020 Slice 3)
#[test]
#[timeout(30000)]
fn is_derived_var_name_recognizes_old_prefix() {
    assert!(is_derived_var_name("old_x"), "old_ prefix");
    assert!(
        is_derived_var_name("old_x_current"),
        "old_ prefix + _current suffix"
    );
    assert!(is_derived_var_name("old_old_x"), "double old_ prefix");
}

/// Source names: no known suffix or prefix. (#2020 Slice 3)
#[test]
#[timeout(30000)]
fn is_derived_var_name_rejects_source_names() {
    assert!(!is_derived_var_name("x"), "bare source name");
    assert!(!is_derived_var_name("counter"), "bare source name");
    assert!(!is_derived_var_name("result"), "bare source name");
    assert!(
        !is_derived_var_name("arm_0_x"),
        "match arm scoped name (no known suffix)"
    );
    assert!(
        !is_derived_var_name("postcondition_mut"),
        "postcondition_mut (no known suffix)"
    );
    assert!(!is_derived_var_name("self"), "self");
}

/// classify_var_name returns specific DerivedKind for each suffix. (#2020)
#[test]
#[timeout(30000)]
fn classify_var_name_returns_correct_suffix_kind() {
    assert_eq!(
        classify_var_name("x_view"),
        Some(DerivedKind::View),
        "_view -> View"
    );
    assert_eq!(
        classify_var_name("x_current"),
        Some(DerivedKind::Current),
        "_current → Current"
    );
    assert_eq!(
        classify_var_name("x_final"),
        Some(DerivedKind::Final),
        "_final → Final"
    );
    assert_eq!(
        classify_var_name("x_prime"),
        Some(DerivedKind::Prime),
        "_prime → Prime"
    );
}

/// classify_var_name: old_ prefix without suffix returns Old. (#2020)
#[test]
#[timeout(30000)]
fn classify_var_name_old_prefix_only() {
    assert_eq!(
        classify_var_name("old_x"),
        Some(DerivedKind::Old),
        "old_ prefix with no suffix → Old"
    );
    assert_eq!(
        classify_var_name("old_old_x"),
        Some(DerivedKind::Old),
        "double old_ prefix → Old"
    );
}

/// classify_var_name: suffix takes priority over old_ prefix. (#2020)
///
/// Names like `old_x_current` have both a prefix and a suffix. The suffix
/// wins because suffix checks run first, matching the resolution cascade
/// order in resolve_var_sort_candidate.
#[test]
#[timeout(30000)]
fn classify_var_name_suffix_beats_old_prefix() {
    assert_eq!(
        classify_var_name("old_x_view"),
        Some(DerivedKind::View),
        "old_x_view -> View (outer _view wins)"
    );
    assert_eq!(
        classify_var_name("old_x_current"),
        Some(DerivedKind::Current),
        "old_x_current → Current (suffix wins)"
    );
    assert_eq!(
        classify_var_name("old_x_final"),
        Some(DerivedKind::Final),
        "old_x_final → Final (suffix wins)"
    );
    assert_eq!(
        classify_var_name("old_x_prime"),
        Some(DerivedKind::Prime),
        "old_x_prime → Prime (suffix wins)"
    );
}

/// classify_var_name: source names return None. (#2020)
#[test]
#[timeout(30000)]
fn classify_var_name_source_names_return_none() {
    assert_eq!(classify_var_name("x"), None, "bare source name");
    assert_eq!(classify_var_name("counter"), None, "bare source name");
    assert_eq!(classify_var_name("self"), None, "self");
    assert_eq!(classify_var_name("arm_0_x"), None, "match arm scoped name");
    assert_eq!(
        classify_var_name("postcondition_mut"),
        None,
        "postcondition_mut"
    );
}

/// classify_var_name: chained suffixes yield the outermost kind. (#2020)
#[test]
#[timeout(30000)]
fn classify_var_name_chained_suffixes() {
    assert_eq!(
        classify_var_name("x_current_view"),
        Some(DerivedKind::View),
        "x_current_view -> View (outermost)"
    );
    // x_current_final: outermost suffix is _final
    assert_eq!(
        classify_var_name("x_current_final"),
        Some(DerivedKind::Final),
        "x_current_final → Final (outermost)"
    );
    // x_prime_current: outermost suffix is _current
    assert_eq!(
        classify_var_name("x_prime_current"),
        Some(DerivedKind::Current),
        "x_prime_current → Current (outermost)"
    );
}

// ---------------------------------------------------------------------------
// Source-name vs derived-name sort resolution fence (#2020 Slice 3)
// ---------------------------------------------------------------------------

/// Mixed old_+suffix name resolves through old_ stripping then suffix cascade.
///
/// `old_v_current` has both `old_` prefix and `_current` suffix. The resolver
/// must strip `old_` → `v_current`, then let resolve_var_sort_candidate strip
/// `_current` → `v`, where the Seq hint is found. (#2020 Slice 3)
#[test]
#[timeout(30000)]
fn resolve_mixed_old_prefix_and_suffix_inherits_sort() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder.record_sort_hint("v".to_string(), ExprSort::Seq);

    // old_v_current: classify_var_name returns Current (suffix wins), but
    // the resolver must still try old_ stripping to find `v` via `v_current`.
    assert_eq!(
        encoder.resolve_var_sort_or_int("old_v_current"),
        Sort::seq(Sort::Int),
        "old_v_current should resolve to Seq via old_ strip → suffix cascade → v"
    );
}

/// Derived name (suffix) correctly inherits sort from base. (#2020 Slice 3)
#[test]
#[timeout(30000)]
fn resolve_derived_name_uses_suffix_cascade() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder.record_sort_hint("v".to_string(), ExprSort::Seq);

    // v_current is a derived name — suffix cascade strips _current → finds v
    assert_eq!(
        encoder.resolve_var_sort_or_int("v_current"),
        Sort::seq(Sort::Int),
        "derived name v_current should inherit Seq via suffix cascade"
    );
}

/// Derived name (old_ prefix) correctly inherits sort. (#2020 Slice 3)
#[test]
#[timeout(30000)]
fn resolve_derived_name_uses_old_prefix_cascade() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder.record_sort_hint("v".to_string(), ExprSort::Bool);

    // old_v is a derived name — old_ prefix stripping finds v
    assert_eq!(
        encoder.resolve_var_sort_or_int("old_v"),
        Sort::Bool,
        "derived name old_v should inherit Bool via prefix cascade"
    );
}

/// View aliases are derived names and must peel `_view` before looking up the
/// underlying base sort. (#2020 Slice 3)
#[test]
#[timeout(30000)]
fn resolve_view_alias_uses_view_suffix_cascade() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder.record_sort_hint("v".to_string(), ExprSort::Seq);

    assert_eq!(
        encoder.resolve_var_sort_or_int("v_current_view"),
        Sort::seq(Sort::Int),
        "v_current_view should resolve via _view -> _current -> v"
    );
}

/// Nested reference carriers must peel once per `final/current/view` step,
/// not just once overall. This is the derived-name sort core behind
/// `take_first_mut` shapes like `self__final_current_view`. (#1805)
#[test]
#[timeout(30000)]
fn resolve_nested_mutref_current_view_alias_peels_multiple_layers() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let nested_seq = ExprSort::MutRef(Box::new(ExprSort::MutRef(Box::new(ExprSort::Seq))));
    let declared = encoder.sort_from_expr_sort(nested_seq);
    encoder
        .get_or_declare_var("self_", declared)
        .expect("declare nested mutref self_");

    assert_eq!(
        encoder.resolve_var_sort_or_int("self__final_current_view"),
        Sort::seq(Sort::Int),
        "self__final_current_view should peel final + current to reach the Seq carrier"
    );
}

/// Scalar nested reference carriers need the same repeated peeling as Seq
/// carriers. This models `unnest` equalities like `^*x == ^^x`. (#2673)
#[test]
#[timeout(30000)]
fn resolve_nested_mutref_final_current_alias_peels_to_scalar_inner_sort() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let nested_int = ExprSort::MutRef(Box::new(ExprSort::MutRef(Box::new(ExprSort::Int))));
    let declared = encoder.sort_from_expr_sort(nested_int);
    encoder
        .get_or_declare_var("x", declared)
        .expect("declare nested mutref x");

    assert_eq!(
        encoder.resolve_var_sort_or_int("x_final_current"),
        Sort::Int,
        "x_final_current should peel both reference layers back to Int"
    );
}

/// `final_{x}_view` follows the same propagated chain as hint registration:
/// `final_{x}_view` -> `{x}_view` -> `{x}`. (#2020 Slice 3)
#[test]
#[timeout(30000)]
fn resolve_final_view_alias_uses_final_then_view_cascade() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder.record_sort_hint("v".to_string(), ExprSort::Seq);

    assert_eq!(
        encoder.resolve_var_sort_or_int("final_v_view"),
        Sort::seq(Sort::Int),
        "final_v_view should resolve via final_ strip -> v_view -> v"
    );
}

/// `final_{x}_current_view` must peel the `final_` prefix before the `_view`
/// cascade continues, matching hint propagation's mixed-chain handling.
/// `final_v_current_view` -> `v_current_view` -> `v_current` -> `v`. (#2020)
#[test]
#[timeout(30000)]
fn resolve_final_prefixed_current_view_alias_inherits_sort() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder.record_sort_hint("v".to_string(), ExprSort::Seq);

    assert_eq!(
        encoder.resolve_var_sort_or_int("final_v_current_view"),
        Sort::seq(Sort::Int),
        "final_v_current_view should resolve via final_ strip -> v_current_view -> _current"
    );
}

/// `final_old_{x}_view` must compose the inner `final_` peel with the regular
/// `old_` fallback path: `final_old_v_view` -> `old_v_view` -> `v_view` -> `v`.
#[test]
#[timeout(30000)]
fn resolve_final_prefixed_old_view_alias_inherits_sort() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder.record_sort_hint("v".to_string(), ExprSort::Bool);

    assert_eq!(
        encoder.resolve_var_sort_or_int("final_old_v_view"),
        Sort::Bool,
        "final_old_v_view should resolve via final_ strip -> old_v_view -> old_ strip -> v"
    );
}

/// `final_old_{x}_current_view` must compose all three derived-name passes:
/// `final_old_v_current_view` -> `old_v_current_view` -> `v_current_view` ->
/// `v_current` -> `v`. (#2020)
#[test]
#[timeout(30000)]
fn resolve_final_prefixed_old_current_view_alias_inherits_sort() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder.record_sort_hint("v".to_string(), ExprSort::Seq);

    assert_eq!(
        encoder.resolve_var_sort_or_int("final_old_v_current_view"),
        Sort::seq(Sort::Int),
        "final_old_v_current_view should resolve via final_ strip -> old_ strip -> _view -> _current"
    );
}

/// Mixed old_ + suffix + view names need all three passes:
/// `old_v_current_view` -> `v_current_view` -> `v_current` -> `v`. (#2020)
#[test]
#[timeout(30000)]
fn resolve_old_prefix_current_view_alias_inherits_sort() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder.record_sort_hint("v".to_string(), ExprSort::Bool);

    assert_eq!(
        encoder.resolve_var_sort_or_int("old_v_current_view"),
        Sort::Bool,
        "old_v_current_view should resolve via old_ strip -> _view strip -> _current strip"
    );
}

/// Repeated `old_` prefixes still resolve through the same derived-name
/// cascade: `old_old_v_current_view` -> `old_v_current_view` ->
/// `v_current_view` -> `v_current` -> `v`. (#2020 Slice 3)
#[test]
#[timeout(30000)]
fn resolve_double_old_prefix_current_view_alias_inherits_sort() {
    use trust_wp_core::formula::ExprSort;

    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder.record_sort_hint("v".to_string(), ExprSort::Bool);

    assert_eq!(
        encoder.resolve_var_sort_or_int("old_old_v_current_view"),
        Sort::Bool,
        "old_old_v_current_view should resolve via repeated old_ peel -> _view -> _current"
    );
}

/// Source name without hints correctly falls back to Int. (#2020 Slice 3)
///
/// The diagnostic fires only under TRUST_WP_DEBUG=1, but the Int fallback
/// is always the same. This test verifies behavioral compatibility.
#[test]
#[timeout(30000)]
fn resolve_source_name_falls_back_to_int_without_cascade() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();

    // "unknown_source" is a source name — no suffix/prefix cascade applies
    assert_eq!(
        encoder.resolve_var_sort_or_int("unknown_source"),
        Sort::Int,
        "source name without hints should fall back to Int"
    );
}

/// Source name with exact declaration resolves without cascade. (#2020 Slice 3)
#[test]
#[timeout(30000)]
fn resolve_source_name_with_declaration_resolves_directly() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    let sort = Sort::Uninterpreted("UserOption".to_string());
    encoder
        .get_or_declare_var("x", sort.clone())
        .expect("declare x");

    // Source name with declaration — no cascade needed
    assert_eq!(
        encoder.resolve_var_sort_or_int("x"),
        sort,
        "declared source name should resolve directly"
    );
}

/// Reserved standard datatype declarations canonicalize to native AY sorts
/// and derived names inherit that exact canonical sort.
#[test]
#[timeout(30000)]
fn resolve_reserved_option_declaration_uses_native_datatype() {
    let mut encoder = AYEncoder::new_pure_with_quantifiers();
    encoder
        .get_or_declare_var("opt", Sort::Uninterpreted("OptionInt".to_string()))
        .expect("declare opt");

    assert!(
        matches!(
            encoder.resolve_var_sort_or_int("opt_current"),
            Sort::Datatype(dt) if dt.name == "OptionInt"
        ),
        "reserved OptionInt should canonicalize before derived-name resolution"
    );
}

/// View(@) recurses into inner expression sort — identity for scalars. (#2057)
/// Reverted from #2003 unconditional Seq return which caused 8 regressions.
#[test]
#[timeout(30000)]
fn test_infer_expr_sort_view_recurses_comprehensive() {
    // View(Int(42)) → Int — View is identity for scalars (#2057)
    assert_eq!(infer_expr_sort(&view(int(42))), Sort::Int);
    // View(Bool — via Not) → Bool — View recurses. Not on unannotated var
    // defaults to Bool (logical negation, dominant case in contracts).
    assert_eq!(infer_expr_sort(&view(not(var("x")))), Sort::Bool);
    // View(comparison) → Bool — View recurses
    assert_eq!(infer_expr_sort(&view(gt(var("a"), var("b")))), Sort::Bool);
    // View(Seq-producing MethodCall) → Seq — View recurses into push_back
    assert_eq!(
        infer_expr_sort(&view(method_call(var("v"), "push_back", vec![int(1)]))),
        Sort::seq(Sort::Int),
        "View of Seq-producing method should return Seq"
    );
    // View(nested View(Var)) → Int — View recurses through nested View
    assert_eq!(
        infer_expr_sort(&view(view(var("x")))),
        Sort::Int,
        "Nested View on unannotated Var should return Int"
    );
}
