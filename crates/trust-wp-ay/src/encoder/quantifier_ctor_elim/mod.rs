// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Constructor equality quantifier elimination.
//!
//! Detects patterns like `exists<v> scrutinee == Constructor(v)` and eliminates
//! the quantifier using datatype tester/selector operations. Handles both
//! single-variable (#1752) and multi-variable (#1765) patterns.
//!
//! Extracted from `quantifier.rs` as part of #1669 structural decomposition.
//!
//! ## Module layout
//!
//! - [`sort_inference`] — Sort inference for quantifier variables from constructor args
//! - [`detection`] — Constructor equality pattern detection in quantifier bodies
//! - [`elimination`] — `AYEncoder` methods for quantifier elimination encoding

mod detection;
mod elimination;
mod sort_inference;

// Re-export the public API at the same paths as before the decomposition.
use ay_dpll::api::{DatatypeSort, Term};
pub(crate) use detection::detect_constructor_eq;
// Test-only re-export for coverage_gaps tests that cannot access private submodules.
#[cfg(test)]
pub(crate) use sort_inference::arg_is_any_qvar_reference;
pub(crate) use sort_inference::{
    infer_constructor_arg_sort, infer_constructor_arg_sorts_batch, infer_method_call_usage_sort,
    infer_method_call_usage_sorts_batch,
};
use trust_wp_core::formula::PureExpr;

/// Result of detecting a constructor equality pattern in a quantifier body.
///
/// Represents the destructured information needed to eliminate a quantifier
/// via datatype tester/selector substitution (#1752, #1765).
pub(crate) struct ConstructorEqInfo<'a> {
    /// The scrutinee expression (the non-constructor side of the equality).
    pub(crate) scrutinee: &'a PureExpr,
    /// The constructor name (e.g., "OwnResult::Ok", "Some").
    pub(crate) ctor_name: &'a str,
    /// The declared datatype for this constructor.
    pub(crate) datatype: DatatypeSort,
    /// Mapping of quantifier variables to constructor field indices.
    /// Each entry is `(var_name, field_index)`. For a nullary constructor
    /// this is empty. For `exists<k, v> x == Pair(k, v)`, this would be
    /// `[("k", 0), ("v", 1)]`. (#1765)
    pub(crate) var_field_map: Vec<(&'a str, usize)>,
    /// Optional nested constructor for patterns like `OwnResult::Ok(Some(t))`.
    ///
    /// When present, the outer constructor has exactly one arg which is an
    /// inner constructor call, and the inner constructor's args are the
    /// actual quantifier variables. The elimination produces:
    ///   `is-Outer(self) && is_inner(selector(self)) ==> P(accessor(selector(self)))`
    ///
    /// This avoids the E-matching chain that would be needed if the nested
    /// constructor equality were handled by UF coercion axioms — ay-dpll
    /// cannot Skolemize existentials (#ay#813), so the negated universal's
    /// trigger would have no ground instances to match against. (#1296)
    pub(crate) inner_ctor: Option<InnerConstructorEq<'a>>,
}

/// Nested constructor information for two-level constructor equality elimination.
///
/// Represents the inner constructor in patterns like `OwnResult::Ok(Some(t))`.
pub(crate) struct InnerConstructorEq<'a> {
    /// The inner constructor name (e.g., "Some").
    pub(crate) ctor_name: &'a str,
    /// The declared datatype for the inner constructor.
    pub(crate) datatype: DatatypeSort,
    /// Field index of the outer constructor's field that holds the inner value.
    pub(crate) outer_field_index: usize,
    /// Mapping of quantifier variables to inner constructor field indices.
    pub(crate) var_field_map: Vec<(&'a str, usize)>,
}

/// Pre-computed outer elimination results passed into nested constructor
/// elimination, reducing the parameter count below clippy's
/// `too_many_arguments` threshold. (#2657)
pub(crate) struct OuterElimContext<'a> {
    /// The encoded scrutinee term from the outer constructor match.
    pub(crate) scrutinee_term: Term,
    /// The outer constructor tester (e.g., `is-Ok(self)`).
    pub(crate) outer_tester: Term,
    /// The constructor equality info for the outer pattern.
    pub(crate) info: &'a ConstructorEqInfo<'a>,
}

pub(crate) fn arg_is_qvar_reference(expr: &PureExpr, qvar: &str) -> bool {
    match expr {
        PureExpr::Var(name, _) => name == qvar,
        PureExpr::Deref(inner)
        | PureExpr::Old(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => arg_is_qvar_reference(inner, qvar),
        _ => false,
    }
}

/// Extract the base variable name from a scrutinee expression.
///
/// Handles `Var("x")`, `Deref(Var("x"))`, `Old(Var("x"))`, etc.
/// Used to pre-seed the scrutinee's sort before encoding in the
/// constructor equality elimination path. (#1752)
///
/// Delegates to [`sort_context::extract_base_var_name`] — same logic,
/// deduplicated in #2654.
pub(crate) fn extract_scrutinee_var_name(expr: &PureExpr) -> Option<&str> {
    crate::encoder::sort_context::extract_base_var_name(expr)
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use trust_wp_core::formula::PureExpr;

    use super::{arg_is_qvar_reference, extract_scrutinee_var_name};
    use crate::{
        encoder::quantifier_ctor_elim::arg_is_any_qvar_reference,
        tests::helpers::{deref, final_expr, old, var, view},
    };

    // ── arg_is_qvar_reference ──

    #[test]
    fn test_arg_is_qvar_reference_direct_match() {
        let expr = var("x");
        assert!(arg_is_qvar_reference(&expr, "x"));
    }

    #[test]
    fn test_arg_is_qvar_reference_different_name() {
        let expr = var("x");
        assert!(!arg_is_qvar_reference(&expr, "y"));
    }

    #[test]
    fn test_arg_is_qvar_reference_through_deref() {
        let expr = deref(var("x"));
        assert!(arg_is_qvar_reference(&expr, "x"));
    }

    #[test]
    fn test_arg_is_qvar_reference_through_old() {
        let expr = old(var("x"));
        assert!(arg_is_qvar_reference(&expr, "x"));
    }

    #[test]
    fn test_arg_is_qvar_reference_through_final() {
        let expr = final_expr(var("x"));
        assert!(arg_is_qvar_reference(&expr, "x"));
    }

    #[test]
    fn test_arg_is_qvar_reference_through_view() {
        let expr = view(var("x"));
        assert!(arg_is_qvar_reference(&expr, "x"));
    }

    #[test]
    fn test_arg_is_qvar_reference_nested_wrappers() {
        // Deref(Old(View(Var("x"))))
        let expr = deref(old(view(var("x"))));
        assert!(arg_is_qvar_reference(&expr, "x"));
    }

    #[test]
    fn test_arg_is_qvar_reference_non_var_returns_false() {
        let expr = PureExpr::Int(42);
        assert!(!arg_is_qvar_reference(&expr, "x"));
    }

    // ── extract_scrutinee_var_name ──

    #[test]
    fn test_extract_scrutinee_var_name_direct() {
        let expr = var("self");
        assert_eq!(extract_scrutinee_var_name(&expr), Some("self"));
    }

    #[test]
    fn test_extract_scrutinee_var_name_through_deref() {
        let expr = deref(var("self"));
        assert_eq!(extract_scrutinee_var_name(&expr), Some("self"));
    }

    #[test]
    fn test_extract_scrutinee_var_name_through_old() {
        let expr = old(var("x"));
        assert_eq!(extract_scrutinee_var_name(&expr), Some("x"));
    }

    #[test]
    fn test_extract_scrutinee_var_name_through_final() {
        let expr = final_expr(var("ma"));
        assert_eq!(extract_scrutinee_var_name(&expr), Some("ma"));
    }

    #[test]
    fn test_extract_scrutinee_var_name_through_view() {
        let expr = view(var("v"));
        assert_eq!(extract_scrutinee_var_name(&expr), Some("v"));
    }

    #[test]
    fn test_extract_scrutinee_var_name_nested_wrappers() {
        let expr = deref(old(var("self")));
        assert_eq!(extract_scrutinee_var_name(&expr), Some("self"));
    }

    #[test]
    fn test_extract_scrutinee_var_name_non_var_returns_none() {
        let expr = PureExpr::Int(0);
        assert_eq!(extract_scrutinee_var_name(&expr), None);
    }

    #[test]
    fn test_extract_scrutinee_var_name_binop_returns_none() {
        use crate::tests::helpers::add;
        let expr = add(var("x"), var("y"));
        assert_eq!(extract_scrutinee_var_name(&expr), None);
    }

    // ── arg_is_any_qvar_reference ──

    #[test]
    fn test_arg_is_any_qvar_reference_match() {
        let qvars: HashSet<&str> = ["k", "v"].into_iter().collect();
        let expr = var("k");
        assert_eq!(arg_is_any_qvar_reference(&expr, &qvars), Some("k"));
    }

    #[test]
    fn test_arg_is_any_qvar_reference_second_var() {
        let qvars: HashSet<&str> = ["k", "v"].into_iter().collect();
        let expr = var("v");
        assert_eq!(arg_is_any_qvar_reference(&expr, &qvars), Some("v"));
    }

    #[test]
    fn test_arg_is_any_qvar_reference_not_in_set() {
        let qvars: HashSet<&str> = ["k", "v"].into_iter().collect();
        let expr = var("x");
        assert_eq!(arg_is_any_qvar_reference(&expr, &qvars), None);
    }

    #[test]
    fn test_arg_is_any_qvar_reference_through_deref() {
        let qvars: HashSet<&str> = ["k"].into_iter().collect();
        let expr = deref(var("k"));
        assert_eq!(arg_is_any_qvar_reference(&expr, &qvars), Some("k"));
    }

    #[test]
    fn test_arg_is_any_qvar_reference_non_var() {
        let qvars: HashSet<&str> = ["k"].into_iter().collect();
        let expr = PureExpr::Int(42);
        assert_eq!(arg_is_any_qvar_reference(&expr, &qvars), None);
    }

    #[test]
    fn test_arg_is_any_qvar_reference_empty_set() {
        let qvars: HashSet<&str> = HashSet::new();
        let expr = var("x");
        assert_eq!(arg_is_any_qvar_reference(&expr, &qvars), None);
    }
}

#[cfg(test)]
mod detect_constructor_eq_tests {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
    use ntest::timeout;

    use super::detect_constructor_eq;
    use crate::{
        encoder::{quantifier::QuantifierKind, AYEncoder},
        tests::helpers::{add, eq, gt, implies, int, logic_fn_call, var},
    };

    fn option_int_datatype() -> DatatypeSort {
        DatatypeSort {
            name: "OptionInt".to_string(),
            constructors: vec![
                DatatypeConstructor {
                    name: "None".to_string(),
                    fields: vec![],
                },
                DatatypeConstructor {
                    name: "Some".to_string(),
                    fields: vec![DatatypeField {
                        name: "value".to_string(),
                        sort: Sort::Int,
                    }],
                },
            ],
        }
    }

    /// exists<v> x == Some(v) should be detected as a constructor equality
    /// pattern with var_field_map mapping v to field 0.
    #[test]
    #[timeout(30000)]
    fn detect_option_some_single_var_exists() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let dt = option_int_datatype();
        encoder.ensure_datatype_declared(&dt);
        encoder
            .get_or_declare_var("x", Sort::Datatype(dt))
            .expect("declare x");

        let body = eq(var("x"), logic_fn_call("OptionInt::Some", vec![var("v")]));
        let qvars = vec!["v"];
        let info = detect_constructor_eq(&encoder, QuantifierKind::Exists, &body, &qvars);

        assert!(info.is_some(), "should detect constructor equality pattern");
        let info = info.unwrap();
        assert_eq!(info.ctor_name, "OptionInt::Some");
        assert_eq!(info.var_field_map.len(), 1);
        assert_eq!(info.var_field_map[0], ("v", 0));
        assert!(info.inner_ctor.is_none(), "no nested constructor");
    }

    /// Constructor equality with reversed sides: Some(v) == x should also
    /// be detected (the detector checks both orderings).
    #[test]
    #[timeout(30000)]
    fn detect_reversed_equality_some_v_eq_x() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let dt = option_int_datatype();
        encoder.ensure_datatype_declared(&dt);
        encoder
            .get_or_declare_var("x", Sort::Datatype(dt))
            .expect("declare x");

        // Reversed: Some(v) == x instead of x == Some(v)
        let body = eq(logic_fn_call("OptionInt::Some", vec![var("v")]), var("x"));
        let qvars = vec!["v"];
        let info = detect_constructor_eq(&encoder, QuantifierKind::Exists, &body, &qvars);

        assert!(
            info.is_some(),
            "should detect reversed constructor equality"
        );
        let info = info.unwrap();
        assert_eq!(info.ctor_name, "OptionInt::Some");
        assert_eq!(info.var_field_map[0], ("v", 0));
    }

    /// A body with no constructor equality (e.g., x > 0) should return None
    /// for both Exists and Forall quantifiers.
    #[test]
    #[timeout(30000)]
    fn detect_non_constructor_body_returns_none() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let dt = option_int_datatype();
        encoder.ensure_datatype_declared(&dt);
        encoder
            .get_or_declare_var("x", Sort::Datatype(dt))
            .expect("declare x");

        // Body is just x > 0 — no constructor pattern
        let body = gt(var("x"), int(0));
        let qvars = vec!["v"];

        let exists_info = detect_constructor_eq(&encoder, QuantifierKind::Exists, &body, &qvars);
        assert!(
            exists_info.is_none(),
            "non-constructor body should not be detected for exists"
        );

        let forall_info = detect_constructor_eq(&encoder, QuantifierKind::Forall, &body, &qvars);
        assert!(
            forall_info.is_none(),
            "non-constructor body should not be detected for forall"
        );
    }

    /// forall<v> x == Some(v) ==> v > 0 should be detected as a constructor
    /// equality pattern (the guard is the LHS of Implies).
    #[test]
    #[timeout(30000)]
    fn detect_forall_implies_constructor_guard() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let dt = option_int_datatype();
        encoder.ensure_datatype_declared(&dt);
        encoder
            .get_or_declare_var("x", Sort::Datatype(dt))
            .expect("declare x");

        let guard = eq(var("x"), logic_fn_call("OptionInt::Some", vec![var("v")]));
        let consequent = gt(var("v"), int(0));
        let body = implies(guard, consequent);
        let qvars = vec!["v"];
        let info = detect_constructor_eq(&encoder, QuantifierKind::Forall, &body, &qvars);

        assert!(
            info.is_some(),
            "forall with Implies-shaped body should detect constructor guard"
        );
        let info = info.unwrap();
        assert_eq!(info.ctor_name, "OptionInt::Some");
        assert_eq!(info.var_field_map[0], ("v", 0));
    }

    /// forall<v> x == Some(v) (non-Implies body) should NOT be detected.
    /// This is the #1781 soundness guard — detect returns None so the normal
    /// quantifier encoder handles it.
    #[test]
    #[timeout(30000)]
    fn detect_forall_non_implies_returns_none() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let dt = option_int_datatype();
        encoder.ensure_datatype_declared(&dt);
        encoder
            .get_or_declare_var("x", Sort::Datatype(dt))
            .expect("declare x");

        let body = eq(var("x"), logic_fn_call("OptionInt::Some", vec![var("v")]));
        let qvars = vec!["v"];
        let info = detect_constructor_eq(&encoder, QuantifierKind::Forall, &body, &qvars);

        assert!(
            info.is_none(),
            "forall with non-Implies body must not be detected (#1781)"
        );
    }

    /// Constructor arg that is not a quantifier variable should cause
    /// detection to fail: exists<v> x == Some(y) where y is not in qvars.
    #[test]
    #[timeout(30000)]
    fn detect_rejects_non_qvar_constructor_arg() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let dt = option_int_datatype();
        encoder.ensure_datatype_declared(&dt);
        encoder
            .get_or_declare_var("x", Sort::Datatype(dt))
            .expect("declare x");

        // y is not in qvars
        let body = eq(var("x"), logic_fn_call("OptionInt::Some", vec![var("y")]));
        let qvars = vec!["v"];
        let info = detect_constructor_eq(&encoder, QuantifierKind::Exists, &body, &qvars);

        assert!(
            info.is_none(),
            "constructor arg not in qvars should cause detection to fail"
        );
    }

    /// Constructor arg that is a complex expression (not a variable) should
    /// cause detection to fail: exists<v> x == Some(v + 1).
    #[test]
    #[timeout(30000)]
    fn detect_rejects_complex_constructor_arg() {
        let mut encoder = AYEncoder::new_with_quantifiers();
        let dt = option_int_datatype();
        encoder.ensure_datatype_declared(&dt);
        encoder
            .get_or_declare_var("x", Sort::Datatype(dt))
            .expect("declare x");

        let body = eq(
            var("x"),
            logic_fn_call("OptionInt::Some", vec![add(var("v"), int(1))]),
        );
        let qvars = vec!["v"];
        let info = detect_constructor_eq(&encoder, QuantifierKind::Exists, &body, &qvars);

        assert!(
            info.is_none(),
            "complex expression as constructor arg should cause detection to fail"
        );
    }

    /// Constructor arg wrapped in Deref should be detected for exists:
    /// `exists<t> *self == OwnResult::Ok(*t)` where `*t` = Deref(Var("t")).
    ///
    /// This is the pattern used by `OwnResult::as_ref` postconditions where
    /// reference-typed quantifier variables are dereferenced inside the
    /// constructor call. (#1296)
    #[test]
    #[timeout(30000)]
    fn detect_deref_wrapped_qvar_in_constructor_arg() {
        use crate::tests::helpers::deref;

        let mut encoder = AYEncoder::new_with_quantifiers();
        let dt = own_result_datatype();
        encoder.ensure_datatype_declared(&dt);
        encoder
            .get_or_declare_var("self", Sort::Datatype(dt))
            .expect("declare self");

        // Pattern: *self == OwnResult::Ok(*t) where *t = Deref(Var("t"))
        let body = eq(
            deref(var("self")),
            logic_fn_call("OwnResult::Ok", vec![deref(var("t"))]),
        );
        let qvars = vec!["t"];
        let info = detect_constructor_eq(&encoder, QuantifierKind::Exists, &body, &qvars);

        assert!(
            info.is_some(),
            "Deref-wrapped qvar in constructor arg should be detected (#1296)"
        );
        let info = info.unwrap();
        assert_eq!(info.ctor_name, "OwnResult::Ok");
        assert_eq!(info.var_field_map.len(), 1);
        assert_eq!(info.var_field_map[0], ("t", 0));
    }

    /// Forall with Deref-wrapped qvar in constructor guard should be detected:
    /// `forall<t: &T> *self == OwnResult::Ok(*t) ==> result == OwnResult::Ok(t)`
    ///
    /// This is the exact pattern from `OwnResult::as_ref` in the Creusot
    /// compat test file. (#1296)
    #[test]
    #[timeout(30000)]
    fn detect_forall_deref_wrapped_qvar_as_ref_pattern() {
        use crate::tests::helpers::deref;

        let mut encoder = AYEncoder::new_with_quantifiers();
        let dt = own_result_datatype();
        encoder.ensure_datatype_declared(&dt);
        encoder
            .get_or_declare_var("self", Sort::Datatype(dt))
            .expect("declare self");

        // Guard: *self == OwnResult::Ok(*t)
        let guard = eq(
            deref(var("self")),
            logic_fn_call("OwnResult::Ok", vec![deref(var("t"))]),
        );
        // Consequent: result == OwnResult::Ok(t)
        let consequent = eq(
            var("result"),
            logic_fn_call("OwnResult::Ok", vec![var("t")]),
        );
        let body = implies(guard, consequent);
        let qvars = vec!["t"];
        let info = detect_constructor_eq(&encoder, QuantifierKind::Forall, &body, &qvars);

        assert!(
            info.is_some(),
            "forall with Deref-wrapped qvar guard should detect as_ref pattern (#1296)"
        );
        let info = info.unwrap();
        assert_eq!(info.ctor_name, "OwnResult::Ok");
        assert_eq!(info.var_field_map[0], ("t", 0));
    }

    fn own_result_datatype() -> DatatypeSort {
        DatatypeSort {
            name: "OwnResult".to_string(),
            constructors: vec![
                DatatypeConstructor {
                    name: "Ok".to_string(),
                    fields: vec![DatatypeField {
                        name: "ok_value".to_string(),
                        sort: Sort::Int,
                    }],
                },
                DatatypeConstructor {
                    name: "Err".to_string(),
                    fields: vec![DatatypeField {
                        name: "err_value".to_string(),
                        sort: Sort::Int,
                    }],
                },
            ],
        }
    }
}
