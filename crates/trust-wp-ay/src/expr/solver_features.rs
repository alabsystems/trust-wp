// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Solver feature detection predicates for `PureExpr` trees.
//!
//! These predicates determine which SMT solver features (quantifiers,
//! custom sorts, etc.) an expression requires, used by `verify/setup.rs`
//! for solver logic selection.

use trust_wp_core::{
    formula::{PureExpr, PureExprDepthLimitedTraversalExt as _},
    logic::is_invariant_method_name,
};

use crate::encoder::MAX_ENCODING_DEPTH;

/// Checks if an expression contains method calls that require UF-capable logic.
///
/// Closure-spec methods (`postcondition_once`, `postcondition_mut`, etc.) may
/// trigger the `fn_mut_once` law axiom, which uses quantifiers. When closure-spec
/// methods appear in requires/ensures, quantifier support is needed for the
/// connecting axiom.
///
/// Also detects `invariant()` predicate methods, which are encoded as
/// uninterpreted Bool functions and require a UF-capable solver logic.
pub(crate) fn expr_has_closure_spec_method(expr: &PureExpr) -> bool {
    // fail-closed: `on_limit = true` assumes feature exists at depth limit
    expr.any_recursive_with_depth_limit(MAX_ENCODING_DEPTH, true, |e| {
        matches!(
            e,
            PureExpr::MethodCall { method, .. }
                if matches!(
                    method.as_str(),
                    "precondition" | "postcondition" | "postcondition_once" | "postcondition_mut"
                ) || is_invariant_method_name(method)
        )
    })
}

/// Checks if an expression contains any quantifiers (forall/exists).
///
/// Used to determine if SMT encoding requires quantifier support.
/// Returns true if any subexpression is a `Forall` or `Exists`.
pub(crate) fn expr_needs_quantifiers(expr: &PureExpr) -> bool {
    // fail-closed: `on_limit = true` assumes quantifiers exist at depth limit
    expr.any_recursive_with_depth_limit(MAX_ENCODING_DEPTH, true, |e| {
        matches!(e, PureExpr::Forall { .. } | PureExpr::Exists { .. })
    })
}

/// Checks if an expression uses Option/Result spec methods or constructors.
///
/// Returns true if the expression contains:
/// - Method calls: `is_some`, `is_none`, `unwrap`, `unwrap_logic`, `unwrap_or_default`, `is_ok`, `is_err`, `unwrap_err`, `contains`
/// - Logic function calls: `Some`, `None`, `Ok`, `Err` (constructor expressions)
///
/// When true, the encoder needs quantifier support to assert the constructor/
/// tester/accessor axioms (e.g., `forall v. spec_unwrap(Some(v)) = v`).
pub(crate) fn expr_has_datatype_spec_method(expr: &PureExpr) -> bool {
    // fail-closed: `on_limit = true` assumes feature exists at depth limit
    expr.any_recursive_with_depth_limit(MAX_ENCODING_DEPTH, true, |e| {
        matches!(
            e,
            PureExpr::MethodCall { method, .. }
                if matches!(
                    method.as_str(),
                    "is_some" | "is_none" | "unwrap" | "unwrap_logic" | "unwrap_or_default" | "is_ok" | "is_err" | "unwrap_err" | "contains"
                )
        ) || matches!(
            e,
            PureExpr::LogicFnCall { name, .. }
                if matches!(name.as_str(), "Some" | "None" | "Ok" | "Err")
        )
    })
}

/// Checks if an expression contains a match with Option/Result constructor patterns.
///
/// When true, the match encoder will declare a native ay datatype (OptionInt or
/// ResultIntInt), requiring a solver logic that supports algebraic datatypes.
/// The `QF_LIA` (pure) solver doesn't support datatypes and returns `Unknown`. (#1055)
pub(crate) fn expr_has_match_constructor_pattern(expr: &PureExpr) -> bool {
    // fail-closed: `on_limit = true` assumes feature exists at depth limit
    expr.any_recursive_with_depth_limit(MAX_ENCODING_DEPTH, true, |e| {
        matches!(
            e,
            PureExpr::Match { arms, .. }
                if arms.iter().any(|arm| matches!(
                    arm.pattern,
                    trust_wp_core::formula::Pattern::Constructor { .. }
                ))
        )
    })
}

/// Checks if an expression contains tuple constructor or destructor logic function calls.
///
/// Returns true if any subexpression is a `LogicFnCall` that is a valid tuple
/// constructor (`__trust_wp_tupleN` with N >= 2) or field accessor
/// (`__trust_wp_tuple_get_I`). Uses precise parsers to avoid false positives from
/// prefix matching. When true, the solver needs quantifier support so that the
/// tuple axioms (`forall x0 x1. get_I(tupleN(x0, x1)) = xI`) can be instantiated
/// via E-matching.
pub(crate) fn expr_has_tuple_fn(expr: &PureExpr) -> bool {
    use trust_wp_core::formula::internal::tuple_lowering::{
        tuple_field_logic_fn_index, tuple_logic_fn_arity,
    };
    // fail-closed: `on_limit = true` assumes feature exists at depth limit
    expr.any_recursive_with_depth_limit(MAX_ENCODING_DEPTH, true, |e| {
        matches!(
            e,
            PureExpr::LogicFnCall { name, .. }
                if tuple_logic_fn_arity(name).is_some()
                    || tuple_field_logic_fn_index(name).is_some()
        )
    })
}

/// Checks if an expression contains bitwise operators (Shl, Shr, BitAnd, BitXor, BitOr).
///
/// These operators are encoded as uninterpreted functions (`__trust_wp_bit_and`, etc.)
/// with quantified axioms (`assert_bitwise_axioms`). A QF_LIA solver cannot handle
/// UFs or quantifiers, so the logic must be escalated when bitwise ops appear. (#1922)
pub(crate) fn expr_has_bitwise_ops(expr: &PureExpr) -> bool {
    use trust_wp_core::formula::BinOp;
    // fail-closed: `on_limit = true` assumes feature exists at depth limit
    expr.any_recursive_with_depth_limit(MAX_ENCODING_DEPTH, true, |e| {
        matches!(
            e,
            PureExpr::BinOp(_, op, _)
                if matches!(op, BinOp::Shl | BinOp::Shr | BinOp::BitAnd | BinOp::BitXor | BinOp::BitOr)
        )
    })
}
