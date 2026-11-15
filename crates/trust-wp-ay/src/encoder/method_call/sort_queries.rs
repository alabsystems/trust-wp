// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sort-inference helpers for method-call encoding.
//!
//! Extracted from `method_call/mod.rs` as part of #1584 to isolate
//! encoded-sort lookup and expression-level sort classification from
//! the main dispatch router.

use ay_dpll::api::{Sort, Term};
use trust_wp_core::formula::{
    internal::tuple_lowering::{NAMED_FIELD_LOGIC_FN_PREFIX, TUPLE_FIELD_LOGIC_FN_PREFIX},
    resolve_sort_name, ExprSort, PureExpr,
};

use crate::encoder::{
    match_enc::stdlib_option_datatype_for_payload,
    sort_context::{
        extract_base_var_name, infer_expr_sort_cached, is_seq_family_sort, resolve_nameable_expr,
        resolve_registered_non_int_sort, resolve_view_var_name,
        sort_inference::{expr_sort_to_ay_sort, is_seq_model_type},
        DerivedKind, InferExprSortCache,
    },
    AYEncoder,
};

/// Check if an expression has a Seq sort annotation, including `Datatype`
/// annotations for types that map to Seq (Vec, List, VecDeque, Seq). (#994)
///
/// Previously only matched `ExprSort::Seq` directly, missing cases where
/// MIR lowering preserves the concrete type name (e.g., `Datatype(List)`)
/// instead of normalizing to `ExprSort::Seq`. This caused loop-generated
/// variables with `Datatype(List)` annotations to be misrouted in the
/// ambiguous method dispatch (len, contains, index).
pub(super) fn expr_has_seq_sort_annotation(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Var(_, Some(ann)) => annotation_is_seq(ann),
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => expr_has_seq_sort_annotation(inner),
        _ => false,
    }
}

fn annotation_is_seq(sort: &ExprSort) -> bool {
    match sort {
        ExprSort::Seq => true,
        ExprSort::Ref(inner) | ExprSort::MutRef(inner) => annotation_is_seq(inner),
        ExprSort::Datatype(id) => {
            let name = resolve_sort_name(*id);
            let type_name = name.rsplit("::").next().unwrap_or(&name);
            is_seq_model_type(type_name)
        }
        _ => false,
    }
}

fn registered_name_is_seq(encoder: &AYEncoder, name: &str) -> bool {
    resolve_registered_non_int_sort(encoder, name).is_some_and(|sort| is_seq_family_sort(&sort))
        || encoder.sort_hint(name).is_some_and(annotation_is_seq)
}

fn sort_from_expr_sort_hint(encoder: &AYEncoder, hint: &ExprSort) -> Sort {
    if annotation_is_seq(hint) {
        return encoder
            .seq_state
            .sort()
            .cloned()
            .unwrap_or_else(|| Sort::seq(Sort::Int));
    }
    expr_sort_to_ay_sort(hint)
}

/// Returns true when the expression is syntactically known to evaluate to an
/// Int carrier, independent of sort-hint state. This is used by the
/// `index_logic` dispatcher to keep numeric indices such as `seq.len()` on the
/// Seq path even if stronger Seq hints have been recorded elsewhere. (#994)
pub(super) fn expr_is_known_int_key(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::Int(_) => true,
        PureExpr::Var(_, Some(sort)) => expr_sort_to_ay_sort(sort) == Sort::Int,
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => expr_is_known_int_key(inner),
        PureExpr::UnOp(trust_wp_core::formula::UnOp::Neg, inner) => expr_is_known_int_key(inner),
        PureExpr::BinOp(left, op, right) => {
            matches!(
                op,
                trust_wp_core::formula::BinOp::Add
                    | trust_wp_core::formula::BinOp::Sub
                    | trust_wp_core::formula::BinOp::Mul
                    | trust_wp_core::formula::BinOp::Div
                    | trust_wp_core::formula::BinOp::Mod
                    | trust_wp_core::formula::BinOp::DivTrunc
                    | trust_wp_core::formula::BinOp::RemTrunc
                    | trust_wp_core::formula::BinOp::Shl
                    | trust_wp_core::formula::BinOp::Shr
                    | trust_wp_core::formula::BinOp::BitAnd
                    | trust_wp_core::formula::BinOp::BitXor
                    | trust_wp_core::formula::BinOp::BitOr
            ) && expr_is_known_int_key(left)
                && expr_is_known_int_key(right)
        }
        PureExpr::MethodCall { method, .. } => matches!(
            method.as_str(),
            "len"
                | "len_logic"
                | "pow2"
                | "sum"
                | "deep_model"
                | "shallow_model"
                | "discriminant"
                | "capacity"
        ),
        // A machine bit operation at its type (D-242) is an integer.
        PureExpr::LogicFnCall { name, .. } => crate::encoder::parse_int_bitop_name(name).is_some(),
        _ => false,
    }
}

pub(super) fn expr_is_structural_field_receiver(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::LogicFnCall { name, .. } => {
            name.starts_with(TUPLE_FIELD_LOGIC_FN_PREFIX)
                || name.starts_with(NAMED_FIELD_LOGIC_FN_PREFIX)
        }
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => expr_is_structural_field_receiver(inner),
        _ => false,
    }
}

impl AYEncoder {
    pub(super) fn method_param_sort(
        &self,
        expr: &PureExpr,
        term: Term,
        prefix: Option<DerivedKind>,
    ) -> Sort {
        let actual = self.solver.get_sort(term);
        let inferred = self.infer_encoded_sort(expr, prefix);
        if actual == Sort::Int {
            return inferred;
        }

        match (&actual, &inferred) {
            // ay may expose a native datatype carrier as an Uninterpreted sort
            // on term reads even when the encoder has already registered the
            // concrete Datatype sort for the expression. Preserve the
            // registered Datatype sort so method UF symbols stay aligned with
            // type-invariant axiom registration and other sort-keyed method
            // declarations. (#2257, #2189)
            (Sort::Uninterpreted(actual_name), Sort::Datatype(inferred_dt))
                if actual_name == &inferred_dt.name =>
            {
                inferred
            }
            _ => actual,
        }
    }

    /// Infer the sort of an expression using encoder state (var_sorts).
    ///
    /// Unlike the free function `infer_expr_sort`, this method resolves
    /// expression-to-variable-name mappings (including View) and looks up
    /// the actual declared sort in `var_sorts`. Falls back to `infer_expr_sort`
    /// when the expression doesn't resolve to a known variable. (#1128)
    pub(in crate::encoder) fn infer_encoded_sort(
        &self,
        expr: &PureExpr,
        prefix: Option<DerivedKind>,
    ) -> Sort {
        // Try View-specific resolution first (View(Var("v")) → "v_view")
        if let Some(name) = resolve_view_var_name(expr, prefix) {
            if let Some(sort) = resolve_registered_non_int_sort(self, &name) {
                return sort;
            }
        }
        // Try standard resolution (Var, Old, Deref, Final)
        if let Some(name) = resolve_nameable_expr(expr, prefix) {
            if let Some(sort) = resolve_registered_non_int_sort(self, &name) {
                return sort;
            }
        }
        // Check sort hints on the base variable name through wrappers.
        // Quantifier-bound variables (e.g., forall<s: Seq>) have sort hints
        // on the bare name "s", but Deref(Var("s")) resolves to "s_current"
        // which may not have a hint. Strip wrappers to find the base name
        // and check its hint. (#1805)
        if let Some(base) = extract_base_var_name(expr) {
            if let Some(prefixed_key) = prefix.map(|kind| kind.format_name(base)) {
                if let Some(hint) = self.sort_hint(&prefixed_key) {
                    return sort_from_expr_sort_hint(self, hint);
                }
            }
            if let Some(hint) = self.sort_hint(base) {
                return sort_from_expr_sort_hint(self, hint);
            }
        }
        // Preserve explicit ExprSort::Seq annotations under wrappers (Deref/Old/Final/View)
        // for method UF declarations. AST-only infer_expr_sort intentionally defaults
        // Seq vars to Int in some paths; method signatures need the concrete Seq sort.
        if expr_has_seq_sort_annotation(expr) {
            return self
                .seq_state
                .sort()
                .cloned()
                .unwrap_or_else(|| Sort::seq(Sort::Int));
        }
        if let PureExpr::Var(name, None) = expr {
            if let Some(datatype) = self.nullary_constructor_datatype(name) {
                return Sort::Datatype(datatype);
            }
        }
        // Standard ADT constructors (Some/None/Ok/Err) return Int in the
        // UF encoding path (logic_Some: Int -> Int, logic_None: Int, etc.).
        // Return Int directly instead of falling to the AST-level catch-all
        // which fires the demoting SortFallbackToIntFromLogicFn counter.
        // Without this, postconditions that reference Option/Result values
        // accumulate false demotions that convert Verified to Unknown.
        // (#1474, bug/1504)
        if let PureExpr::LogicFnCall { name, args } = expr {
            let short = name
                .rsplit_once("::")
                .map_or(name.as_str(), |(_, short)| short);
            if short == "Some" {
                if let Some(payload) = args.first() {
                    let payload_sort = self.infer_encoded_sort(payload, prefix);
                    let payload_sort = if is_seq_family_sort(&payload_sort) {
                        Sort::Uninterpreted("Seq".to_string())
                    } else {
                        payload_sort.as_term_sort()
                    };
                    let datatype = stdlib_option_datatype_for_payload(payload_sort);
                    return Sort::Datatype(datatype);
                }
                return Sort::Int;
            }
            if matches!(short, "None" | "Ok" | "Err") {
                return Sort::Int;
            }
            if let Some(datatype) = self.constructor_datatype(name) {
                return Sort::Datatype(datatype);
            }
        }
        // MutRef-annotated variables that are already declared as Int: use
        // the declared sort instead of the AST annotation. The RustHorn
        // encoding represents &mut T variables as (current, final) pairs of
        // the inner sort. When `MutRef(TypeParam(T))` peels to Int in the
        // sort plan but the raw annotation still says MutRef, the AST-level
        // inference returns `Uninterpreted("MutRef_Int")`. This mismatch
        // causes `prefer_specific_sort` to select MutRef as the equality
        // target sort, which cascades into spurious sort coercion and
        // disconnected constraints. (#2673)
        if let PureExpr::Var(name, Some(ExprSort::MutRef(_))) = expr {
            let resolved = prefix
                .map(|kind| kind.format_name(name))
                .unwrap_or_else(|| name.to_string());
            if matches!(self.var_sort(&resolved), Some(Sort::Int)) {
                return Sort::Int;
            }
        }
        // A registered logic-function declaration is authoritative for the
        // call's result sort. Consult it before AST-only inference, whose
        // unknown-function fallback defaults to Int and records a demotion.
        // This mirrors `infer_expr_sort_with_context`.
        if let PureExpr::LogicFnCall { name, .. } = expr {
            let smt_name = trust_wp_core::logic::logic_fn_smt_name(name);
            if let Some(func_decl) = self.logic_func_decl_cloned(&smt_name) {
                return func_decl.range().clone();
            }
            if let Some(method) = name.strip_prefix("Self::") {
                let bare_name = trust_wp_core::logic::logic_fn_smt_name(method);
                if let Some(func_decl) = self.logic_func_decl_cloned(&bare_name) {
                    return func_decl.range().clone();
                }
            }
        }
        // Fall back to AST-level inference, memoized for the duration of THIS
        // call only (#2278 F2 asked for the memo to kill O(n²) re-walks during
        // BinOp encoding; it must not outlive the tree it keyed on).
        //
        // The memo is keyed by `*const PureExpr`. `expr` and its `Arc` children
        // are alive for the whole call, so every key is valid here. An encoder-
        // lifetime cache is NOT: callers routinely hand this function
        // short-lived temporaries (the ghost flattener's ground instances, the
        // rewritten equalities in `encode_binop_expr`), and once such a node is
        // dropped the allocator hands its address to the next `PureExpr`, which
        // then inherits the dead node's sort. Measured on `fmap_indexing`: an
        // `FMap` payload `lookup` inherited `Sort::Bool`, which routes every
        // later `<recv>.lookup(k)` through the Bool-context operand path and
        // replaces the Int payload with `lookup(recv, k) != 0` — fabricating
        // `payload ∈ {0, 1}` premises that contradict the faithfully encoded
        // copy of the same frame law (base UNSAT -> fail-closed vacuous proof).
        let mut sort_cache = InferExprSortCache::default();
        infer_expr_sort_cached(expr, &mut sort_cache)
    }

    /// Check if an expression's base variable name has a Seq sort hint,
    /// either under the given prefix or bare. Used by `index_logic` dispatch
    /// to detect Seq-keyed arguments from quantifier-bound variables whose
    /// Var node lacks an ExprSort annotation but whose Forall var_sort is Seq.
    /// (#1805)
    pub(super) fn base_var_has_seq_hint(
        &self,
        expr: &PureExpr,
        prefix: Option<DerivedKind>,
    ) -> bool {
        fn candidate_has_seq_hint(
            encoder: &AYEncoder,
            name: &str,
            prefix: Option<DerivedKind>,
        ) -> bool {
            let prefixed = prefix.map(|kind| kind.format_name(name));
            let view_name = DerivedKind::View.format_name(name);

            prefixed
                .as_deref()
                .is_some_and(|candidate| registered_name_is_seq(encoder, candidate))
                || registered_name_is_seq(encoder, name)
                || registered_name_is_seq(encoder, &view_name)
        }

        extract_base_var_name(expr).is_some_and(|base| {
            if candidate_has_seq_hint(self, base, prefix) {
                return true;
            }

            let mut stripped = base;
            while let Some((_kind, next)) = DerivedKind::strip_from(stripped) {
                if candidate_has_seq_hint(self, next, prefix) {
                    return true;
                }
                stripped = next;
            }

            for stripped in DerivedKind::peel_old_prefixes(base) {
                if candidate_has_seq_hint(self, stripped, prefix) {
                    return true;
                }
            }

            false
        })
    }

    /// Check if a method call has a Bool sort hint. Uses receiver-qualified
    /// key to prevent cross-receiver sort hint pollution (#1820, #2245).
    pub(super) fn method_has_bool_hint(
        &self,
        receiver: &trust_wp_core::formula::PureExpr,
        method: &str,
    ) -> bool {
        let qualified_key =
            crate::encoder::sort_context::hint_collection::receiver_qualified_method_hint_key(
                receiver, method,
            );
        self.sort_hint_matches(&qualified_key, &trust_wp_core::formula::ExprSort::Bool)
    }
}
