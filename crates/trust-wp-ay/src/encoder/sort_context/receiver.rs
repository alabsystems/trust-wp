// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Method receiver sort classification helpers.

use ay_dpll::api::Sort;
use trust_wp_core::formula::{resolve_sort_name, ExprSort, PureExpr};

use super::{
    annotations::expr_annotation_is_mapping,
    mapping_expr_sort, matches_registered_sort, reference_like_inner_sort, resolve_view_var_name,
    sort_inference::{
        expr_sort_to_ay_sort, is_fmap_model_type, is_mapping_model_type, is_seq_model_type,
    },
    sort_mapping::expr_sort_to_ay_sort_for_carrier,
};
use crate::encoder::{
    seq::{expr_produces_seq, normalize_seq_receiver_for_scan},
    AYEncoder,
};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ReceiverAnnotationKind {
    Seq,
    FMap,
    Mapping,
    OtherNonInt,
}

fn expr_sort_is_seq(sort: &ExprSort) -> bool {
    if let Some(inner) = reference_like_inner_sort(sort) {
        return expr_sort_is_seq(inner);
    }
    match sort {
        ExprSort::Seq => true,
        ExprSort::Datatype(id) => {
            let name = resolve_sort_name(*id);
            let type_name = name.rsplit("::").next().unwrap_or(&name);
            is_seq_model_type(type_name)
        }
        _ => false,
    }
}

fn expr_sort_is_fmap(sort: &ExprSort) -> bool {
    if let Some(inner) = reference_like_inner_sort(sort) {
        return expr_sort_is_fmap(inner);
    }
    match sort {
        ExprSort::FMap => true,
        ExprSort::Datatype(id) => {
            let name = resolve_sort_name(*id);
            let type_name = name.rsplit("::").next().unwrap_or(&name);
            is_fmap_model_type(type_name)
        }
        _ => false,
    }
}

fn expr_sort_is_mapping(sort: &ExprSort) -> bool {
    if let Some(inner) = reference_like_inner_sort(sort) {
        return expr_sort_is_mapping(inner);
    }
    match sort {
        ExprSort::Datatype(id) => {
            let name = resolve_sort_name(*id);
            let type_name = name.rsplit("::").next().unwrap_or(&name);
            is_mapping_model_type(type_name)
        }
        _ => false,
    }
}

fn expr_sort_is_predcell_slice(sort: &ExprSort) -> bool {
    if let Some(inner) = reference_like_inner_sort(sort) {
        return expr_sort_is_predcell_slice(inner);
    }
    match sort {
        ExprSort::Datatype(id) => {
            let name = resolve_sort_name(*id);
            let type_name = name.rsplit("::").next().unwrap_or(&name);
            type_name == "PredCellSlice"
        }
        _ => false,
    }
}

fn receiver_annotation(expr: &PureExpr) -> Option<&ExprSort> {
    match expr {
        PureExpr::Var(_, ann) => ann.as_ref(),
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => receiver_annotation(inner),
        _ => None,
    }
}

fn receiver_annotation_kind(expr: &PureExpr) -> Option<ReceiverAnnotationKind> {
    let sort = receiver_annotation(expr)?;
    if matches!(expr, PureExpr::View(inner) if receiver_annotation(inner).is_some_and(expr_sort_is_predcell_slice))
        || expr_sort_is_seq(sort)
    {
        Some(ReceiverAnnotationKind::Seq)
    } else if expr_sort_is_fmap(sort) {
        Some(ReceiverAnnotationKind::FMap)
    } else if expr_sort_is_mapping(sort) || expr_annotation_is_mapping(expr) {
        Some(ReceiverAnnotationKind::Mapping)
    } else if expr_sort_to_ay_sort(sort) != Sort::Int {
        Some(ReceiverAnnotationKind::OtherNonInt)
    } else {
        None
    }
}

/// Returns true if the expression structurally produces an FMap-sorted result.
///
/// Mirrors `expr_produces_seq` for FMap: detects FMap-returning method calls
/// (`insert` with 2 args, `merge`), FMap constructor LogicFnCalls
/// (`fmap_empty`, `FMap::empty`, `fmap_insert`, `fmap_merge`), and propagates
/// through wrappers and branches. (#994 Phase 3 Slice 2)
fn expr_produces_fmap(expr: &PureExpr) -> bool {
    match expr {
        PureExpr::MethodCall { method, args, .. } => {
            matches!((method.as_str(), args.len()), ("insert" | "merge", 2))
        }
        PureExpr::LogicFnCall { name, .. } => {
            matches!(
                name.as_str(),
                "fmap_empty" | "FMap::empty" | "fmap_insert" | "fmap_merge"
            )
        }
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => expr_produces_fmap(inner),
        PureExpr::Ite(_, then_br, else_br) => {
            expr_produces_fmap(then_br) || expr_produces_fmap(else_br)
        }
        PureExpr::Match { arms, .. } => arms.iter().any(|arm| expr_produces_fmap(&arm.body)),
        PureExpr::Let { body, .. }
        | PureExpr::LetAssume { body, .. }
        | PureExpr::LetObligation { body, .. } => expr_produces_fmap(body),
        _ => false,
    }
}

fn receiver_is_predcell_slice_index_view(expr: &PureExpr) -> bool {
    let PureExpr::View(inner) = expr else {
        return false;
    };
    let PureExpr::MethodCall {
        receiver, method, ..
    } = inner.as_ref()
    else {
        return false;
    };
    matches!(method.as_str(), "index" | "index_logic")
        && receiver_annotation(receiver).is_some_and(expr_sort_is_predcell_slice)
}

impl AYEncoder {
    fn is_seq_index_mapping_candidate(
        &self,
        receiver: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> bool {
        let PureExpr::MethodCall {
            receiver: inner,
            method,
            args,
        } = receiver
        else {
            return false;
        };
        matches!(method.as_str(), "index" | "index_logic")
            && args.len() == 1
            // #2316: `Seq<Mapping>` element receivers lower to a nested
            // `seq.index_logic(i).index_logic(k)` shape. Until Seq element sorts
            // become parametric, treat that inner Seq element as a Mapping
            // receiver so later lookups stay on the same carrier as
            // `PredCellSlice` element views.
            && self.is_seq_receiver(inner, prefix)
    }

    /// Check if a method call receiver is Seq-sorted. (#699)
    ///
    /// Priority: structural > annotation (authoritative) > hint (heuristic).
    /// Annotations from ExprSort MUST be checked before hint-based View
    /// early-returns to prevent stale Seq hints from overriding FMap/Mapping
    /// annotations. See coverage_steps test for regression guard.
    pub(crate) fn is_seq_receiver(
        &self,
        receiver: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> bool {
        // `set` returns `Self`, so `X.set(k, v)` has `X`'s collection kind. The
        // unconditional `method_produces_seq("set")` (meaning "set on a Seq")
        // otherwise mis-classifies a chained total-`Mapping` `m.set(..).set(..)`
        // (mapping_indexing) as Seq. Recurse on the inner receiver first. (#newfrontier)
        if let PureExpr::MethodCall {
            receiver: inner,
            method,
            args,
        } = receiver
        {
            if method == "set" && args.len() == 2 {
                return self.is_seq_receiver(inner, prefix);
            }
        }
        if expr_produces_seq(receiver) {
            return true;
        }
        // PredCellSlice element views are Mapping carriers, not Seq
        // receivers. Keep them off the Seq path so `index_logic` can
        // reach the dedicated Mapping dispatch instead of `seq_index_logic`.
        if receiver_is_predcell_slice_index_view(receiver) {
            return false;
        }
        // Bare PredCellSlice receivers are not intrinsically Seq-like:
        // `index_logic` still returns PredCell, not an Int element. But when the
        // prescan tags the specific receiver as Seq (for `len()` on
        // PredCellSlice), honor that explicit hint before the non-Int
        // annotation fallback rejects it. (#2316)
        if receiver_annotation(receiver).is_some_and(expr_sort_is_predcell_slice)
            && self.is_receiver_of_sort(receiver, prefix, &ExprSort::Seq)
        {
            return true;
        }
        match receiver_annotation_kind(receiver) {
            Some(ReceiverAnnotationKind::Seq) => return true,
            Some(
                ReceiverAnnotationKind::FMap
                | ReceiverAnnotationKind::Mapping
                | ReceiverAnnotationKind::OtherNonInt,
            ) => {
                return false;
            }
            None => {}
        }
        if matches!(receiver, PureExpr::View(_))
            && self.is_receiver_of_sort(receiver, prefix, &ExprSort::Seq)
        {
            return true;
        }
        self.is_receiver_of_sort(receiver, prefix, &ExprSort::Seq)
    }

    /// Check if a method call receiver is FMap-sorted. (#1778)
    ///
    /// Priority: structural > annotation (authoritative) > hint (heuristic).
    /// Structural check added in #994 Phase 3 Slice 2 to match `is_seq_receiver`
    /// symmetry — prevents FMap-sorted receivers from leaking into Seq dispatch
    /// when annotations are missing.
    pub(crate) fn is_fmap_receiver(
        &self,
        receiver: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> bool {
        if expr_produces_fmap(receiver) {
            return true;
        }
        match receiver_annotation_kind(receiver) {
            Some(ReceiverAnnotationKind::FMap) => return true,
            Some(
                ReceiverAnnotationKind::Seq
                | ReceiverAnnotationKind::Mapping
                | ReceiverAnnotationKind::OtherNonInt,
            ) => {
                return false;
            }
            None => {}
        }
        if matches!(receiver, PureExpr::View(_))
            && self.is_receiver_of_sort(receiver, prefix, &ExprSort::FMap)
        {
            return true;
        }
        self.is_receiver_of_sort(receiver, prefix, &ExprSort::FMap)
    }

    /// Check if a method call receiver is Mapping (total function) sorted. (#2317)
    ///
    /// Priority: annotation (authoritative) > hint (heuristic).
    pub(crate) fn is_mapping_receiver(
        &self,
        receiver: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> bool {
        // `set` returns `Self`: a chained total-`Mapping` `m.set(..).set(..)`
        // keeps the Mapping kind of its innermost receiver. (#newfrontier)
        if let PureExpr::MethodCall {
            receiver: inner,
            method,
            args,
        } = receiver
        {
            if method == "set" && args.len() == 2 {
                return self.is_mapping_receiver(inner, prefix);
            }
        }
        if receiver_is_predcell_slice_index_view(receiver) {
            return true;
        }
        if self.is_seq_index_mapping_candidate(receiver, prefix) {
            return true;
        }
        match receiver_annotation_kind(receiver) {
            Some(ReceiverAnnotationKind::Mapping) => return true,
            Some(
                ReceiverAnnotationKind::Seq
                | ReceiverAnnotationKind::FMap
                | ReceiverAnnotationKind::OtherNonInt,
            ) => {
                return false;
            }
            None => {}
        }
        let mapping = mapping_expr_sort();
        if matches!(receiver, PureExpr::View(_))
            && self.is_receiver_of_sort(receiver, prefix, &mapping)
        {
            return true;
        }
        self.is_receiver_of_sort(receiver, prefix, &mapping)
    }

    /// Check if a method call receiver matches the given sort hint. (#2083)
    ///
    /// Shared implementation for `is_seq_receiver` and `is_fmap_receiver`.
    /// Checks the variable name against sort hints (prefixed, unprefixed,
    /// normalized view var, and unprefixed normalized).
    fn is_receiver_of_sort(
        &self,
        receiver: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
        hint: &ExprSort,
    ) -> bool {
        // Compared against sorts this encoder has actually registered, so the
        // hint must be minted on this encoder's Seq carrier — a native
        // `(Seq Int)` target would never match a registered `Seq` and every
        // Seq receiver would fall out of Seq dispatch.
        let target_sort = expr_sort_to_ay_sort_for_carrier(hint, self.seq_carrier());
        if let PureExpr::Var(name, _) = receiver {
            let lookup = prefix.map_or_else(|| name.clone(), |kind| kind.format_name(name));
            if matches_registered_sort(self, &lookup, &target_sort) {
                return true;
            }
        }
        let normalized = normalize_seq_receiver_for_scan(receiver);
        if let Some(name) = resolve_view_var_name(normalized.as_ref(), prefix) {
            if matches_registered_sort(self, &name, &target_sort) {
                return true;
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use ntest::timeout;

    use super::*;

    fn var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), None)
    }

    fn method_call(receiver: PureExpr, method: &str, args: Vec<PureExpr>) -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(receiver),
            method: method.to_string(),
            args,
        }
    }

    fn logic_fn(name: &str) -> PureExpr {
        PureExpr::LogicFnCall {
            name: name.to_string(),
            args: vec![],
        }
    }

    #[test]
    #[timeout(30000)]
    fn test_expr_produces_fmap_insert_2arg() {
        let expr = method_call(var("m"), "insert", vec![var("k"), var("v")]);
        assert!(expr_produces_fmap(&expr));
    }

    #[test]
    #[timeout(30000)]
    fn test_expr_produces_fmap_insert_1arg_is_fset() {
        let expr = method_call(var("s"), "insert", vec![var("x")]);
        assert!(!expr_produces_fmap(&expr));
    }

    #[test]
    #[timeout(30000)]
    fn test_expr_produces_fmap_merge() {
        let expr = method_call(var("m"), "merge", vec![var("other"), var("resolver")]);
        assert!(expr_produces_fmap(&expr));
    }

    #[test]
    #[timeout(30000)]
    fn test_expr_produces_fmap_logic_fn_constructors() {
        assert!(expr_produces_fmap(&logic_fn("fmap_empty")));
        assert!(expr_produces_fmap(&logic_fn("FMap::empty")));
        assert!(expr_produces_fmap(&logic_fn("fmap_insert")));
        assert!(expr_produces_fmap(&logic_fn("fmap_merge")));
    }

    #[test]
    #[timeout(30000)]
    fn test_expr_produces_fmap_non_fmap_methods() {
        assert!(!expr_produces_fmap(&method_call(var("m"), "len", vec![])));
        assert!(!expr_produces_fmap(&method_call(
            var("m"),
            "lookup",
            vec![var("k")]
        )));
        assert!(!expr_produces_fmap(&method_call(
            var("m"),
            "contains",
            vec![var("k")]
        )));
    }

    #[test]
    #[timeout(30000)]
    fn test_expr_produces_fmap_through_wrappers() {
        let insert = method_call(var("m"), "insert", vec![var("k"), var("v")]);
        // View wrapping
        assert!(expr_produces_fmap(&PureExpr::View(Arc::new(
            insert.clone()
        ))));
        // Old wrapping
        assert!(expr_produces_fmap(&PureExpr::Old(Arc::new(insert.clone()))));
        // Nested: Old(View(insert))
        assert!(expr_produces_fmap(&PureExpr::Old(Arc::new(
            PureExpr::View(Arc::new(insert))
        ))));
    }

    #[test]
    #[timeout(30000)]
    fn test_expr_produces_fmap_through_ite() {
        let fmap_branch = logic_fn("fmap_empty");
        let int_branch = var("x");
        let expr = PureExpr::Ite(
            Arc::new(var("cond")),
            Arc::new(fmap_branch),
            Arc::new(int_branch),
        );
        assert!(expr_produces_fmap(&expr));
    }

    #[test]
    #[timeout(30000)]
    fn test_expr_produces_fmap_bare_var() {
        // Bare variables are not structurally FMap — need annotation or hint
        assert!(!expr_produces_fmap(&var("hashmap")));
    }
}
