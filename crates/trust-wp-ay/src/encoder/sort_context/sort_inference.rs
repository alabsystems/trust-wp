// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sort inference for pure expressions.

use std::collections::HashMap;

mod logic_fn_sort;
mod method_call_sort;
mod non_bool;
mod receiver_shape;

use ay_dpll::api::Sort;
use logic_fn_sort::infer_logic_fn_sort;
use method_call_sort::infer_method_call_sort;
pub(crate) use non_bool::is_definitely_non_bool;
use receiver_shape::{
    annotation_is_seq_like, method_call_returns_predcell_like, receiver_annotation,
    receiver_is_predcell_like,
};
use trust_wp_core::formula::{BinOp, PureExpr, UnOp};

pub(crate) use super::sort_mapping::{
    ay_sort_to_expr_sort, canonical_sort, expr_sort_to_ay_sort, fmap_sort, is_fmap_model_type,
    is_mapping_model_type, is_seq_model_type, mapping_sort, unit_sort, CanonicalSort,
};
use super::{
    extract_inner_var_annotation, reference_like_inner_sort, resolve_adt_family_alias,
    sort_coercion::normalize_structural_sort_family,
};
use crate::encoder::unsoundness;

/// Memo table for [`infer_expr_sort_cached`], keyed by the *address* of the
/// `PureExpr` node.
///
/// # Lifetime contract (load-bearing — read before reusing this type)
///
/// A `*const PureExpr` key is only meaningful while that node is alive. The
/// allocator reuses freed addresses, so an entry that outlives its node becomes
/// a **use-after-free oracle**: the next `PureExpr` that happens to land on the
/// same address gets the dead node's sort. That is not a rare theoretical
/// hazard — `PureExpr` temporaries are minted and dropped in bulk by the ghost
/// flattener's ground instantiation, and the reuse was measured live
/// (`Int(2)` answering `Sort::Bool`; `map.lookup(k)` answering `Sort::Bool`).
///
/// **Every cache of this type must therefore be created, used, and dropped
/// inside a single call that holds the expression tree alive** — never stored
/// in encoder state across calls.
pub(in crate::encoder) type InferExprSortCache = HashMap<*const PureExpr, Sort>;

enum InferExprSortMode<'a> {
    Uncached,
    Cached(&'a mut InferExprSortCache),
}

impl InferExprSortMode<'_> {
    fn get(&mut self, expr: &PureExpr) -> Option<Sort> {
        match self {
            Self::Uncached => None,
            Self::Cached(cache) => cache.get(&std::ptr::from_ref(expr)).cloned(),
        }
    }

    fn insert(&mut self, expr: &PureExpr, sort: Sort) {
        if let Self::Cached(cache) = self {
            cache.insert(std::ptr::from_ref(expr), sort);
        }
    }
}

#[allow(clippy::match_same_arms, clippy::too_many_lines)]
fn infer_expr_sort_impl(expr: &PureExpr, cache_mode: &mut InferExprSortMode<'_>) -> Sort {
    fn deref_or_final_sort(inner: &PureExpr, cache_mode: &mut InferExprSortMode<'_>) -> Sort {
        if let Some(referent_sort) =
            extract_inner_var_annotation(inner).and_then(reference_like_inner_sort)
        {
            return expr_sort_to_ay_sort(referent_sort);
        }
        infer_expr_sort_impl(inner, cache_mode)
    }

    if let Some(sort) = cache_mode.get(expr) {
        return sort;
    }

    let sort = match expr {
        PureExpr::Bool(_) => Sort::Bool,
        PureExpr::Int(_) => Sort::Int,
        PureExpr::Float(_) => Sort::Real,
        PureExpr::Var(_, Some(sort)) => expr_sort_to_ay_sort(sort),
        PureExpr::Var(_, None) => {
            unsoundness::increment(unsoundness::UnsoundnessCategory::SortFallbackToIntFromVar);
            Sort::Int
        }
        PureExpr::BinOp(_, op, _) => match op {
            BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => Sort::Bool,
            BinOp::And | BinOp::Or | BinOp::Implies => Sort::Bool,
            BinOp::Add
            | BinOp::Sub
            | BinOp::Mul
            | BinOp::Div
            | BinOp::Mod
            | BinOp::DivTrunc
            | BinOp::RemTrunc
            | BinOp::Shl
            | BinOp::Shr
            | BinOp::BitAnd
            | BinOp::BitXor
            | BinOp::BitOr => Sort::Int,
            // BinOp is #[non_exhaustive]; required for cross-crate match.
            // AUDIT(#2663): Currently unreachable — all BinOp variants are
            // matched above. Reclassified from HIGH SortFallbackToInt to
            // LOW SortFallbackToIntFromCatchAll per #2663 Phase 1a —
            // the catch-all is future-proofing, not a current risk.
            #[allow(unreachable_patterns)]
            _ => {
                unsoundness::increment(
                    unsoundness::UnsoundnessCategory::SortFallbackToIntFromCatchAll,
                );
                Sort::Int
            }
        },
        PureExpr::UnOp(op, operand) => match op {
            UnOp::Not => {
                // Logical NOT on Bool -> Bool (dominant case in logic context).
                // Bitwise NOT on Int -> Int (Rust `!x` on integers).
                // Only return Int when the operand is *structurally* known to
                // be non-Bool (annotated Int, arithmetic expression, etc.).
                // Unannotated variables default to Bool for Not since logical
                // negation is the overwhelming use in contracts. (#1096)
                if is_definitely_non_bool(operand) {
                    Sort::Int
                } else {
                    Sort::Bool
                }
            }
            // BitNot is always Int -> Int (integer bitwise complement, #2697).
            UnOp::BitNot => Sort::Int,
            UnOp::Neg => {
                // Arithmetic negation: `-x` -> Int in all practical cases.
                // Propagate Bool only when operand is structurally Bool
                // (e.g., annotated Bool variable). (#1096)
                let operand_sort = infer_expr_sort_impl(operand, cache_mode);
                if operand_sort == Sort::Bool {
                    Sort::Bool
                } else {
                    Sort::Int
                }
            }
            // UnOp is #[non_exhaustive]; required for cross-crate match.
            // AUDIT(#2663): Currently unreachable — Not, BitNot, and Neg
            // are the only UnOp variants. Reclassified from HIGH
            // SortFallbackToInt to LOW SortFallbackToIntFromCatchAll
            // per #2663 Phase 1a — catch-all is future-proofing only.
            #[allow(unreachable_patterns)]
            _ => {
                unsoundness::increment(
                    unsoundness::UnsoundnessCategory::SortFallbackToIntFromCatchAll,
                );
                Sort::Int
            }
        },
        PureExpr::Ite(_, then_expr, else_expr) => {
            let then_sort = infer_expr_sort_impl(then_expr, cache_mode);
            let else_sort = infer_expr_sort_impl(else_expr, cache_mode);
            if then_sort == else_sort {
                then_sort
            } else if then_sort == Sort::Int {
                // Prefer the concrete sort when one branch is Int (unknown/default)
                // and the other is more specific. (#1965 Phase 2 audit)
                else_sort
            } else if else_sort == Sort::Int {
                then_sort
            } else if let Some(resolved) = resolve_same_family_sorts(&then_sort, &else_sort) {
                // When both branches are sorts in the same ADT family
                // (e.g., OptionInt vs Option, Datatype(OptionInt) vs
                // Uninterpreted("Option"), Seq(Int) vs Uninterpreted("Vec")),
                // prefer the more specific sort. (#2675, #2699)
                resolved
            } else if let Some(target) =
                super::sort_coercion::select_structural_sort_target(&then_sort, &else_sort)
            {
                // Structural sort target resolution handles cross-sort-type
                // families (e.g., Seq vs Int-from-Vec, Datatype vs Int).
                // This catches cases that resolve_same_family_sorts misses
                // because the sorts are from different ay sort constructors
                // but represent the same logical type. (#2699)
                target
            } else {
                // Genuine mismatch — fall back to then_sort. This can happen
                // with complex nested expressions; the encoder's coercion layer
                // will handle any actual sort conflicts at the ay level.
                then_sort
            }
        }
        PureExpr::Forall { .. } | PureExpr::Exists { .. } => Sort::Bool,
        PureExpr::Old(inner) => infer_expr_sort_impl(inner, cache_mode),
        PureExpr::Deref(inner) => deref_or_final_sort(inner, cache_mode),
        PureExpr::Final(inner) => deref_or_final_sort(inner, cache_mode),
        // View (@) usually preserves the underlying sort, but some wrappers
        // expose a different logical carrier. PredCell views are Mapping-valued,
        // so `cell@` must infer as Mapping rather than the runtime PredCell type.
        // (#2316)
        PureExpr::View(inner) if receiver_is_predcell_like(inner) => mapping_sort(),
        // View on a collection-annotated receiver: `vec@` produces `Seq<T>`,
        // so infer Seq sort. Only triggers when the inner expression carries
        // an explicit Seq or collection Datatype annotation (via
        // `receiver_annotation`), not the broad `receiver_is_seq_like` fallback
        // which considers all View expressions as Seq-like. Without this rule,
        // View on `Var("v", Datatype(Vec))` falls through to recursive identity
        // inference and returns the Datatype sort instead of Seq. (#1096)
        PureExpr::View(inner) if annotation_is_seq_like(receiver_annotation(inner)) => {
            Sort::seq(Sort::Int)
        }
        // `PredCell::as_slice_of_cells(...)[i]` produces a `PredCell<T>` element,
        // so viewing the indexed element must expose the predicate Mapping.
        // (#2316)
        PureExpr::View(inner) if method_call_returns_predcell_like(inner) => mapping_sort(),
        // View on a non-collection Datatype-annotated expression: where x
        // has an ADT annotation (Option, Result, user enum) should propagate
        // the ADT sort. Without this, the recursive identity inference may lose
        // the type information when the inner expression is a complex expression
        // rather than a simple Var. (#2699)
        PureExpr::View(inner)
            if matches!(
                extract_inner_var_annotation(inner),
                Some(trust_wp_core::formula::ExprSort::Datatype(_))
            ) && !annotation_is_seq_like(extract_inner_var_annotation(inner)) =>
        {
            let inner_sort = infer_expr_sort_impl(inner, cache_mode);
            // Only propagate if the inner sort is concrete (not Int fallback)
            if inner_sort != Sort::Int {
                inner_sort
            } else {
                // Fall back to annotation-derived sort
                match extract_inner_var_annotation(inner) {
                    Some(ann) => expr_sort_to_ay_sort(ann),
                    None => infer_expr_sort_impl(inner, cache_mode),
                }
            }
        }
        // View is otherwise identity for scalars (e.g., u32@ = u32) and only
        // produces Seq/FMap/Mapping when the inner already carries that sort.
        // The encoding layer (encode_view_expr + sort hints) handles Seq
        // declaration. Unconditional Seq return caused 8 regressions in tests
        // using View on non-collection variables. (#2057, reverts #2003)
        PureExpr::View(inner) => infer_expr_sort_impl(inner, cache_mode),
        PureExpr::MethodCall {
            receiver,
            method,
            args,
            ..
        } => infer_method_call_sort(receiver, method, args, &mut |arg| {
            infer_expr_sort_impl(arg, cache_mode)
        }),
        PureExpr::LogicFnCall { name, args } => {
            infer_logic_fn_sort(name, args, &mut |arg| infer_expr_sort_impl(arg, cache_mode))
        }
        PureExpr::Match { arms, .. } if !arms.is_empty() => {
            let first_sort = infer_expr_sort_impl(&arms[0].body, cache_mode);
            // If the first arm infers as Int (unknown/default), check if any
            // later arm has a concrete sort and prefer that. (#1965 Phase 2 audit)
            if first_sort == Sort::Int {
                if let Some(concrete_sort) = arms
                    .iter()
                    .skip(1)
                    .map(|arm| infer_expr_sort_impl(&arm.body, cache_mode))
                    .find(|arm_sort| *arm_sort != Sort::Int)
                {
                    concrete_sort
                } else {
                    first_sort
                }
            } else {
                // First arm is non-Int. Check if later arms disagree and
                // try to resolve cross-sort-type mismatches via family
                // resolution and structural sort targets. (#2699)
                let mut best = first_sort;
                for arm in arms.iter().skip(1) {
                    let arm_sort = infer_expr_sort_impl(&arm.body, cache_mode);
                    if arm_sort == best || arm_sort == Sort::Int {
                        continue;
                    }
                    // Try family resolution (e.g., Datatype vs Uninterpreted)
                    if let Some(resolved) = resolve_same_family_sorts(&best, &arm_sort) {
                        best = resolved;
                    } else if let Some(target) =
                        super::sort_coercion::select_structural_sort_target(&best, &arm_sort)
                    {
                        best = target;
                    }
                    // Otherwise keep the current best
                }
                best
            }
        }
        PureExpr::Let { body, .. } => infer_expr_sort_impl(body, cache_mode),
        PureExpr::LetAssume { body, .. } | PureExpr::LetObligation { body, .. } => {
            infer_expr_sort_impl(body, cache_mode)
        }
        // Closures: infer sort from the body expression. Closures in logic
        // context are lambda-like — their "sort" is the body's return sort.
        // Previously hit the catch-all HIGH SortFallbackToInt. (#994)
        PureExpr::Closure { body, .. } => infer_expr_sort_impl(body, cache_mode),
        // Catch-all for future #[non_exhaustive] PureExpr variants.
        // AUDIT(#2663): Currently unreachable — all PureExpr variants
        // (Bool, Int, Float, Var, BinOp, UnOp, Ite, Forall, Exists, Old,
        // Deref, Final, View, MethodCall, LogicFnCall, Match, Let,
        // LetAssume, LetObligation, Closure) are matched above.
        // Reclassified from HIGH SortFallbackToInt to LOW
        // SortFallbackToIntFromCatchAll per #2663 Phase 1a.
        #[allow(unreachable_patterns)]
        _ => {
            unsoundness::increment(unsoundness::UnsoundnessCategory::SortFallbackToIntFromCatchAll);
            Sort::Int
        }
    };

    cache_mode.insert(expr, sort.clone());
    sort
}

/// Resolve two sorts that belong to the same ADT or model family.
///
/// Handles cross-sort-type resolution beyond just Uninterpreted vs Uninterpreted:
/// - `Uninterpreted("OptionInt")` vs `Uninterpreted("Option")` → prefer OptionInt
/// - `Datatype(OptionInt)` vs `Uninterpreted("OptionInt")` → prefer Datatype
/// - `Seq(Int)` vs `Uninterpreted("Vec")` → prefer Seq(Int) (native sort)
/// - `Datatype(Adt_Some_None)` vs `Uninterpreted("Option")` → prefer Datatype
///
/// Returns `None` if the sorts are unrelated.
///
/// Known families:
/// - `Option` / `OptionInt` → prefer `OptionInt`
/// - `Result` / `ResultIntInt` → prefer `ResultIntInt`
/// - `Vec` / `VecDeque` / `Seq` / `LinkedList` → prefer `Seq(Int)` (native)
/// - `FMap` / `HashMap` / `GhostMap` → prefer `FMap`
fn resolve_same_family_sorts(a: &Sort, b: &Sort) -> Option<Sort> {
    // Case 1: Both Uninterpreted — original path
    if let (Sort::Uninterpreted(an), Sort::Uninterpreted(bn)) = (a, b) {
        let family_a = ite_sort_family(an);
        let family_b = ite_sort_family(bn);
        if family_a == family_b {
            // Prefer the more specific (longer) name.
            return if an.len() >= bn.len() {
                Some(a.clone())
            } else {
                Some(b.clone())
            };
        }
    }

    // Case 2: Datatype vs Uninterpreted in the same family.
    // Native Datatype sorts from match encoding (e.g., Datatype(Adt_Some_None))
    // should be preferred over Uninterpreted("Option") since they carry
    // constructor/accessor information needed by the solver. (#2699)
    if let (Sort::Datatype(dt), Sort::Uninterpreted(name)) = (a, b) {
        let family_a = ite_sort_family(&dt.name);
        let family_b = ite_sort_family(name);
        if family_a == family_b {
            return Some(a.clone()); // prefer Datatype
        }
    }
    if let (Sort::Uninterpreted(name), Sort::Datatype(dt)) = (a, b) {
        let family_a = ite_sort_family(name);
        let family_b = ite_sort_family(&dt.name);
        if family_a == family_b {
            return Some(b.clone()); // prefer Datatype
        }
    }

    // Case 3: Seq vs Uninterpreted Seq-family (e.g., Seq(Int) vs Uninterpreted("Vec")).
    // The native Seq sort is the canonical encoding for all Seq-model types post-#2080.
    // When one branch infers Seq(Int) and the other infers a legacy Uninterpreted("Vec"),
    // prefer the native Seq sort. (#2699)
    if let Sort::Seq(_) = a {
        if let Sort::Uninterpreted(name) = b {
            let family = normalize_structural_sort_family(name);
            if family == "Seq" {
                return Some(a.clone()); // prefer native Seq
            }
        }
    }
    if let Sort::Seq(_) = b {
        if let Sort::Uninterpreted(name) = a {
            let family = normalize_structural_sort_family(name);
            if family == "Seq" {
                return Some(b.clone()); // prefer native Seq
            }
        }
    }

    // Case 4: Seq vs Datatype collection-model (e.g., Seq(Int) vs Datatype(Vec)).
    // When the Datatype represents a collection type that trust-wp models as Seq,
    // prefer the native Seq sort — it is the canonical encoding sort post-#2080.
    // Without this, Datatype(Vec) from struct layout extraction wins over Seq(Int)
    // from the encoding path, causing sort mismatches in Seq operations. (#2699)
    if let Sort::Seq(_) = a {
        if let Sort::Datatype(dt) = b {
            let family = normalize_structural_sort_family(&dt.name);
            if family == "Seq" {
                return Some(a.clone()); // prefer native Seq
            }
        }
    }
    if let Sort::Seq(_) = b {
        if let Sort::Datatype(dt) = a {
            let family = normalize_structural_sort_family(&dt.name);
            if family == "Seq" {
                return Some(b.clone()); // prefer native Seq
            }
        }
    }

    // Case 4b: Seq(X) vs Seq(Y) where element sorts differ.
    // Both are native Seq sorts — prefer Seq(Int) as the canonical element
    // sort, or pick the first arbitrarily if neither is Seq(Int). (#2699)
    if let (Sort::Seq(elem_a), Sort::Seq(elem_b)) = (a, b) {
        if **elem_a == Sort::Int {
            return Some(a.clone());
        }
        if **elem_b == Sort::Int {
            return Some(b.clone());
        }
        return Some(a.clone());
    }

    // Case 5: Two Datatype sorts in the same family.
    if let (Sort::Datatype(dt_a), Sort::Datatype(dt_b)) = (a, b) {
        let family_a = ite_sort_family(&dt_a.name);
        let family_b = ite_sort_family(&dt_b.name);
        if family_a == family_b {
            // Prefer the more specific name (longer, monomorphized).
            return if dt_a.name.len() >= dt_b.name.len() {
                Some(a.clone())
            } else {
                Some(b.clone())
            };
        }
    }

    // Case 6: Datatype alias vs Uninterpreted family.
    // If direct family comparison above missed a synthesized `Adt_*` enum
    // name, consult the alias registry and prefer the native Datatype sort
    // when its registered source type matches the Uninterpreted family. (#2699)
    if let (Sort::Datatype(dt), Sort::Uninterpreted(name)) = (a, b) {
        let bare = bare_sort_name(&dt.name);
        if let Some(alias) = resolve_adt_family_alias(bare) {
            let alias_family = normalize_structural_sort_family(&alias);
            let name_family = normalize_structural_sort_family(name);
            if alias_family == name_family {
                return Some(a.clone());
            }
        }
    }
    if let (Sort::Uninterpreted(name), Sort::Datatype(dt)) = (a, b) {
        let bare = bare_sort_name(&dt.name);
        if let Some(alias) = resolve_adt_family_alias(bare) {
            let alias_family = normalize_structural_sort_family(&alias);
            let name_family = normalize_structural_sort_family(name);
            if alias_family == name_family {
                return Some(b.clone());
            }
        }
    }

    // Case 7: TypeParam vs concrete sort.
    // When one sort is a type parameter placeholder (__trust_wp_typaram::T) and
    // the other is concrete, prefer the concrete sort. TypeParam is a generic
    // placeholder that provides no sort information; the concrete sort from
    // the other branch is always more informative. (#2699)
    fn is_type_param(sort: &Sort) -> bool {
        matches!(sort, Sort::Uninterpreted(name) if name.starts_with("__trust_wp_typaram::"))
    }
    if is_type_param(a) && !is_type_param(b) {
        return Some(b.clone());
    }
    if is_type_param(b) && !is_type_param(a) {
        return Some(a.clone());
    }
    // Case 8: Both TypeParam but different names (e.g., T vs U).
    // Both are placeholders; pick the first arbitrarily so the caller gets a
    // unified sort instead of falling through to Sort::Int. (#2699)
    if is_type_param(a) && is_type_param(b) {
        return Some(a.clone());
    }

    None
}

/// Map a sort name to its canonical ADT family for Ite/Match resolution.
fn ite_sort_family(name: &str) -> String {
    let bare = bare_sort_name(name);

    // Strip Adt_ prefix for synthesized datatype names.
    if let Some(suffix) = bare.strip_prefix("Adt_") {
        let segments: Vec<&str> = suffix.split('_').collect();
        if segments.iter().any(|s| *s == "Some" || *s == "None") {
            return "Option".to_string();
        }
        if segments.iter().any(|s| *s == "Ok" || *s == "Err") {
            return "Result".to_string();
        }
        if suffix == "Cons_Nil" {
            return "List".to_string();
        }
    }
    // Recover the original user-defined enum family for synthesized `Adt_*`
    // names before falling back to raw-name comparison. (#2699)
    if let Some(alias) = resolve_adt_family_alias(bare) {
        if alias != bare {
            return normalize_structural_sort_family(&alias);
        }
    }
    match bare {
        "Option" => "Option".to_string(),
        _ if bare.starts_with("Option") => "Option".to_string(),
        "ResultIntInt" | "Result" => "Result".to_string(),
        // Tuple family: TupleN sorts from different paths share one family
        // so cross-sort-type resolution unifies them. (#2699)
        _ if bare.starts_with("Tuple")
            && bare.len() > 5
            && bare[5..].chars().all(|c| c.is_ascii_digit()) =>
        {
            bare.to_string()
        }
        // Seq-model types: normalize to Seq family so Uninterpreted("Vec")
        // and Seq(Int) resolve correctly in ite_sort_family. (#2699)
        "Vec" | "VecDeque" | "Seq" | "LinkedList" => "Seq".to_string(),
        // FMap-model types. (#2699)
        "HashMap" | "GhostMap" | "FMap" => "FMap".to_string(),
        _ => bare.to_string(),
    }
}

fn bare_sort_name(name: &str) -> &str {
    name.rsplit("::").next().unwrap_or(name)
}

pub(crate) fn infer_expr_sort(expr: &PureExpr) -> Sort {
    let mut cache_mode = InferExprSortMode::Uncached;
    infer_expr_sort_impl(expr, &mut cache_mode)
}

pub(in crate::encoder) fn infer_expr_sort_cached(
    expr: &PureExpr,
    cache: &mut InferExprSortCache,
) -> Sort {
    let mut cache_mode = InferExprSortMode::Cached(cache);
    infer_expr_sort_impl(expr, &mut cache_mode)
}

#[cfg(test)]
mod tests;
