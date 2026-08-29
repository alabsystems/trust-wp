// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Sort coercion helpers for heterogeneous branch and operand encoding.

use std::{
    cell::RefCell,
    collections::HashMap,
    sync::atomic::{AtomicU64, Ordering},
};

use ay_dpll::api::{Solver, Sort, Term};
use tracing::debug;

use super::sort_inference::{
    ay_sort_to_expr_sort, canonical_sort, expr_sort_to_ay_sort, unit_sort, CanonicalSort,
};
use crate::encoder::unsoundness;

std::thread_local! {
    // Match encoding synthesizes `Adt_*` names from constructor sets, while
    // other encoder paths still see the source enum name. Keep a thread-local
    // alias map so family resolution can bridge those names safely. (#2699)
    static ADT_FAMILY_ALIASES: RefCell<HashMap<String, String>> = RefCell::new(HashMap::new());
}

/// Register a synthesized ADT name as an alias for its original type name.
///
/// This lets sort-family resolution recover user-defined enum families when
/// one path sees `Adt_Cons_Nil` and another still sees `List`. (#2699)
pub(crate) fn register_adt_family_alias(adt_name: &str, type_name: &str) {
    ADT_FAMILY_ALIASES.with(|aliases| {
        aliases
            .borrow_mut()
            .insert(adt_name.to_string(), type_name.to_string());
    });
}

/// Resolve a synthesized ADT family alias back to its original type name.
///
/// Used by sort-family coercion to relate `Adt_*` datatype names to the
/// user-defined enum name they were synthesized from. (#2699)
pub(crate) fn resolve_adt_family_alias(name: &str) -> Option<String> {
    ADT_FAMILY_ALIASES.with(|aliases| aliases.borrow().get(name).cloned())
}

/// Coerce two terms to the same sort for use in an `ite` or `eq` expression.
///
/// ay-dpll requires both ite branches (and eq operands) to have the same sort.
/// Enum matches can produce heterogeneous sorts: e.g., `Cons(x, rest) => (x, rest)`
/// is Tuple2, while `Nil => ()` is Unit or `Nil => default` is Int.
///
/// Strategy (ordered by priority):
/// 1. Unit vs Int: coerce Unit to Int(0) (Unit carries no information)
/// 2. Bool vs Int: coerce Bool to Int via `ite(bool, 1, 0)` (preserves value)
/// 3. Unit vs other: coerce Unit to fresh unconstrained constant of the other sort
/// 4. Bool vs other: coerce Bool to fresh unconstrained constant of the other sort
/// 5. Int vs other: coerce Int to fresh unconstrained constant of the other sort
/// 6. other vs other: coerce second to fresh unconstrained constant of the first sort
///
/// Bool is handled before Int because Bool→Int preserves the boolean value as
/// 0/1 (lossless), while the generic Int/other→fresh path discards it. (#2077)
///
/// Using unconstrained constants is sound: ay won't derive false conclusions
/// about the value in the mismatched branch.
pub(in crate::encoder) fn coerce_ite_sorts(
    solver: &mut Solver,
    a: Term,
    a_sort: Sort,
    b: Term,
    b_sort: Sort,
) -> (Term, Term) {
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let fresh = || {
        let id = COUNTER.fetch_add(1, Ordering::Relaxed);
        format!("__trust_wp_coerce_{id}")
    };

    if a_sort == b_sort {
        return (a, b);
    }

    let unit = unit_sort();

    // --- Unit coercion (Unit carries no information) ---
    if a_sort == unit && b_sort == Sort::Int {
        (solver.int_const(0), b)
    } else if b_sort == unit && a_sort == Sort::Int {
        (a, solver.int_const(0))
    } else if a_sort == unit {
        // Unit vs non-Int sort: fresh const is conservative (unconstrained). (#2231)
        unsoundness::increment(unsoundness::UnsoundnessCategory::SortCoercionBridge);
        (solver.declare_const(&fresh(), b_sort), b)
    } else if b_sort == unit {
        unsoundness::increment(unsoundness::UnsoundnessCategory::SortCoercionBridge);
        (a, solver.declare_const(&fresh(), a_sort))
    }
    // --- Bool coercion (Bool→Int is lossless via ite(b,1,0)) ---
    else if a_sort == Sort::Bool && b_sort == Sort::Int {
        (bool_to_int(solver, a), b)
    } else if b_sort == Sort::Bool && a_sort == Sort::Int {
        (a, bool_to_int(solver, b))
    } else if a_sort == Sort::Bool {
        // Bool vs non-Int/non-Unit (e.g., Tuple2): fresh const is conservative. (#2231, #2353)
        unsoundness::increment(unsoundness::UnsoundnessCategory::SortCoercionBridge);
        (solver.declare_const(&fresh(), b_sort), b)
    } else if b_sort == Sort::Bool {
        unsoundness::increment(unsoundness::UnsoundnessCategory::SortCoercionBridge);
        (a, solver.declare_const(&fresh(), a_sort))
    }
    // --- Int↔Real coercion (lossless promotion to Real) ---
    // IntToFloat identity (#1802) passes Int PureExprs to Float locals.
    // When these appear in equality/Ite with Real-sorted terms, promote
    // Int→Real via int_to_real rather than losing the value with a fresh
    // constant. (#2353)
    else if a_sort == Sort::Int && b_sort == Sort::Real {
        (solver.int_to_real(a), b)
    } else if b_sort == Sort::Int && a_sort == Sort::Real {
        (a, solver.int_to_real(b))
    }
    // --- TypeParam coercion (TypeParam is a generic placeholder) ---
    // When one sort is a __trust_wp_typaram::* sort and the other is concrete,
    // bridge the TypeParam side to the concrete sort via fresh constant.
    // TypeParam carries no type information; the concrete sort is always
    // preferable. This parallels select_legacy_type_param_sort_target
    // but handles the case at the term level rather than just the sort
    // selection level. (#2699)
    else if is_type_param_coercion(&a_sort, &b_sort) {
        unsoundness::increment(unsoundness::UnsoundnessCategory::SortCoercionBridge);
        // Prefer the non-TypeParam sort
        if is_type_param_sort_name(&a_sort) {
            (solver.declare_const(&fresh(), b_sort), b)
        } else {
            (a, solver.declare_const(&fresh(), a_sort))
        }
    }
    // --- Structural non-Int coercion (related sort families) ---
    else if let Some(target_sort) = select_structural_sort_target(&a_sort, &b_sort) {
        // When one operand is being replaced by a fresh constant, track the
        // approximation. This covers Int-vs-structural coercion that was
        // previously handled by the Int-vs-complex path below (#2231).
        unsoundness::increment(unsoundness::UnsoundnessCategory::SortCoercionBridge);
        if target_sort == a_sort {
            (a, solver.declare_const(&fresh(), a_sort))
        } else {
            (solver.declare_const(&fresh(), b_sort), b)
        }
    }
    // --- Int coercion (Int vs complex sort: fresh const) ---
    // Int is the default/unknown sort. Bridging to complex sort uses an
    // unconstrained fresh constant — conservative, cannot produce false
    // proofs. Reclassified from HIGH to LOW per #2231.
    else if a_sort == Sort::Int {
        debug!(
            "[TRUST_WP_DEBUG] coerce_ite_sorts Int-vs-complex: a_sort={:?} b_sort={:?}",
            a_sort, b_sort
        );

        unsoundness::increment(unsoundness::UnsoundnessCategory::SortCoercionBridge);
        (solver.declare_const(&fresh(), b_sort), b)
    }
    // --- Fallback: b is Int, or both are non-Int/non-Bool/non-Unit ---
    // Keep a, coerce b to a's sort. Fresh const is conservative. (#2231)
    else {
        debug!(
            "[TRUST_WP_DEBUG] coerce_ite_sorts general-fallback: a_sort={:?} b_sort={:?}",
            a_sort, b_sort
        );

        unsoundness::increment(unsoundness::UnsoundnessCategory::SortCoercionBridge);
        (a, solver.declare_const(&fresh(), a_sort))
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd)]
enum StructuralSortStrength {
    Bare,
    Qualified,
    EncodingAlias,
    NativeDatatype,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct StructuralSortDescriptor {
    family: String,
    strength: StructuralSortStrength,
}

pub(crate) fn select_structural_sort_target(a_sort: &Sort, b_sort: &Sort) -> Option<Sort> {
    if a_sort == b_sort {
        return Some(a_sort.clone());
    }

    if matches!(
        (a_sort, b_sort),
        (Sort::Int, Sort::Real) | (Sort::Real, Sort::Int)
    ) {
        return Some(Sort::Real);
    }

    if let Some(sort) = select_mutref_carrier_target(a_sort, b_sort) {
        return Some(sort);
    }

    if let Some(sort) = select_legacy_type_param_sort_target(a_sort, b_sort) {
        return Some(sort);
    }

    if matches!(a_sort, Sort::Uninterpreted(name) if name == "Seq") && is_seq_family_sort(b_sort) {
        return Some(a_sort.clone());
    }
    if matches!(b_sort, Sort::Uninterpreted(name) if name == "Seq") && is_seq_family_sort(a_sort) {
        return Some(b_sort.clone());
    }

    // Native Seq vs Datatype(collection) special case: when one side is the
    // native Sort::Seq and the other is a Datatype whose family is "Seq",
    // always prefer the native Seq sort. Sort::Seq is the canonical encoding
    // sort for all collection types post-#2080; the Datatype comes from struct
    // layout extraction and should be coerced to Seq for encoding. (#2699)
    if let Sort::Seq(_) = a_sort {
        if let Sort::Datatype(dt) = b_sort {
            if normalize_structural_sort_family(&dt.name) == "Seq" {
                return Some(a_sort.clone());
            }
        }
    }
    if let Sort::Seq(_) = b_sort {
        if let Sort::Datatype(dt) = a_sort {
            if normalize_structural_sort_family(&dt.name) == "Seq" {
                return Some(b_sort.clone());
            }
        }
    }

    // Seq(X) vs Seq(Y) where X != Y: both are native Seq sorts with different
    // element sorts. Prefer Seq(Int) as the canonical element sort since Int is
    // the universal encoding sort for collection elements in trust-wp. If neither
    // is Seq(Int), pick the first arbitrarily — the sort coercion bridge in
    // coerce_ite_sorts will create a fresh constant for the mismatched side.
    // Without this, two Seq sorts with different element sorts fall through to
    // the structural descriptor comparison, which treats them both as "Seq"
    // family with equal strength and picks the first — but the match arms below
    // cannot reach this case because a_sort != b_sort was already checked. (#2699)
    if let (Sort::Seq(elem_a), Sort::Seq(elem_b)) = (a_sort, b_sort) {
        if **elem_a == Sort::Int {
            return Some(a_sort.clone());
        }
        if **elem_b == Sort::Int {
            return Some(b_sort.clone());
        }
        // Neither is Seq(Int) — pick the first arbitrarily.
        return Some(a_sort.clone());
    }

    let a_desc = structural_sort_descriptor(a_sort);
    let b_desc = structural_sort_descriptor(b_sort);
    match (a_desc, b_desc) {
        (Some(a_d), Some(b_d)) => {
            if a_d.family == b_d.family {
                if a_d.strength >= b_d.strength {
                    Some(a_sort.clone())
                } else {
                    Some(b_sort.clone())
                }
            } else if synthesized_user_adt_family_fallback(a_sort, &b_d.family).is_some() {
                Some(b_sort.clone())
            } else if synthesized_user_adt_family_fallback(b_sort, &a_d.family).is_some() {
                Some(a_sort.clone())
            } else {
                None
            }
        }
        // When one side is Int (the universal fallback from sort inference)
        // and the other has a structural descriptor, prefer the structural
        // sort. Int is not a genuine sort choice — it means "inference could
        // not determine the sort." Using the structural sort for equality
        // resolution avoids the HIGH SortFallbackToInt demotion that would
        // otherwise fire in encode_binop for Eq/Ne. (#2231)
        (Some(_), None) if *b_sort == Sort::Int => Some(a_sort.clone()),
        (None, Some(_)) if *a_sort == Sort::Int => Some(b_sort.clone()),
        // Bool vs structural: both are valid sorts. Prefer Bool so that
        // eq_or_iff uses `iff` (logically correct for Boolean equality).
        (Some(_), None) if *b_sort == Sort::Bool => Some(Sort::Bool),
        (None, Some(_)) if *a_sort == Sort::Bool => Some(Sort::Bool),
        // --- Non-structural fallback cases (None, None) ---
        // Int vs Bool: Int is the universal "unknown" sort from inference
        // fallback. When the other side is Bool, prefer Bool so eq_or_iff
        // uses `iff` (logically correct for Boolean equality). Without this,
        // the Eq/Ne path in operators.rs fires SortFallbackToInt and uses
        // `eq` instead of `iff`, which can miss logical equivalence. (#2663)
        (None, None) if *a_sort == Sort::Bool && *b_sort == Sort::Int => Some(Sort::Bool),
        (None, None) if *a_sort == Sort::Int && *b_sort == Sort::Bool => Some(Sort::Bool),
        _ => None,
    }
}

pub(crate) fn select_mutref_carrier_target(a_sort: &Sort, b_sort: &Sort) -> Option<Sort> {
    fn mutref_inner_sort(sort: &Sort) -> Option<Sort> {
        match ay_sort_to_expr_sort(sort) {
            Some(trust_wp_core::formula::ExprSort::MutRef(inner)) => {
                Some(expr_sort_to_ay_sort(&inner))
            }
            _ => None,
        }
    }

    if mutref_inner_sort(a_sort).as_ref() == Some(b_sort) {
        return Some(a_sort.clone());
    }
    if mutref_inner_sort(b_sort).as_ref() == Some(a_sort) {
        return Some(b_sort.clone());
    }
    None
}

fn select_legacy_type_param_sort_target(a_sort: &Sort, b_sort: &Sort) -> Option<Sort> {
    fn uninterpreted_name(sort: &Sort) -> Option<&str> {
        match sort {
            Sort::Uninterpreted(name) => Some(name.as_str()),
            _ => None,
        }
    }

    fn legacy_type_param_name(name: &str) -> Option<&str> {
        name.strip_prefix("__trust_wp_typaram::")
    }

    fn is_type_param_sort(sort: &Sort) -> bool {
        matches!(sort, Sort::Uninterpreted(name) if name.starts_with("__trust_wp_typaram::"))
    }

    // Case 1: Both Uninterpreted — original path.
    if let (Some(a_name), Some(b_name)) = (uninterpreted_name(a_sort), uninterpreted_name(b_sort)) {
        match (
            legacy_type_param_name(a_name),
            legacy_type_param_name(b_name),
        ) {
            (Some(a_bare), Some(b_bare)) if a_bare == b_bare => return Some(a_sort.clone()),
            (Some(a_bare), None) if a_bare == b_name => return Some(a_sort.clone()),
            (None, Some(b_bare)) if a_name == b_bare => return Some(b_sort.clone()),
            _ => {}
        }
    }

    // Case 2: TypeParam vs concrete non-Uninterpreted sort.
    // TypeParam is a placeholder from generics. When paired with a concrete
    // sort (Datatype, Seq, Bool, etc.), always prefer the concrete sort —
    // the TypeParam provides no sort information beyond "some type T". (#2699)
    if is_type_param_sort(a_sort) && !is_type_param_sort(b_sort) {
        return Some(b_sort.clone());
    }
    if is_type_param_sort(b_sort) && !is_type_param_sort(a_sort) {
        return Some(a_sort.clone());
    }

    // Case 3: Both TypeParam but different names (e.g., __trust_wp_typaram::T
    // vs __trust_wp_typaram::U). Both are placeholders with no type information;
    // pick the first arbitrarily so the caller can proceed with a unified sort
    // instead of falling through to the general fallback which fires the HIGH
    // SortFallbackToInt demotion. (#2699)
    if is_type_param_sort(a_sort) && is_type_param_sort(b_sort) {
        return Some(a_sort.clone());
    }

    None
}

fn structural_sort_descriptor(sort: &Sort) -> Option<StructuralSortDescriptor> {
    let (name, strength) = match sort {
        Sort::Datatype(dt) => {
            // Native Datatype sorts from match encoding. Classify by name
            // to enable cross-sort coercion with Uninterpreted counterparts
            // (e.g., Datatype(OptionInt) ↔ Uninterpreted("OptionInt")). (#2231)
            let bare = dt.name.as_str();
            let family = normalize_structural_sort_family(bare);
            return Some(StructuralSortDescriptor {
                family,
                strength: StructuralSortStrength::NativeDatatype,
            });
        }
        // Native Seq sort — canonical encoding sort post-#2080 migration.
        Sort::Seq(_) => {
            return Some(StructuralSortDescriptor {
                family: "Seq".to_string(),
                strength: StructuralSortStrength::EncodingAlias,
            });
        }
        Sort::Uninterpreted(name) => {
            let bare = name.rsplit("::").next().unwrap_or(name);
            let strength = match bare {
                "OptionInt" | "ResultIntInt" => StructuralSortStrength::EncodingAlias,
                // Canonical model sorts: prefer these over concrete types
                // in structural coercion (FMap over HashMap). (#2116)
                // Mixed datatype VCs may use an uninterpreted Seq carrier to
                // avoid ay-dpll's native Seq+datatype unsupported fragment.
                "Seq" | "FMap" | "Mapping" => StructuralSortStrength::EncodingAlias,
                // Tuple sorts (Tuple2, Tuple3, etc.) from tuple encoding.
                // These are structural sorts with a known family. (#2699)
                _ if bare.starts_with("Tuple")
                    && bare.len() > 5
                    && bare[5..].chars().all(|c| c.is_ascii_digit()) =>
                {
                    StructuralSortStrength::EncodingAlias
                }
                _ if bare != name => StructuralSortStrength::Qualified,
                _ => StructuralSortStrength::Bare,
            };
            (name.as_str(), strength)
        }
        _ => return None,
    };

    match canonical_sort(name) {
        CanonicalSort::Uninterpreted(_) => Some(StructuralSortDescriptor {
            family: normalize_structural_sort_family(name),
            strength,
        }),
        // Seq-model types (Vec, VecDeque, Seq) share the "Seq" family.
        // FMap-model types (HashMap, GhostMap, FMap) share the "FMap" family.
        // Mapping types share the "Mapping" family.
        // Without this, Vec↔Seq coercion falls through to the general fallback
        // and fires SortFallbackToInt, causing demotion of otherwise-verified
        // proofs (e.g., bug/two_phase.rs). (#2116)
        CanonicalSort::Seq | CanonicalSort::FMap | CanonicalSort::Mapping => {
            Some(StructuralSortDescriptor {
                family: normalize_structural_sort_family(name),
                strength,
            })
        }
        CanonicalSort::Int => None,
    }
}

pub(in crate::encoder) fn normalize_structural_sort_family(name: &str) -> String {
    let bare = name.rsplit("::").next().unwrap_or(name);
    match bare {
        "Option" => "Option".to_string(),
        _ if bare.starts_with("Option") => "Option".to_string(),
        "ResultIntInt" | "Result" => "Result".to_string(),
        // Seq-model types: Vec, VecDeque, Seq all model as Seq (#2116)
        "Vec" | "VecDeque" | "Seq" | "LinkedList" => "Seq".to_string(),
        // FMap-model types: HashMap, GhostMap all model as FMap (#2116)
        "HashMap" | "GhostMap" | "FMap" => "FMap".to_string(),
        // Tuple family: TupleN names from different encoding paths share a
        // family so Tuple2 from struct layout coerces to Tuple2 from tuple
        // constructor. Without this, two Tuple2-named sorts from different
        // ay sort constructors (Datatype vs Uninterpreted) fall through to
        // the general fallback and create fresh constants. (#2699)
        _ if bare.starts_with("Tuple") && bare[5..].chars().all(|c| c.is_ascii_digit()) => {
            bare.to_string()
        }
        // Mapping stays as-is (single canonical name)
        _ => {
            // Synthesized ADT names like "Adt_Some_None" → Option family,
            // "Adt_Ok_Err" → Result family, for coercion with their
            // Uninterpreted counterparts. (#2231)
            if let Some(suffix) = bare.strip_prefix("Adt_") {
                let segments: Vec<&str> = suffix.split('_').collect();
                if segments.iter().any(|s| *s == "Some" || *s == "None") {
                    return "Option".to_string();
                }
                if segments.iter().any(|s| *s == "Ok" || *s == "Err") {
                    return "Result".to_string();
                }
                // For user-defined enums, prefer the registered source type
                // family when available; otherwise fall back to the joined
                // constructor name without the synthetic `Adt_` prefix. (#2699)
                if let Some(alias) = resolve_adt_family_alias(bare) {
                    if alias != bare {
                        return normalize_structural_sort_family(&alias);
                    }
                }
                if suffix == "Cons_Nil" {
                    return "List".to_string();
                }
                return suffix.to_string();
            }
            if let Some(alias) = resolve_adt_family_alias(bare) {
                if alias != bare {
                    return normalize_structural_sort_family(&alias);
                }
            }
            bare.to_string()
        }
    }
}

/// Check if a ay Sort belongs to the Seq family (collection types modeled as Seq).
///
/// Returns `true` for:
/// - `Sort::Seq(_)` — the native Seq sort (canonical post-#2080)
/// - `Sort::Uninterpreted("Vec")` / `Sort::Uninterpreted("VecDeque")` etc.
/// - `Sort::Datatype(Vec)` / `Sort::Datatype(LinkedList)` etc.
///
/// Used by `harmonize_eq_or_ite_terms` to decide whether to bridge a term
/// to Seq via `coerce_to_seq` instead of creating a fresh unconstrained
/// constant that discards the value. (#2699)
pub(crate) fn is_seq_family_sort(sort: &Sort) -> bool {
    match sort {
        Sort::Seq(_) => true,
        Sort::Uninterpreted(name) => normalize_structural_sort_family(name) == "Seq",
        Sort::Datatype(dt) => normalize_structural_sort_family(&dt.name) == "Seq",
        _ => false,
    }
}

/// Check if two sorts belong to the same structural family but have
/// different ay representations.
///
/// Returns `Some(family_name)` when both sorts resolve to the same family
/// via `normalize_structural_sort_family` but differ as ay `Sort` values.
/// This catches:
/// - `Datatype(Adt_Some_None)` vs `Uninterpreted("OptionInt")` → `"Option"`
/// - `Datatype(Adt_Ok_Err)` vs `Uninterpreted("ResultIntInt")` → `"Result"`
/// - `Datatype(Adt_Cons_Nil)` vs `Uninterpreted("List")` → `"List"`
/// - Two different Datatype sorts from the same user-defined enum
///
/// Used by `harmonize_eq_or_ite_terms` to decide when a UF bridge should be
/// used instead of a fresh unconstrained constant. (#2699)
pub(crate) fn same_structural_family(a: &Sort, b: &Sort) -> Option<String> {
    if a == b {
        return None; // same sort, no bridging needed
    }
    let a_family = structural_sort_family_name(a)?;
    let b_family = structural_sort_family_name(b)?;
    if a_family == b_family {
        Some(a_family)
    } else if let Some(family) = synthesized_user_adt_family_fallback(a, &b_family) {
        Some(family)
    } else {
        synthesized_user_adt_family_fallback(b, &a_family)
    }
}

fn synthesized_user_adt_family_fallback(sort: &Sort, other_family: &str) -> Option<String> {
    let name = match sort {
        Sort::Datatype(dt) => dt.name.as_str(),
        Sort::Uninterpreted(name) => name.as_str(),
        _ => return None,
    };
    let bare = name.rsplit("::").next().unwrap_or(name);
    let suffix = bare.strip_prefix("Adt_")?;
    let segments = suffix.split('_').collect::<Vec<_>>();
    if segments.iter().any(|s| *s == "Some" || *s == "None")
        || segments.iter().any(|s| *s == "Ok" || *s == "Err")
        || other_family == "Option"
        || other_family == "Result"
        || other_family == "Seq"
        || other_family == "FMap"
        || other_family == "Mapping"
        || other_family.starts_with("Tuple")
        || other_family.starts_with("Adt_")
    {
        return None;
    }
    Some(other_family.to_string())
}

/// Extract the structural sort family name for a sort.
///
/// Returns `None` for scalar sorts (Int, Bool, Real) that have no
/// structural family. Returns the normalized family name for Datatype,
/// Uninterpreted, and Seq sorts. (#2699)
fn structural_sort_family_name(sort: &Sort) -> Option<String> {
    match sort {
        Sort::Datatype(dt) => Some(normalize_structural_sort_family(&dt.name)),
        Sort::Uninterpreted(name) => Some(normalize_structural_sort_family(name)),
        Sort::Seq(_) => Some("Seq".to_string()),
        _ => None,
    }
}

/// Convert a Bool-sorted term to Int via `ite(b, 1, 0)`.
///
/// Shared helper for `coerce_ite_sorts` and `coerce_to_numeric`, ensuring
/// Bool→Int coercion uses a single code path everywhere. (#2610)
fn bool_to_int(solver: &mut Solver, term: Term) -> Term {
    let one = solver.int_const(1);
    let zero = solver.int_const(0);
    solver.ite(term, one, zero)
}

fn is_type_param_sort_name(sort: &Sort) -> bool {
    matches!(sort, Sort::Uninterpreted(name) if name.starts_with("__trust_wp_typaram::"))
}

fn is_type_param_coercion(a: &Sort, b: &Sort) -> bool {
    (is_type_param_sort_name(a) && !is_type_param_sort_name(b))
        || (is_type_param_sort_name(b) && !is_type_param_sort_name(a))
}

/// Mode for numeric operand coercion.
#[derive(Clone, Copy)]
pub(in crate::encoder) enum NumericOperandMode {
    IntOnly,
    IntOrReal,
}

/// Coerce arithmetic/comparison operands into a ay-accepted numeric sort.
///
/// ay-dpll's arithmetic/comparison operators and trust-wp's integer-only
/// bitwise UF declarations require numeric operands. This function ensures
/// both operands are in the target numeric sort (Int or Real), applying
/// Bool→Int promotion via `bool_to_int` (same path as `coerce_ite_sorts`)
/// and fresh-constant fallback with `SortFallbackToInt` tracking for
/// non-numeric sorts.
///
/// Moved from `operators.rs` to centralize all sort coercion in one module,
/// preventing the sort inconsistency that caused #2608. (#2610)
pub(in crate::encoder) fn coerce_to_numeric(
    solver: &mut Solver,
    l: Term,
    r: Term,
    mode: NumericOperandMode,
) -> (Term, Term) {
    static INT_COERCE_COUNTER: AtomicU64 = AtomicU64::new(0);

    let l_sort = solver.get_sort(l);
    let r_sort = solver.get_sort(r);

    let allow_real = matches!(mode, NumericOperandMode::IntOrReal);
    let target_sort = if allow_real && (l_sort == Sort::Real || r_sort == Sort::Real) {
        Sort::Real
    } else {
        Sort::Int
    };
    let l_ok = l_sort == Sort::Int || (allow_real && l_sort == Sort::Real);
    let r_ok = r_sort == Sort::Int || (allow_real && r_sort == Sort::Real);

    // Fast path: both operands already numeric and match the target sort.
    if l_ok && r_ok && l_sort == target_sort && r_sort == target_sort {
        return (l, r);
    }

    // Bool→Int coercion via shared `bool_to_int` helper — same ite(b,1,0)
    // path as coerce_ite_sorts. (#2558, #2610)
    let (l, l_sort) = if l_sort == Sort::Bool && target_sort == Sort::Int {
        (bool_to_int(solver, l), Sort::Int)
    } else {
        (l, l_sort)
    };
    let (r, r_sort) = if r_sort == Sort::Bool && target_sort == Sort::Int {
        (bool_to_int(solver, r), Sort::Int)
    } else {
        (r, r_sort)
    };

    // Recompute ok flags after Bool→Int promotion.
    let l_ok = l_sort == Sort::Int || (allow_real && l_sort == Sort::Real);
    let r_ok = r_sort == Sort::Int || (allow_real && r_sort == Sort::Real);

    // Fast path after Bool promotion: both now numeric.
    if l_ok && r_ok && l_sort == target_sort && r_sort == target_sort {
        return (l, r);
    }

    // When both operands are the same non-numeric term, reuse one fresh
    // numeric constant for both sides to preserve reflexivity. (#2285)
    // Fresh constant is unconstrained — conservative. Reclassified LOW per #2231.
    if !l_ok && !r_ok && l == r {
        unsoundness::increment(unsoundness::UnsoundnessCategory::SortCoercionBridge);
        let id = INT_COERCE_COUNTER.fetch_add(1, Ordering::Relaxed);
        let shared =
            solver.declare_const(&format!("__trust_wp_num_coerce_{id}"), target_sort.clone());
        return (shared, shared);
    }

    let l = if l_ok {
        if target_sort == Sort::Real && l_sort == Sort::Int {
            solver.int_to_real(l)
        } else {
            l
        }
    } else {
        // Non-numeric operand bridged to numeric via fresh const. Conservative. (#2231)
        unsoundness::increment(unsoundness::UnsoundnessCategory::SortCoercionBridge);
        let id = INT_COERCE_COUNTER.fetch_add(1, Ordering::Relaxed);
        solver.declare_const(&format!("__trust_wp_num_coerce_{id}"), target_sort.clone())
    };
    let r = if r_ok {
        if target_sort == Sort::Real && r_sort == Sort::Int {
            solver.int_to_real(r)
        } else {
            r
        }
    } else {
        unsoundness::increment(unsoundness::UnsoundnessCategory::SortCoercionBridge);
        let id = INT_COERCE_COUNTER.fetch_add(1, Ordering::Relaxed);
        solver.declare_const(&format!("__trust_wp_num_coerce_{id}"), target_sort)
    };

    (l, r)
}

#[cfg(test)]
mod tests {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Logic, Sort};
    use ntest::timeout;

    use super::*;

    fn make_datatype(name: &str) -> Sort {
        Sort::Datatype(DatatypeSort {
            name: name.to_string(),
            constructors: vec![],
        })
    }

    fn make_option_dt() -> Sort {
        Sort::Datatype(DatatypeSort {
            name: "Adt_Some_None".to_string(),
            constructors: vec![
                DatatypeConstructor {
                    name: "Some".to_string(),
                    fields: vec![DatatypeField {
                        name: "0".to_string(),
                        sort: Sort::Int,
                    }],
                },
                DatatypeConstructor {
                    name: "None".to_string(),
                    fields: vec![],
                },
            ],
        })
    }

    fn make_result_dt() -> Sort {
        Sort::Datatype(DatatypeSort {
            name: "Adt_Ok_Err".to_string(),
            constructors: vec![
                DatatypeConstructor {
                    name: "Ok".to_string(),
                    fields: vec![DatatypeField {
                        name: "0".to_string(),
                        sort: Sort::Int,
                    }],
                },
                DatatypeConstructor {
                    name: "Err".to_string(),
                    fields: vec![DatatypeField {
                        name: "0".to_string(),
                        sort: Sort::Int,
                    }],
                },
            ],
        })
    }

    // --- same_structural_family tests ---

    #[test]
    #[timeout(5000)]
    fn test_same_family_datatype_vs_uninterpreted_option() {
        let dt = make_option_dt();
        let ui = Sort::Uninterpreted("OptionInt".to_string());
        let family = same_structural_family(&dt, &ui);
        assert_eq!(family, Some("Option".to_string()));
    }

    #[test]
    #[timeout(5000)]
    fn test_same_family_datatype_vs_uninterpreted_option_reversed() {
        let dt = make_option_dt();
        let ui = Sort::Uninterpreted("OptionInt".to_string());
        let family = same_structural_family(&ui, &dt);
        assert_eq!(family, Some("Option".to_string()));
    }

    #[test]
    #[timeout(5000)]
    fn test_same_family_result_dt_vs_uninterpreted() {
        let dt = make_result_dt();
        let ui = Sort::Uninterpreted("ResultIntInt".to_string());
        let family = same_structural_family(&dt, &ui);
        assert_eq!(family, Some("Result".to_string()));
    }

    #[test]
    #[timeout(5000)]
    fn test_same_family_seq_vs_uninterpreted_vec() {
        let seq = Sort::seq(Sort::Int);
        let vec_ui = Sort::Uninterpreted("Vec".to_string());
        let family = same_structural_family(&seq, &vec_ui);
        assert_eq!(family, Some("Seq".to_string()));
    }

    #[test]
    #[timeout(5000)]
    fn test_same_family_different_families_returns_none() {
        let option_dt = make_option_dt();
        let result_ui = Sort::Uninterpreted("ResultIntInt".to_string());
        let family = same_structural_family(&option_dt, &result_ui);
        assert_eq!(family, None);
    }

    #[test]
    #[timeout(5000)]
    fn test_same_family_int_vs_datatype_returns_none() {
        let dt = make_option_dt();
        let family = same_structural_family(&Sort::Int, &dt);
        assert_eq!(family, None, "Int has no structural family");
    }

    #[test]
    #[timeout(5000)]
    fn test_same_family_identical_sorts_returns_none() {
        let ui = Sort::Uninterpreted("Option".to_string());
        let family = same_structural_family(&ui, &ui);
        assert_eq!(family, None, "identical sorts should return None");
    }

    #[test]
    #[timeout(5000)]
    fn test_same_family_tuple_sorts() {
        let tuple_dt = make_datatype("Tuple2");
        let tuple_ui = Sort::Uninterpreted("Tuple2".to_string());
        let family = same_structural_family(&tuple_dt, &tuple_ui);
        assert_eq!(family, Some("Tuple2".to_string()));
    }

    #[test]
    #[timeout(5000)]
    fn test_same_family_fmap_sorts() {
        let fmap_dt = make_datatype("HashMap");
        let fmap_ui = Sort::Uninterpreted("FMap".to_string());
        let family = same_structural_family(&fmap_dt, &fmap_ui);
        assert_eq!(family, Some("FMap".to_string()));
    }

    #[test]
    #[timeout(5000)]
    fn test_same_family_user_adt_with_alias() {
        // Register an alias so Adt_Cons_Nil resolves to List family
        register_adt_family_alias("Adt_Cons_Nil", "List");
        let dt = make_datatype("Adt_Cons_Nil");
        let ui = Sort::Uninterpreted("List".to_string());
        let family = same_structural_family(&dt, &ui);
        assert_eq!(family, Some("List".to_string()));
    }

    #[test]
    #[timeout(5000)]
    fn test_same_family_cons_nil_list_without_alias() {
        let dt = make_datatype("Adt_Cons_Nil");
        let ui = Sort::Uninterpreted("List".to_string());
        let family = same_structural_family(&dt, &ui);
        assert_eq!(
            family,
            Some("List".to_string()),
            "List fixtures may reach equality harmonization before ADT aliases are registered"
        );
    }

    #[test]
    #[timeout(5000)]
    fn test_same_family_uninterpreted_cons_nil_list_without_alias() {
        let synthesized = Sort::Uninterpreted("Adt_Cons_Nil".to_string());
        let source = Sort::Uninterpreted("List".to_string());
        let family = same_structural_family(&synthesized, &source);
        assert_eq!(family, Some("List".to_string()));
    }

    #[test]
    #[timeout(5000)]
    fn test_same_family_user_adt_uninterpreted_without_registered_alias() {
        let synth = Sort::Uninterpreted("Adt_Open_Closed".to_string());
        let source = Sort::Uninterpreted("GadgetState".to_string());
        let family = same_structural_family(&synth, &source);
        assert_eq!(family, Some("GadgetState".to_string()));
    }

    // --- select_structural_sort_target tests ---

    #[test]
    #[timeout(5000)]
    fn test_select_target_option_dt_vs_uninterpreted_prefers_datatype() {
        let dt = make_option_dt();
        let ui = Sort::Uninterpreted("Option".to_string());
        let target = select_structural_sort_target(&dt, &ui);
        // Datatype has NativeDatatype strength, Uninterpreted("Option") has Bare.
        // Should prefer the Datatype.
        assert!(target.is_some(), "same-family sorts should find a target");
        assert_eq!(target.unwrap(), dt, "should prefer Datatype sort");
    }

    #[test]
    #[timeout(5000)]
    fn test_select_target_int_vs_structural_prefers_structural() {
        let option_ui = Sort::Uninterpreted("OptionInt".to_string());
        let target = select_structural_sort_target(&Sort::Int, &option_ui);
        assert_eq!(
            target,
            Some(option_ui),
            "Int is universal fallback, prefer structural"
        );
    }

    #[test]
    #[timeout(5000)]
    fn test_select_target_bool_vs_structural_prefers_bool() {
        let option_ui = Sort::Uninterpreted("OptionInt".to_string());
        let target = select_structural_sort_target(&Sort::Bool, &option_ui);
        assert_eq!(
            target,
            Some(Sort::Bool),
            "Bool takes priority for eq_or_iff"
        );
    }

    #[test]
    #[timeout(5000)]
    fn test_select_target_seq_vs_datatype_vec() {
        let seq = Sort::seq(Sort::Int);
        let vec_dt = make_datatype("Vec");
        let target = select_structural_sort_target(&seq, &vec_dt);
        assert_eq!(target, Some(seq), "native Seq preferred over Datatype(Vec)");
    }

    #[test]
    #[timeout(5000)]
    fn test_select_target_typeparam_vs_datatype_prefers_datatype() {
        let typaram = Sort::Uninterpreted("__trust_wp_typaram::T".to_string());
        let dt = make_option_dt();
        let target = select_structural_sort_target(&typaram, &dt);
        assert_eq!(
            target,
            Some(dt),
            "TypeParam should yield to concrete Datatype"
        );
    }

    #[test]
    #[timeout(5000)]
    fn test_select_target_user_adt_uninterpreted_prefers_source_name() {
        let synth = Sort::Uninterpreted("Adt_Cold_Hot".to_string());
        let source = Sort::Uninterpreted("TemperatureState".to_string());
        let target = select_structural_sort_target(&synth, &source);
        assert_eq!(target, Some(source));
    }

    // --- normalize_structural_sort_family tests ---

    #[test]
    #[timeout(5000)]
    fn test_normalize_family_adt_some_none_is_option() {
        assert_eq!(normalize_structural_sort_family("Adt_Some_None"), "Option");
    }

    #[test]
    #[timeout(5000)]
    fn test_normalize_family_adt_ok_err_is_result() {
        assert_eq!(normalize_structural_sort_family("Adt_Ok_Err"), "Result");
    }

    #[test]
    #[timeout(5000)]
    fn test_normalize_family_vec_is_seq() {
        assert_eq!(normalize_structural_sort_family("Vec"), "Seq");
    }

    #[test]
    #[timeout(5000)]
    fn test_normalize_family_hashmap_is_fmap() {
        assert_eq!(normalize_structural_sort_family("HashMap"), "FMap");
    }

    #[test]
    #[timeout(5000)]
    fn test_normalize_family_tuple2_is_tuple2() {
        assert_eq!(normalize_structural_sort_family("Tuple2"), "Tuple2");
    }

    #[test]
    #[timeout(5000)]
    fn test_normalize_family_unknown_adt_with_alias() {
        register_adt_family_alias("Adt_Red_Blue", "Color");
        assert_eq!(normalize_structural_sort_family("Adt_Red_Blue"), "Color");
    }

    // --- is_seq_family_sort tests ---

    #[test]
    #[timeout(5000)]
    fn test_is_seq_family_native_seq() {
        assert!(is_seq_family_sort(&Sort::seq(Sort::Int)));
    }

    #[test]
    #[timeout(5000)]
    fn test_is_seq_family_uninterpreted_vec() {
        assert!(is_seq_family_sort(&Sort::Uninterpreted("Vec".to_string())));
    }

    #[test]
    #[timeout(5000)]
    fn test_is_seq_family_datatype_vec() {
        assert!(is_seq_family_sort(&make_datatype("Vec")));
    }

    #[test]
    #[timeout(5000)]
    fn test_is_not_seq_family_option() {
        assert!(!is_seq_family_sort(&Sort::Uninterpreted(
            "Option".to_string()
        )));
    }

    #[test]
    #[timeout(5000)]
    fn test_is_not_seq_family_int() {
        assert!(!is_seq_family_sort(&Sort::Int));
    }

    // --- coerce_ite_sorts tests ---

    #[test]
    #[timeout(5000)]
    fn test_coerce_ite_sorts_same_sort_noop() {
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let a = solver.int_const(1);
        let b = solver.int_const(2);
        let (ca, cb) = coerce_ite_sorts(&mut solver, a, Sort::Int, b, Sort::Int);
        // Same sort: should return originals unchanged
        assert_eq!(ca, a);
        assert_eq!(cb, b);
    }

    #[test]
    #[timeout(5000)]
    fn test_coerce_ite_sorts_unit_to_int() {
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let unit = solver.declare_const("u", unit_sort());
        let i = solver.int_const(42);
        let (ca, cb) = coerce_ite_sorts(&mut solver, unit, unit_sort(), i, Sort::Int);
        // Unit coerces to Int(0)
        assert_eq!(solver.get_sort(ca), Sort::Int);
        assert_eq!(cb, i);
    }

    #[test]
    #[timeout(5000)]
    fn test_coerce_ite_sorts_bool_to_int() {
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let b = solver.bool_const(true);
        let i = solver.int_const(1);
        let (ca, cb) = coerce_ite_sorts(&mut solver, b, Sort::Bool, i, Sort::Int);
        // Bool coerces to Int via ite(b, 1, 0)
        assert_eq!(solver.get_sort(ca), Sort::Int);
        assert_eq!(cb, i);
    }

    #[test]
    #[timeout(5000)]
    fn test_coerce_ite_sorts_int_to_real() {
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let i = solver.int_const(2);
        let r = solver.declare_const("r_val", Sort::Real);
        let (ca, cb) = coerce_ite_sorts(&mut solver, i, Sort::Int, r, Sort::Real);
        // Int promotes to Real via int_to_real
        assert_eq!(solver.get_sort(ca), Sort::Real);
        assert_eq!(cb, r);
    }

    #[test]
    #[timeout(5000)]
    fn test_coerce_ite_sorts_structural_family_creates_fresh() {
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let option_ui = Sort::Uninterpreted("OptionInt".to_string());
        let option_bare = Sort::Uninterpreted("Option".to_string());
        let a = solver.declare_const("a", option_ui.clone());
        let b = solver.declare_const("b", option_bare.clone());
        let (ca, cb) = coerce_ite_sorts(&mut solver, a, option_ui, b, option_bare);
        // Same family: select_structural_sort_target picks one, other gets fresh
        let ca_sort = solver.get_sort(ca);
        let cb_sort = solver.get_sort(cb);
        // Both should now have the same sort
        assert_eq!(
            ca_sort, cb_sort,
            "structural family coercion should produce matching sorts"
        );
    }

    #[test]
    #[timeout(5000)]
    fn test_coerce_ite_sorts_typeparam_vs_concrete_prefers_concrete() {
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let typaram = Sort::Uninterpreted("__trust_wp_typaram::T".to_string());
        let option_sort = Sort::Uninterpreted("OptionInt".to_string());
        let a = solver.declare_const("tp", typaram.clone());
        let b = solver.declare_const("opt", option_sort.clone());
        let (ca, cb) = coerce_ite_sorts(&mut solver, a, typaram, b, option_sort.clone());
        // TypeParam side should be replaced with fresh const of the concrete sort
        assert_eq!(solver.get_sort(ca), option_sort);
        assert_eq!(cb, b);
    }

    // --- TypeParam vs TypeParam (different names) tests ---

    #[test]
    #[timeout(5000)]
    fn test_select_target_two_different_typarams_resolves() {
        let t = Sort::Uninterpreted("__trust_wp_typaram::T".to_string());
        let u = Sort::Uninterpreted("__trust_wp_typaram::U".to_string());
        let target = select_structural_sort_target(&t, &u);
        assert!(
            target.is_some(),
            "two different TypeParam sorts should resolve to one"
        );
    }

    #[test]
    #[timeout(5000)]
    fn test_coerce_ite_sorts_two_different_typarams_produces_same_sort() {
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let t_sort = Sort::Uninterpreted("__trust_wp_typaram::T".to_string());
        let u_sort = Sort::Uninterpreted("__trust_wp_typaram::U".to_string());
        let a = solver.declare_const("tp_t", t_sort.clone());
        let b = solver.declare_const("tp_u", u_sort.clone());
        let (ca, cb) = coerce_ite_sorts(&mut solver, a, t_sort, b, u_sort);
        // Both sides should now have the same sort
        let ca_sort = solver.get_sort(ca);
        let cb_sort = solver.get_sort(cb);
        assert_eq!(
            ca_sort, cb_sort,
            "two different TypeParam sorts should coerce to the same sort"
        );
    }

    // --- Seq(X) vs Seq(Y) tests ---

    #[test]
    #[timeout(5000)]
    fn test_select_target_seq_int_vs_seq_bool_prefers_seq_int() {
        let seq_int = Sort::seq(Sort::Int);
        let seq_bool = Sort::seq(Sort::Bool);
        let target = select_structural_sort_target(&seq_int, &seq_bool);
        assert_eq!(
            target,
            Some(seq_int),
            "Seq(Int) should be preferred over Seq(Bool) as canonical element sort"
        );
    }

    #[test]
    #[timeout(5000)]
    fn test_select_target_seq_bool_vs_seq_int_prefers_seq_int() {
        let seq_int = Sort::seq(Sort::Int);
        let seq_bool = Sort::seq(Sort::Bool);
        let target = select_structural_sort_target(&seq_bool, &seq_int);
        assert_eq!(
            target,
            Some(seq_int),
            "Seq(Int) should be preferred regardless of argument order"
        );
    }

    #[test]
    #[timeout(5000)]
    fn test_select_target_seq_bool_vs_seq_real_picks_one() {
        let seq_bool = Sort::seq(Sort::Bool);
        let seq_real = Sort::seq(Sort::Real);
        let target = select_structural_sort_target(&seq_bool, &seq_real);
        assert!(
            target.is_some(),
            "two Seq sorts with non-Int elements should still resolve"
        );
    }

    // --- same_structural_family for Seq element sort mismatch ---

    #[test]
    #[timeout(5000)]
    fn test_same_family_seq_int_vs_seq_bool() {
        // Different Seq element sorts are still both Seq; structural_sort_family_name
        // returns "Seq" for both. But same_structural_family checks a != b first.
        let seq_int = Sort::seq(Sort::Int);
        let seq_bool = Sort::seq(Sort::Bool);
        // They are different sorts in the same Seq family.
        let family = same_structural_family(&seq_int, &seq_bool);
        assert_eq!(
            family,
            Some("Seq".to_string()),
            "Seq(Int) and Seq(Bool) are in the same Seq family"
        );
    }
}
