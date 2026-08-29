// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Completed predicate delegation through iterator adapter chains. (#2688)
//!
//! For iterator adapter types (Map, Filter, FilterMap, MapInv, etc.), the
//! `completed()` predicate should propagate through the adapter chain to
//! the inner iterator. When `completed(adapter)` holds, `completed(inner)`
//! must also hold -- the adapter can only be exhausted if its source is.
//!
//! Without this delegation, the solver treats `completed` on different
//! adapter layers as independent uninterpreted functions. This means the
//! solver cannot derive that a completed `Map<IntoIter<T>, F>` implies a
//! completed `IntoIter<T>`, even though this is semantically always true.
//!
//! The axiom asserted here is a ground-level implication:
//!
//! ```text
//! completed(adapter_term) ==> completed(iter(adapter_term))
//! ```
//!
//! where `iter(adapter_term)` is the UF application that extracts the
//! inner iterator from the adapter. This is a sound simplification:
//! every std iterator adapter's `completed()` is equivalent to its inner
//! iterator's `completed()` (for Map, Filter, FilterMap, Take, Skip, etc.).
//!
//! # Sort detection
//!
//! Adapter types are detected by matching the PureExpr receiver's sort
//! name against known iterator adapter paths (e.g., `core::iter::Map`,
//! `std::iter::Filter`, etc.). The inner iterator extraction is modeled
//! as a method call `receiver.iter()`, which resolves to the adapter's
//! `iter()` accessor UF.

use std::sync::Arc;

use trust_wp_core::formula::{ExprSort, PureExpr};

use super::super::{sort_context::DerivedKind, AYEncoder};
use crate::error::EncodingError;

/// Sort name fragments that identify iterator adapter types for completed
/// delegation. These are checked against the fully-qualified Rust type path
/// stored in `ExprSort::Datatype` annotations.
///
/// The delegation fires for any adapter type whose `completed()` semantics
/// are equivalent to the inner iterator's `completed()`. This includes all
/// standard library iterator adapters that wrap a single inner iterator.
/// Uses a three-tier matching strategy:
///
/// 1. **Module-qualified short paths** (e.g., `iter::Map`): These match short
///    paths such as `core::iter::Map` and `std::iter::Map`.
///
/// 2. **Submodule-qualified full paths** (e.g., `adapters::map::Map`): These
///    match rustc paths with intermediate adapter submodules such as
///    `core::iter::adapters::map::Map`.
///
/// 3. **Bare type names** (e.g., `::FilterMap`, `::Peekable`, `MapInv`): A
///    last-resort fallback for adapter types with sufficiently unique names.
const ADAPTER_COMPLETED_SORT_FRAGMENTS: &[&str] = &[
    // Module-qualified: catches core::iter::X, std::iter::X patterns
    "iter::Map",
    "iter::Filter",
    "iter::Enumerate",
    "iter::Skip",
    "iter::Take",
    "iter::Zip",
    "iter::Chain",
    "iter::Fuse",
    "iter::Cloned",
    "iter::Copied",
    "iter::Rev",
    "iter::FilterMap",
    "iter::Peekable",
    "adapters::map::Map",
    "adapters::filter::Filter",
    "adapters::enumerate::Enumerate",
    "adapters::skip::Skip",
    "adapters::take::Take",
    "adapters::zip::Zip",
    "adapters::chain::Chain",
    "adapters::fuse::Fuse",
    "adapters::cloned::Cloned",
    "adapters::copied::Copied",
    "adapters::rev::Rev",
    "adapters::filter_map::FilterMap",
    "adapters::peekable::Peekable",
    // Bare type names for full rustc internal paths
    // (e.g., core::iter::adapters::filter_map::FilterMap)
    "::FilterMap",
    "::Peekable",
    // trust-wp/Creusot-specific adapter
    "MapInv",
];

/// Check whether a PureExpr receiver is a known iterator adapter type by
/// examining its sort annotation.
///
/// Walks through Old, Deref, Final, and View wrappers to find the root
/// Var with a Datatype sort, then checks against known adapter sort name
/// fragments.
#[cfg(test)]
fn is_iterator_adapter_receiver(expr: &PureExpr) -> bool {
    adapter_sort_name(expr).is_some()
}

fn root_datatype_sort_name(expr: &PureExpr) -> Option<String> {
    match expr {
        PureExpr::Var(_, Some(ExprSort::Datatype(id))) => {
            Some(trust_wp_core::formula::resolve_sort_name(*id))
        }
        PureExpr::Old(inner)
        | PureExpr::Deref(inner)
        | PureExpr::Final(inner)
        | PureExpr::View(inner) => root_datatype_sort_name(inner),
        _ => None,
    }
}

fn adapter_sort_name(expr: &PureExpr) -> Option<String> {
    let sort_name = root_datatype_sort_name(expr)?;
    ADAPTER_COMPLETED_SORT_FRAGMENTS
        .iter()
        .any(|frag| sort_name.contains(frag))
        .then_some(sort_name)
}

/// Sort name fragments identifying `Zip<A, B>` adapter types.
/// Zip wraps two iterators accessed via `itera()` and `iterb()`.
const ZIP_SORT_FRAGMENTS: &[&str] = &["iter::Zip", "adapters::zip::Zip"];

/// Sort name fragments identifying `Chain<A, B>` adapter types.
/// Chain wraps two iterators accessed via `a()` and `b()`.
const CHAIN_SORT_FRAGMENTS: &[&str] = &["iter::Chain", "adapters::chain::Chain"];

/// Determine the inner iterator accessor method names for an adapter type.
///
/// Most adapters use a single `.iter()` accessor. Two exceptions:
/// - **Zip**: wraps two iterators via `.itera()` and `.iterb()`
/// - **Chain**: wraps two iterators via `.a()` and `.b()`
///
/// Returns the list of accessor method names to delegate `completed()` through.
fn inner_iterator_accessors(sort_name: &str) -> &'static [&'static str] {
    if ZIP_SORT_FRAGMENTS.iter().any(|f| sort_name.contains(f)) {
        &["itera", "iterb"]
    } else if CHAIN_SORT_FRAGMENTS.iter().any(|f| sort_name.contains(f)) {
        &["a", "b"]
    } else {
        &["iter"]
    }
}

impl AYEncoder {
    /// Assert completed delegation for iterator adapter types. (#2688)
    ///
    /// When `completed(adapter_term)` is observed for an adapter-typed receiver,
    /// asserts ground implications that propagate exhaustion to the inner
    /// iterator(s):
    ///
    /// For single-inner adapters (Map, Filter, Enumerate, etc.):
    /// ```text
    /// completed(adapter) ==> completed(adapter.iter())
    /// ```
    ///
    /// For Zip (dual-inner):
    /// ```text
    /// completed(zip) ==> completed(zip.itera())
    /// completed(zip) ==> completed(zip.iterb())
    /// ```
    ///
    /// For Chain (dual-inner):
    /// ```text
    /// completed(chain) ==> completed(chain.a())
    /// completed(chain) ==> completed(chain.b())
    /// ```
    ///
    /// This propagates the exhaustion predicate through the adapter chain to the
    /// inner iterator(s). Without this, the solver treats `completed` on the outer
    /// adapter and the inner iterator(s) as independent, preventing it from
    /// leveraging inner-iterator properties (e.g., Seq view length = 0 when
    /// completed) to reason about the adapter's state.
    ///
    /// Fires only at ground level (quantifier_depth == 0) to avoid re-asserting
    /// the delegation inside quantifier bodies where bound variables would produce
    /// non-ground instances.
    pub(crate) fn assert_adapter_completed_delegation(
        &mut self,
        receiver: &PureExpr,
        completed_term: ay_dpll::api::Term,
        prefix: Option<DerivedKind>,
    ) -> Result<(), EncodingError> {
        if self.quantifier_state.quantifier_depth() > 0 || adapter_sort_name(receiver).is_none() {
            return Ok(());
        }
        let Some(sort_name) = adapter_sort_name(receiver) else {
            return Ok(());
        };

        let dedup_key = format!("adapter_completed_delegation::{completed_term:?}");
        if !self.mark_logic_fn_axiom_asserted(dedup_key) {
            return Ok(());
        }

        let accessors = inner_iterator_accessors(&sort_name);
        for accessor in accessors {
            // Build the inner iterator extraction: adapter.<accessor>()
            let inner_iter_expr = PureExpr::MethodCall {
                receiver: Arc::new(receiver.clone()),
                method: (*accessor).to_string(),
                args: vec![],
            };

            // Build completed(adapter.<accessor>()) as a PureExpr
            let inner_completed_expr = PureExpr::MethodCall {
                receiver: Arc::new(inner_iter_expr),
                method: "completed".to_string(),
                args: vec![],
            };

            // Encode the inner completed predicate. If this fails (e.g., sort
            // mismatch because the inner iterator sort is not known), we silently
            // skip this accessor -- the quantified axioms still provide coverage.
            let inner_completed_term = match self.encode_pure_impl(&inner_completed_expr, prefix) {
                Ok(term) => term,
                Err(_) => continue, // Graceful degradation
            };

            // Assert: completed(adapter) ==> completed(adapter.<accessor>())
            let implication = self.solver.implies(completed_term, inner_completed_term);
            self.assert_solver_term("adapter_completed_delegation", implication);
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use ntest::timeout;
    use trust_wp_core::formula::{intern_sort_name, ExprSort, PureExpr};

    use super::*;

    fn make_adapter_var(name: &str, sort_name: &str) -> PureExpr {
        let id = intern_sort_name(sort_name);
        PureExpr::Var(name.to_string(), Some(ExprSort::Datatype(id)))
    }

    // --- is_iterator_adapter_receiver ---

    #[test]
    #[timeout(10000)]
    fn test_core_iter_map_detected() {
        let v = make_adapter_var("it", "core::iter::Map");
        assert!(is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_std_iter_filter_detected() {
        let v = make_adapter_var("it", "std::iter::Filter");
        assert!(is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_core_iter_filter_map_detected() {
        let v = make_adapter_var("it", "core::iter::adapters::filter_map::FilterMap");
        assert!(is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_trust_wp_map_inv_detected() {
        let v = make_adapter_var("it", "trust_wp_std::std::iter::MapInv");
        assert!(is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_creusot_map_inv_detected() {
        let v = make_adapter_var("it", "creusot_std::MapInv");
        assert!(is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_core_iter_enumerate_detected() {
        let v = make_adapter_var("it", "core::iter::Enumerate");
        assert!(is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_core_iter_skip_detected() {
        let v = make_adapter_var("it", "core::iter::Skip");
        assert!(is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_core_iter_take_detected() {
        let v = make_adapter_var("it", "core::iter::Take");
        assert!(is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_core_iter_zip_detected() {
        let v = make_adapter_var("it", "core::iter::Zip");
        assert!(is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_core_iter_chain_detected() {
        let v = make_adapter_var("it", "core::iter::Chain");
        assert!(is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_core_iter_fuse_detected() {
        let v = make_adapter_var("it", "core::iter::Fuse");
        assert!(is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_core_iter_cloned_detected() {
        let v = make_adapter_var("it", "core::iter::Cloned");
        assert!(is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_core_iter_copied_detected() {
        let v = make_adapter_var("it", "core::iter::Copied");
        assert!(is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_core_iter_rev_detected() {
        let v = make_adapter_var("it", "core::iter::Rev");
        assert!(is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_into_iter_not_detected() {
        let v = make_adapter_var("it", "std::vec::IntoIter");
        assert!(!is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_slice_iter_not_detected() {
        let v = make_adapter_var("it", "core::slice::Iter");
        assert!(!is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_iter_mut_not_detected() {
        let v = make_adapter_var("it", "core::slice::IterMut");
        assert!(!is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_fmap_iter_not_detected() {
        let v = make_adapter_var("it", "trust_wp_std::logic::fmap::FMapIter");
        assert!(!is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_view_wrapped_adapter_detected() {
        let inner = make_adapter_var("it", "core::iter::Map");
        let view = PureExpr::View(Arc::new(inner));
        assert!(is_iterator_adapter_receiver(&view));
    }

    #[test]
    #[timeout(10000)]
    fn test_old_wrapped_adapter_detected() {
        let inner = make_adapter_var("it", "std::iter::Filter");
        let old = PureExpr::Old(Arc::new(inner));
        assert!(is_iterator_adapter_receiver(&old));
    }

    #[test]
    #[timeout(10000)]
    fn test_core_iter_peekable_detected() {
        let v = make_adapter_var("it", "core::iter::Peekable");
        assert!(is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_core_iter_adapters_peekable_detected() {
        let v = make_adapter_var("it", "core::iter::adapters::peekable::Peekable");
        assert!(is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_full_path_map_detected() {
        let v = make_adapter_var("it", "core::iter::adapters::map::Map");
        assert!(is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_full_path_filter_detected() {
        let v = make_adapter_var("it", "core::iter::adapters::filter::Filter");
        assert!(is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_full_path_enumerate_detected() {
        let v = make_adapter_var("it", "core::iter::adapters::enumerate::Enumerate");
        assert!(is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_full_path_skip_detected() {
        let v = make_adapter_var("it", "core::iter::adapters::skip::Skip");
        assert!(is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_full_path_take_detected() {
        let v = make_adapter_var("it", "core::iter::adapters::take::Take");
        assert!(is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_full_path_zip_detected() {
        let v = make_adapter_var("it", "core::iter::adapters::zip::Zip");
        assert!(is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_full_path_chain_detected() {
        let v = make_adapter_var("it", "core::iter::adapters::chain::Chain");
        assert!(is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_full_path_fuse_detected() {
        let v = make_adapter_var("it", "core::iter::adapters::fuse::Fuse");
        assert!(is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_full_path_cloned_detected() {
        let v = make_adapter_var("it", "core::iter::adapters::cloned::Cloned");
        assert!(is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_full_path_copied_detected() {
        let v = make_adapter_var("it", "core::iter::adapters::copied::Copied");
        assert!(is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_full_path_rev_detected() {
        let v = make_adapter_var("it", "core::iter::adapters::rev::Rev");
        assert!(is_iterator_adapter_receiver(&v));
    }

    #[test]
    #[timeout(10000)]
    fn test_non_var_not_detected() {
        // Integer literal is not an adapter
        let expr = PureExpr::Int(42);
        assert!(!is_iterator_adapter_receiver(&expr));
    }

    // --- inner_iterator_accessors ---

    #[test]
    #[timeout(10000)]
    fn test_inner_accessors_map_uses_iter() {
        assert_eq!(inner_iterator_accessors("core::iter::Map"), &["iter"]);
    }

    #[test]
    #[timeout(10000)]
    fn test_inner_accessors_filter_uses_iter() {
        assert_eq!(inner_iterator_accessors("std::iter::Filter"), &["iter"]);
    }

    #[test]
    #[timeout(10000)]
    fn test_inner_accessors_enumerate_uses_iter() {
        assert_eq!(inner_iterator_accessors("core::iter::Enumerate"), &["iter"]);
    }

    #[test]
    #[timeout(10000)]
    fn test_inner_accessors_zip_uses_itera_iterb() {
        assert_eq!(
            inner_iterator_accessors("core::iter::Zip"),
            &["itera", "iterb"]
        );
    }

    #[test]
    #[timeout(10000)]
    fn test_inner_accessors_std_zip_uses_itera_iterb() {
        assert_eq!(
            inner_iterator_accessors("std::iter::Zip"),
            &["itera", "iterb"]
        );
    }

    #[test]
    #[timeout(10000)]
    fn test_inner_accessors_full_path_zip_uses_itera_iterb() {
        assert_eq!(
            inner_iterator_accessors("core::iter::adapters::zip::Zip"),
            &["itera", "iterb"]
        );
    }

    #[test]
    #[timeout(10000)]
    fn test_inner_accessors_chain_uses_a_b() {
        assert_eq!(inner_iterator_accessors("core::iter::Chain"), &["a", "b"]);
    }

    #[test]
    #[timeout(10000)]
    fn test_inner_accessors_std_chain_uses_a_b() {
        assert_eq!(inner_iterator_accessors("std::iter::Chain"), &["a", "b"]);
    }

    #[test]
    #[timeout(10000)]
    fn test_inner_accessors_full_path_chain_uses_a_b() {
        assert_eq!(
            inner_iterator_accessors("core::iter::adapters::chain::Chain"),
            &["a", "b"]
        );
    }

    #[test]
    #[timeout(10000)]
    fn test_inner_accessors_peekable_uses_iter() {
        assert_eq!(inner_iterator_accessors("core::iter::Peekable"), &["iter"]);
    }

    #[test]
    #[timeout(10000)]
    fn test_inner_accessors_fuse_uses_iter() {
        assert_eq!(inner_iterator_accessors("core::iter::Fuse"), &["iter"]);
    }

    #[test]
    #[timeout(10000)]
    fn test_inner_accessors_rev_uses_iter() {
        assert_eq!(inner_iterator_accessors("core::iter::Rev"), &["iter"]);
    }

    #[test]
    #[timeout(10000)]
    fn test_inner_accessors_unknown_defaults_to_iter() {
        assert_eq!(inner_iterator_accessors("some::unknown::Type"), &["iter"]);
    }
}
