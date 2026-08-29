// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! FSet, FMap, and Mapping collection method encoding.
//!
//! Encodes `FSet`, `FMap`, and `Mapping` method calls as uninterpreted functions
//! constrained by postcondition axioms from std specs.

use ay_dpll::api::{Sort, Term};
use tracing::debug;
use trust_wp_core::formula::PureExpr;

use super::AYEncoder;
use crate::{
    encoder::sort_context::{
        resolve_nameable_expr, resolve_view_var_name,
        sort_inference::{fmap_sort, mapping_sort},
    },
    error::EncodingError,
};

impl AYEncoder {
    fn fmap_value_sort_for_receiver(
        &self,
        receiver: &PureExpr,
        receiver_term: Term,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Option<Sort> {
        if let Some(sort) = self.encoding_cache.fmap_value_sort(receiver_term) {
            return Some(sort);
        }
        if let Some(name) = resolve_view_var_name(receiver, prefix) {
            if let Some(sort) = self.encoding_cache.fmap_value_sort_name(&name) {
                return Some(sort);
            }
        }
        if let Some(name) = resolve_nameable_expr(receiver, prefix) {
            if let Some(sort) = self.encoding_cache.fmap_value_sort_name(&name) {
                return Some(sort);
            }
        }
        None
    }

    fn encode_fmap_key_expr(
        &mut self,
        key: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        if let Some(alias) = self.fmap_view_deref_key_alias(key, prefix) {
            debug!("[DEBUG-FMAP] key alias {:?} => {:?}", key, alias);
            return self.encode_pure_impl(&alias, prefix);
        }
        self.encode_pure_impl(key, prefix)
    }

    fn fmap_view_deref_key_alias(
        &self,
        key: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Option<PureExpr> {
        let PureExpr::View(inner) = key else {
            return None;
        };
        if !matches!(inner.as_ref(), PureExpr::Deref(_)) {
            return None;
        }
        let alias_name = resolve_nameable_expr(inner, prefix)?;
        self.var_expr_alias(&alias_name).cloned()
    }

    /// Encode an `FSet` method call.
    ///
    /// `FSet` methods are encoded as uninterpreted functions:
    /// - `contains(elem)` → `fset_contains(receiver, elem)` (Bool)
    /// - `is_empty()` → `fset_is_empty(receiver)` (Bool)
    /// - `len()` → `fset_len(receiver)` (Int) (#2209)
    /// - `peek()` → `fset_peek(receiver)` (Int)
    /// - `remove(elem)` → `fset_remove(receiver, elem)` (Int)
    /// - `intersection(other)` → `fset_intersection(receiver, other)` (Int)
    /// - `difference(other)` → `fset_difference(receiver, other)` (Int)
    pub(in crate::encoder) fn encode_fset_method(
        &mut self,
        receiver: &PureExpr,
        method: &str,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        let receiver_term = self.encode_pure_impl(receiver, prefix)?;

        // FSet values are Sort::Int in the UF encoding. When the actual
        // receiver term has a non-Int sort (e.g., Uninterpreted("Tokens")),
        // this is a custom type that was mis-routed to FSet. Redirect to the
        // generic Bool/Int UF paths that handle arbitrary sorts. (#2316)
        //
        // This mirrors the pattern in encode_fmap_method which checks
        // `receiver_actual_sort != fmap` and falls back.
        let receiver_actual_sort = self.solver.get_sort(receiver_term);
        if receiver_actual_sort != Sort::Int {
            return match method {
                "contains" | "is_empty" => {
                    self.encode_bool_method_predicate(receiver, method, args, prefix)
                }
                _ => self.encode_int_method_uf(receiver, method, args, prefix),
            };
        }

        match method {
            "contains" => {
                let elem_term = self.encode_pure_impl(&args[0], prefix)?;
                if self.solver.get_sort(elem_term) != Sort::Int {
                    return self.encode_bool_method_predicate(receiver, method, args, prefix);
                }
                let func = self.get_or_declare_spec_fn(
                    "fset_contains",
                    &[Sort::Int, Sort::Int],
                    Sort::Bool,
                );
                let result =
                    self.safe_apply("fset_contains", &func, &[receiver_term, elem_term])?;
                // Register ground application for standard axiom instantiation (#2288).
                self.register_standard_ground_application(
                    "fset_contains",
                    result,
                    vec![receiver_term, elem_term],
                );
                Ok(result)
            }
            // is_empty(): Bool predicate — FSet has no size, just emptiness (#939)
            "is_empty" => {
                let func = self.get_or_declare_spec_fn("fset_is_empty", &[Sort::Int], Sort::Bool);
                let result = self.safe_apply("fset_is_empty", &func, &[receiver_term])?;
                self.register_standard_ground_application(
                    "fset_is_empty",
                    result,
                    vec![receiver_term],
                );
                Ok(result)
            }
            // len(): cardinality of the set (Int). Previously, FSet `len()`
            // was routed to `encode_fmap_method` which created a disconnected
            // generic UF `method_len_1_i`. The dedicated `fset_len` UF links
            // to insert/remove axioms for cardinality reasoning. Part of #2209.
            "len" => {
                let func = self.get_or_declare_spec_fn("fset_len", &[Sort::Int], Sort::Int);
                let result = self.safe_apply("fset_len", &func, &[receiver_term])?;
                self.register_standard_ground_application("fset_len", result, vec![receiver_term]);
                Ok(result)
            }
            // peek(): returns an arbitrary element from the set (Int) (#939)
            "peek" => {
                let func = self.get_or_declare_spec_fn("fset_peek", &[Sort::Int], Sort::Int);
                let result = self.safe_apply("fset_peek", &func, &[receiver_term])?;
                self.register_standard_ground_application("fset_peek", result, vec![receiver_term]);
                Ok(result)
            }
            // insert(elem): returns a new FSet with the element added (Int).
            // Ghost variant `insert_ghost` is stripped to `insert` by the
            // method_call dispatcher before reaching here. Part of #1581.
            "insert" if args.len() == 1 => {
                let elem_term = self.encode_pure_impl(&args[0], prefix)?;
                let func =
                    self.get_or_declare_spec_fn("fset_insert", &[Sort::Int, Sort::Int], Sort::Int);
                let result = self.safe_apply("fset_insert", &func, &[receiver_term, elem_term])?;
                self.register_standard_ground_application(
                    "fset_insert",
                    result,
                    vec![receiver_term, elem_term],
                );
                Ok(result)
            }
            // remove(elem): returns a new FSet without the element (Int) (#939)
            "remove" if args.len() == 1 => {
                let elem_term = self.encode_pure_impl(&args[0], prefix)?;
                let func =
                    self.get_or_declare_spec_fn("fset_remove", &[Sort::Int, Sort::Int], Sort::Int);
                let result = self.safe_apply("fset_remove", &func, &[receiver_term, elem_term])?;
                self.register_standard_ground_application(
                    "fset_remove",
                    result,
                    vec![receiver_term, elem_term],
                );
                Ok(result)
            }
            // intersection(other): returns a new FSet containing shared elements (Int) (#1124)
            "intersection" if args.len() == 1 => {
                let other_term = self.encode_pure_impl(&args[0], prefix)?;
                let func = self.get_or_declare_spec_fn(
                    "fset_intersection",
                    &[Sort::Int, Sort::Int],
                    Sort::Int,
                );
                let result =
                    self.safe_apply("fset_intersection", &func, &[receiver_term, other_term])?;
                self.register_standard_ground_application(
                    "fset_intersection",
                    result,
                    vec![receiver_term, other_term],
                );
                Ok(result)
            }
            // difference(other): returns a new FSet without other's elements (Int) (#1124)
            "difference" if args.len() == 1 => {
                let other_term = self.encode_pure_impl(&args[0], prefix)?;
                let func = self.get_or_declare_spec_fn(
                    "fset_difference",
                    &[Sort::Int, Sort::Int],
                    Sort::Int,
                );
                let result =
                    self.safe_apply("fset_difference", &func, &[receiver_term, other_term])?;
                self.register_standard_ground_application(
                    "fset_difference",
                    result,
                    vec![receiver_term, other_term],
                );
                Ok(result)
            }
            // Defensive: callers dispatch only known FSet methods here.
            _ => Err(EncodingError::unsupported(format!(
                "unknown FSet method: {method}"
            ))),
        }
    }

    /// Encode FMap method calls as uninterpreted functions.
    ///
    /// FMap operations are encoded as UFs constrained by postcondition axioms
    /// from the std specs. The postconditions (e.g., `result.contains(arg1)` for
    /// insert) become SMT assumptions linking these functions together.
    ///
    /// Methods:
    /// - `contains(key) -> Bool`: membership test
    /// - `lookup(key) -> Int`: value retrieval
    /// - `index_logic(key) -> Int`: alias for lookup (parser lowers `map[k]`)
    /// - `len() -> Int`: number of entries
    /// - `insert(key, value) -> Int`: returns new map with entry added
    /// - `merge(other, resolver) -> Int`: returns new map combining entries (#1778)
    #[allow(clippy::too_many_lines)]
    pub(in crate::encoder) fn encode_fmap_method(
        &mut self,
        receiver: &PureExpr,
        method: &str,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        let fmap = fmap_sort();
        let receiver_term = self.encode_pure_impl(receiver, prefix)?;
        let receiver_actual_sort = self.solver.get_sort(receiver_term);

        match method {
            "contains" => {
                let key_term = self.encode_fmap_key_expr(&args[0], prefix)?;
                let key_actual_sort = self.solver.get_sort(key_term);
                if receiver_actual_sort != fmap {
                    return self.encode_bool_method_predicate(receiver, method, args, prefix);
                }
                let func = self.get_or_declare_spec_fn(
                    "fmap_contains",
                    &[fmap.clone(), key_actual_sort],
                    Sort::Bool,
                );
                let result = self.safe_apply("fmap_contains", &func, &[receiver_term, key_term])?;
                // Register ground application for standard axiom instantiation (#2288).
                self.register_standard_ground_application(
                    "fmap_contains",
                    result,
                    vec![receiver_term, key_term],
                );
                Ok(result)
            }
            "lookup" | "index_logic" | "index" | "get" => {
                let key_term = self.encode_fmap_key_expr(&args[0], prefix)?;
                let key_actual_sort = self.solver.get_sort(key_term);
                if receiver_actual_sort != fmap {
                    return self.encode_int_method_uf(receiver, method, args, prefix);
                }
                let value_sort = self
                    .fmap_value_sort_for_receiver(receiver, receiver_term, prefix)
                    .unwrap_or(Sort::Int);
                let func = self.get_or_declare_spec_fn(
                    "fmap_lookup",
                    &[fmap.clone(), key_actual_sort],
                    value_sort,
                );
                let result = self.safe_apply("fmap_lookup", &func, &[receiver_term, key_term])?;
                // Register ground application for standard axiom instantiation (#2288).
                self.register_standard_ground_application(
                    "fmap_lookup",
                    result,
                    vec![receiver_term, key_term],
                );

                debug!(
                    "[DEBUG-FMAP] {method}({receiver:?}, {:?}) => fmap_lookup => {result:?}",
                    &args[0]
                );

                Ok(result)
            }
            "len" => {
                if receiver_actual_sort != fmap {
                    return self.encode_int_method_uf(receiver, method, args, prefix);
                }
                let result = self.fmap_len_term(receiver_term);
                self.register_standard_ground_application("fmap_len", result, vec![receiver_term]);
                Ok(result)
            }
            "into_seq" if args.is_empty() => {
                if receiver_actual_sort != fmap {
                    return Err(EncodingError::unsupported(format!(
                        "into_seq requires an FMap receiver, got {receiver_actual_sort:?}"
                    )));
                }
                let seq_sort = self.get_seq_sort();
                let func = self.get_or_declare_spec_fn(
                    "fmap_into_seq",
                    std::slice::from_ref(&fmap),
                    seq_sort,
                );
                let result = self.safe_apply("fmap_into_seq", &func, &[receiver_term])?;
                self.register_standard_ground_application(
                    "fmap_into_seq",
                    result,
                    vec![receiver_term],
                );
                Ok(result)
            }
            "insert" if args.len() == 2 => {
                let key_term = self.encode_fmap_key_expr(&args[0], prefix)?;
                let val_term = self.encode_pure_impl(&args[1], prefix)?;
                let key_actual_sort = self.solver.get_sort(key_term);
                let value_actual_sort = self.solver.get_sort(val_term);
                if receiver_actual_sort != fmap {
                    return self.encode_int_method_uf(receiver, method, args, prefix);
                }
                let func = self.get_or_declare_spec_fn(
                    "fmap_insert",
                    &[fmap.clone(), key_actual_sort, value_actual_sort.clone()],
                    fmap.clone(),
                );
                let result =
                    self.safe_apply("fmap_insert", &func, &[receiver_term, key_term, val_term])?;
                self.encoding_cache
                    .insert_fmap_value_sort(result, value_actual_sort);
                self.register_standard_ground_application(
                    "fmap_insert",
                    result,
                    vec![receiver_term, key_term, val_term],
                );
                Ok(result)
            }
            // merge(other_map, resolver): returns a new FMap combining two maps (#1778).
            // The resolver closure selects which value to keep on key collision.
            // Currently supports left-bias resolver `|(v1, _)| v1` used by Creusot
            // ghost tests. The resolver argument is encoded but not interpreted —
            // merge semantics are enforced via axioms on `fmap_merge`.
            "merge" if args.len() == 2 => {
                let other_term = self.encode_pure_impl(&args[0], prefix)?;
                let other_actual_sort = self.solver.get_sort(other_term);
                if receiver_actual_sort != fmap || other_actual_sort != fmap {
                    return self.encode_int_method_uf(receiver, method, args, prefix);
                }
                let func =
                    self.get_or_declare_spec_fn("fmap_merge", &[fmap.clone(), fmap.clone()], fmap);
                let result = self.safe_apply("fmap_merge", &func, &[receiver_term, other_term])?;
                self.register_standard_ground_application(
                    "fmap_merge",
                    result,
                    vec![receiver_term, other_term],
                );
                Ok(result)
            }
            _ => Err(EncodingError::unsupported(format!(
                "unknown FMap method: {method}"
            ))),
        }
    }

    /// Encode a `Mapping` (total function) method call. (#2317)
    ///
    /// `Mapping` is a total function: every key has a value. Unlike `FMap`,
    /// there is no `contains`/`len` concept. Operations:
    /// - `get(key)` / `index(key)` / `index_logic(key)` → `mapping_get(m, k)` (Int)
    /// - `set(key, value)` → `mapping_set(m, k, v)` (Mapping)
    ///
    /// UFs are separate from FMap to preserve total-map semantics.
    pub(in crate::encoder) fn encode_mapping_method(
        &mut self,
        receiver: &PureExpr,
        method: &str,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        let mapping = mapping_sort();
        let receiver_term = self.encode_pure_impl(receiver, prefix)?;
        let receiver_actual_sort = self.solver.get_sort(receiver_term);

        match method {
            "get" | "index_logic" | "index" => {
                let key_term = self.encode_pure_impl(&args[0], prefix)?;
                let key_actual_sort = self.solver.get_sort(key_term);
                if key_actual_sort != Sort::Int {
                    return self.encode_int_method_uf(receiver, method, args, prefix);
                }
                // Coerce receiver to Mapping sort when AST-level dispatch
                // classified this as a Mapping call but the encoded term has
                // a different sort (e.g., Int from Seq Select). Prefer
                // `try_restore_seq_element_from_int` which reuses the same
                // restore UF as the equality encoding in `encode_binop_expr`,
                // ensuring congruence: the equality `view_elem == seq_elem`
                // produces the same restored Mapping term that we use here
                // for `mapping_get`. Fallback to `coerce_to_mapping` bridge
                // UF for non-Seq-sourced Int terms. (#2316)
                let receiver_term = if receiver_actual_sort == mapping {
                    receiver_term
                } else {
                    self.try_restore_seq_element_from_int(receiver_term, &mapping)
                        .unwrap_or_else(|| self.coerce_to_mapping(receiver_term))
                };
                let func = self.get_or_declare_spec_fn(
                    "mapping_get",
                    &[mapping.clone(), Sort::Int],
                    Sort::Int,
                );
                let result = self.safe_apply("mapping_get", &func, &[receiver_term, key_term])?;
                self.register_standard_ground_application(
                    "mapping_get",
                    result,
                    vec![receiver_term, key_term],
                );

                debug!(
                    "[DEBUG-MAPPING] {method}({receiver:?}, {:?}) => mapping_get => {result:?}",
                    &args[0]
                );

                Ok(result)
            }
            "set" if args.len() == 2 => {
                let key_term = self.encode_pure_impl(&args[0], prefix)?;
                let val_term = self.encode_pure_impl(&args[1], prefix)?;
                let key_actual_sort = self.solver.get_sort(key_term);
                let value_actual_sort = self.solver.get_sort(val_term);
                if key_actual_sort != Sort::Int || value_actual_sort != Sort::Int {
                    return self.encode_int_method_uf(receiver, method, args, prefix);
                }
                // Coerce receiver to Mapping sort (same rationale as get). (#2316)
                let receiver_term = if receiver_actual_sort == mapping {
                    receiver_term
                } else {
                    self.try_restore_seq_element_from_int(receiver_term, &mapping)
                        .unwrap_or_else(|| self.coerce_to_mapping(receiver_term))
                };
                let func = self.get_or_declare_spec_fn(
                    "mapping_set",
                    &[mapping.clone(), Sort::Int, Sort::Int],
                    mapping.clone(),
                );
                let result =
                    self.safe_apply("mapping_set", &func, &[receiver_term, key_term, val_term])?;
                self.register_standard_ground_application(
                    "mapping_set",
                    result,
                    vec![receiver_term, key_term, val_term],
                );

                debug!(
                    "[DEBUG-MAPPING] set({receiver:?}, {:?}, {:?}) => mapping_set => {result:?}",
                    &args[0], &args[1]
                );

                Ok(result)
            }
            _ => {
                // Fall through to generic UF for unrecognized Mapping methods
                self.encode_int_method_uf(receiver, method, args, prefix)
            }
        }
    }

    /// Coerce a non-Mapping-sorted term to Mapping sort via a bridge UF. (#2316)
    ///
    /// When AST-level dispatch classifies a receiver as Mapping (via
    /// `is_mapping_receiver` / `is_seq_index_mapping_candidate`) but the
    /// encoded term has a different sort (typically Int from Seq Select),
    /// this bridge ensures the term can be passed to `mapping_get`/`mapping_set`.
    ///
    /// Used as fallback after `try_restore_seq_element_from_int` for
    /// non-Seq-sourced Int terms. The restore path is preferred because it
    /// reuses the same UF as the equality encoding in `encode_binop_expr`,
    /// preserving congruence. This bridge handles the remaining cases where
    /// no Seq source is recorded.
    ///
    /// The bridge UF `__to_mapping_<sort>: <sort> -> Mapping` preserves
    /// congruence: if `a == b` then `bridge(a) == bridge(b)`, so
    /// `mapping_get(bridge(a), k) == mapping_get(bridge(b), k)`.
    pub(in crate::encoder) fn coerce_to_mapping(&mut self, term: Term) -> Term {
        let term_sort = self.solver.get_sort(term);
        let mapping = mapping_sort();
        if term_sort == mapping {
            return term;
        }
        let sort_label = match &term_sort {
            Sort::Int => "Int".to_string(),
            Sort::Bool => "Bool".to_string(),
            Sort::Uninterpreted(name) => name.replace("::", "_"),
            Sort::Datatype(dt) => dt.name.replace("::", "_"),
            _ => format!("{term_sort:?}"),
        };
        let bridge_name = format!("__to_mapping_{sort_label}");
        let bridge_fn =
            self.get_or_declare_spec_fn(&bridge_name, std::slice::from_ref(&term_sort), mapping);
        self.safe_apply(&bridge_name, &bridge_fn, &[term])
            .unwrap_or_else(|_| self.solver.apply(&bridge_fn, &[term]))
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use ay_dpll::api::Sort;
    use ntest::timeout;
    use trust_wp_core::formula::{intern_sort_name, ExprSort, PureExpr};

    use crate::encoder::AYEncoder;

    #[test]
    #[timeout(30000)]
    fn fset_contains_int_receiver_with_non_int_arg_uses_generic_bool_uf() {
        let mut encoder = AYEncoder::new();
        let receiver = PureExpr::Var("tokens".to_string(), None);
        let arg = PureExpr::Var(
            "ns".to_string(),
            Some(ExprSort::Datatype(intern_sort_name("implementation"))),
        );

        let result = encoder
            .encode_fset_method(&receiver, "contains", &[arg], None)
            .expect("non-Int contains argument should not reach fset_contains");

        assert_eq!(
            encoder.solver.get_sort(result),
            Sort::Bool,
            "generic contains fallback must still produce Bool"
        );
        assert!(
            !encoder.decls().has_spec_func("fset_contains"),
            "non-Int contains argument must not declare fset_contains"
        );
        assert!(
            encoder
                .decls()
                .logic_func_names()
                .any(|name| name.starts_with("method_contains_2_")),
            "fallback should declare the generic Bool method predicate"
        );
    }

    #[test]
    #[timeout(30000)]
    fn fmap_key_view_deref_uses_recorded_source_alias() {
        let mut encoder = AYEncoder::new();
        let receiver = PureExpr::Var("map".to_string(), Some(ExprSort::FMap));
        let alias = PureExpr::Var(
            "cell".to_string(),
            Some(ExprSort::Datatype(intern_sort_name("PermCell"))),
        );
        let rc = PureExpr::Var(
            "rc".to_string(),
            Some(ExprSort::Datatype(intern_sort_name("Rc"))),
        );
        let key = PureExpr::View(Arc::new(PureExpr::Deref(Arc::new(rc))));

        encoder.record_var_expr_alias("rc_current", alias.clone());
        let alias_term = encoder.encode_pure(&alias).expect("encode alias");

        let _ = encoder
            .encode_fmap_method(&receiver, "get", &[key], None)
            .expect("encode FMap get");
        let entries = encoder
            .ground_pool_for_test()
            .entries_for("fmap_lookup")
            .expect("fmap lookup ground application");

        assert_eq!(entries.len(), 1);
        assert_eq!(
            entries[0].arg_terms[1], alias_term,
            "FMap keys should use the recorded source alias for View(Deref(...))"
        );
    }
}
