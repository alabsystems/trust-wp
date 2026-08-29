// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Method call encoding for the AY encoder.
//!
//! Dispatches `PureExpr::MethodCall` to specialized encoders based on the method
//! name and receiver type. Handles Seq operations, closure-spec predicates,
//! iterator protocol, Option/Result spec methods, and generic uninterpreted
//! functions.
//!
//! Extracted from `mod.rs` as part of #896 encoder decomposition.

mod bool_uf;
#[cfg(test)]
mod bool_uf_tests;
mod collection_dispatch;
#[cfg(test)]
mod collection_dispatch_tests;
mod discriminant;
#[cfg(test)]
mod discriminant_tests;
mod ext_eq;
#[cfg(test)]
mod ext_eq_tests;
mod int_uf;
#[cfg(test)]
mod int_uf_tests;
mod logic_dispatch;
mod permutation_axioms;
mod slice_index_spec;
#[cfg(test)]
mod slice_index_spec_tests;
mod sort_queries;
#[cfg(test)]
mod sort_queries_tests;

use std::sync::Arc;

use ay_dpll::api::{FuncDecl, Sort, Term};
use trust_wp_core::{
    formula::{BinOp, ExprSort, PureExpr},
    logic::is_invariant_method_name,
};

use super::AYEncoder;
use crate::{
    encoder::sort_context::{resolve_nameable_expr, resolve_view_var_name},
    error::EncodingError,
};

impl AYEncoder {
    fn tuple2_payload(receiver: &PureExpr) -> Option<(PureExpr, PureExpr)> {
        let PureExpr::LogicFnCall { name, args } = receiver else {
            return None;
        };
        (trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_arity(name) == Some(2)
            && args.len() == 2)
            .then(|| (args[0].clone(), args[1].clone()))
    }

    fn fmap_insert_local_update_expr(map: PureExpr, key: PureExpr, value: PureExpr) -> PureExpr {
        PureExpr::MethodCall {
            receiver: Arc::new(map),
            method: "insert".to_string(),
            args: vec![key, value],
        }
    }

    fn record_fmap_hint_for_local_update_resource(
        &mut self,
        expr: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) {
        if let Some(name) = resolve_view_var_name(expr, prefix) {
            self.record_sort_hint(name, ExprSort::FMap);
        }
        if let Some(name) = resolve_nameable_expr(expr, prefix) {
            self.record_sort_hint(name, ExprSort::FMap);
        }
    }

    fn try_encode_fmap_insert_local_update_premise(
        &mut self,
        receiver: &PureExpr,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Option<Term>, EncodingError> {
        let Some((key, _value)) = Self::tuple2_payload(receiver) else {
            return Ok(None);
        };
        let [from_auth, _from_frag] = args else {
            return Ok(None);
        };
        self.record_fmap_hint_for_local_update_resource(from_auth, prefix);
        let contains = PureExpr::MethodCall {
            receiver: Arc::new(from_auth.clone()),
            method: "contains".to_string(),
            args: vec![key],
        };
        let contains_term = self.encode_pure_impl(&contains, prefix)?;
        Ok(Some(self.solver.not(contains_term)))
    }

    fn try_encode_fmap_insert_local_update_update(
        &mut self,
        receiver: &PureExpr,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Option<Term>, EncodingError> {
        let Some((key, value)) = Self::tuple2_payload(receiver) else {
            return Ok(None);
        };
        let [from_auth, from_frag] = args else {
            return Ok(None);
        };
        self.record_fmap_hint_for_local_update_resource(from_auth, prefix);
        self.record_fmap_hint_for_local_update_resource(from_frag, prefix);
        let updated_auth =
            Self::fmap_insert_local_update_expr(from_auth.clone(), key.clone(), value.clone());
        let updated_frag = Self::fmap_insert_local_update_expr(from_frag.clone(), key, value);
        let pair = PureExpr::LogicFnCall {
            name: trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_name(2),
            args: vec![updated_auth, updated_frag],
        };
        self.encode_pure_impl(&pair, prefix).map(Some)
    }

    fn encode_method_sort_tag(raw: &str) -> String {
        let mut encoded = String::new();
        for byte in raw.as_bytes() {
            let _ = std::fmt::Write::write_fmt(&mut encoded, format_args!("{byte:02x}"));
        }
        encoded
    }

    pub(in crate::encoder) fn method_sort_tag(sort: &Sort) -> String {
        match sort {
            Sort::Bool => "b".to_string(),
            Sort::Int => "i".to_string(),
            Sort::Seq(_) => "s".to_string(),
            Sort::Uninterpreted(name) => format!("u{}", Self::encode_method_sort_tag(name)),
            Sort::Datatype(dt) => format!("d{}", Self::encode_method_sort_tag(&dt.name)),
            other => format!("x{}", Self::encode_method_sort_tag(&format!("{other:?}"))),
        }
    }

    pub(in crate::encoder) fn bool_method_symbol(method: &str, param_sorts: &[Sort]) -> String {
        let sort_signature = param_sorts
            .iter()
            .map(Self::method_sort_tag)
            .collect::<Vec<_>>()
            .join("_");
        format!("method_{method}_{}_{sort_signature}", param_sorts.len())
    }

    /// Get an existing UF declaration from `decls.logic_funcs`, or declare a
    /// new one with the given name, parameter sorts, and return sort.
    ///
    /// This consolidates the 3 "get-or-declare" patterns in
    /// `encode_bool_method_predicate`, `encode_int_method_uf`, and
    /// `encode_produces_predicate`. (#2065)
    pub(super) fn get_or_declare_method_func(
        &mut self,
        smt_name: &str,
        param_sorts: &[Sort],
        return_sort: Sort,
    ) -> FuncDecl {
        if let Some(existing) = self.logic_func_decl_cloned(smt_name) {
            if existing.domain() == param_sorts && existing.range() == &return_sort {
                existing
            } else {
                let collision_key = Self::method_collision_key(smt_name, param_sorts, &return_sort);
                self.get_or_declare_logic_func(&collision_key, param_sorts, return_sort)
            }
        } else {
            self.get_or_declare_logic_func(smt_name, param_sorts, return_sort)
        }
    }

    fn method_collision_key(smt_name: &str, param_sorts: &[Sort], return_sort: &Sort) -> String {
        let params = if param_sorts.is_empty() {
            "nullary".to_string()
        } else {
            param_sorts
                .iter()
                .map(Self::method_sort_tag)
                .collect::<Vec<_>>()
                .join("_")
        };
        let ret = Self::method_sort_tag(return_sort);
        format!("{smt_name}__sig_{params}__ret_{ret}")
    }

    /// Retry a method UF application with actual encoded term sorts when the
    /// inferred sorts don't match. Called from `bool_uf.rs` and `int_uf.rs`.
    pub(super) fn apply_method_func_with_actual_sort_retry(
        &mut self,
        context: &str,
        smt_name: &str,
        inferred_param_sorts: &[Sort],
        return_sort: Sort,
        all_terms: &[Term],
    ) -> Result<(Term, String), EncodingError> {
        let func_decl =
            self.get_or_declare_method_func(smt_name, inferred_param_sorts, return_sort.clone());
        match self.safe_apply(context, &func_decl, all_terms) {
            Ok(term) => Ok((term, func_decl.name().to_string())),
            Err(original_err) => {
                // Retry once with the actual encoded term sorts. Recovery
                // paths often preserve richer inferred sort tags even when the
                // carrier term has fallen back to Int, and reusing the
                // inferred declaration would reproduce the same mismatch.
                let actual_param_sorts: Vec<Sort> = all_terms
                    .iter()
                    .map(|term| self.solver.get_sort(*term))
                    .collect();
                if actual_param_sorts == inferred_param_sorts {
                    return Err(original_err);
                }

                let retry_decl =
                    self.get_or_declare_method_func(smt_name, &actual_param_sorts, return_sort);
                let retry_term = self.safe_apply(context, &retry_decl, all_terms)?;
                Ok((retry_term, retry_decl.name().to_string()))
            }
        }
    }

    /// Encode a method call expression with optional prefix.
    ///
    /// Dispatches to specialized encoders:
    /// - Seq-exclusive: `index_logic`, `push_back`, `tail`, `pop_front`, `pop_back`, `sum`, `concat`, `len_logic`
    /// - FMap-exclusive: `lookup`, `insert`, `insert_ghost`, `merge` (#1778)
    /// - Seq/FMap/Mapping ambiguous (dispatch via is_seq_receiver): `len`, `index`, `get`
    /// - Seq/FMap/FSet ambiguous (dispatch via is_seq_receiver + is_fmap_receiver): `contains`
    /// - Closure-spec: `precondition`, `postcondition`, etc.
    /// - Iterator: `completed` (Bool predicate)
    /// - Option/Result: `is_some`, `unwrap`, `as_ref`, `as_mut`, `unwrap_or_default`, etc.
    #[allow(clippy::too_many_lines)]
    pub(super) fn encode_method_call_impl(
        &mut self,
        receiver: &PureExpr,
        method: &str,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        match method {
            // Seq-exclusive methods: only Seq defines these, safe to route unconditionally.
            // Ghost variants (`_ghost` suffix) are specification-only aliases used
            // inside ghost! blocks — they have identical SMT semantics. Part of #1581.
            "push_back" | "push_back_ghost" | "push_front" | "push_front_ghost" | "pop_front"
            | "pop_front_ghost" | "pop_back" | "pop_back_ghost" | "tail" | "reverse" | "sum"
            | "concat" | "to_owned_seq" => {
                // Strip _ghost suffix so the Seq encoder sees the canonical name
                let canonical = method.strip_suffix("_ghost").unwrap_or(method);
                // Registered logic functions take precedence over Seq dispatch.
                // User-defined ADTs (e.g., List) may define methods with the
                // same name as Seq built-ins (e.g., List::sum). (#1965, #2002)
                if let Some(result) = self.try_logic_fn_dispatch(canonical, receiver, args, prefix)
                {
                    result
                } else {
                    self.encode_seq_operation_impl(receiver, canonical, args, prefix)
                }
            }
            // index_logic: Seq/Mapping/FMap dispatch (#967, #2317)
            "index_logic" => self.encode_index_logic_dispatch(receiver, args, prefix),
            // FMap-exclusive methods: lookup, insert, merge, into_seq are unique to FMap (#967, #1778)
            "lookup" => self.encode_fmap_method(receiver, method, args, prefix),
            // Static empty constructors written in method syntax, e.g. `Seq::empty()`.
            // The parser lowers these as `MethodCall(Var("Seq"), "empty", [])`
            // rather than `LogicFnCall("Seq::empty", [])`. Route them to the
            // same builtins so either surface syntax works. (#2640)
            "empty" if args.is_empty() => match receiver {
                PureExpr::Var(name, _) if name == "Seq" => Ok(self.encode_seq_empty()),
                PureExpr::Var(name, _) if name == "FMap" => Ok(self.solver.declare_const(
                    "fmap_empty",
                    crate::encoder::sort_context::sort_inference::fmap_sort(),
                )),
                PureExpr::Var(name, _) if name == "FSet" => {
                    Ok(self.solver.declare_const("fset_empty", Sort::Int))
                }
                _ => Err(EncodingError::unsupported(format!(
                    "unknown static empty receiver `{receiver:?}`"
                ))),
            },
            // Static singleton constructor written in method syntax, e.g.
            // `Seq::singleton(v)`. Keep it on the same axiom-backed path as
            // `seq![v]`.
            "singleton" if args.len() == 1 => match receiver {
                PureExpr::Var(name, _) if name == "Seq" => {
                    let value_term = self.encode_pure_impl(&args[0], prefix)?;
                    Ok(self.encode_seq_singleton(value_term))
                }
                _ => Err(EncodingError::unsupported(format!(
                    "unknown static singleton receiver `{receiver:?}`"
                ))),
            },
            // char::to_utf8() returns the byte sequence for a char. Keep it as
            // a Seq-valued UF so equalities to concrete seq![u8, ...] literals
            // can propagate SeqValue metadata to subsequent `.len()` calls.
            "to_utf8" if args.is_empty() => {
                let receiver_term = self.encode_pure_impl(receiver, prefix)?;
                let receiver_sort = self.solver.get_sort(receiver_term);
                let smt_name =
                    Self::bool_method_symbol(method, std::slice::from_ref(&receiver_sort));
                let func = self.get_or_declare_method_func(
                    &smt_name,
                    &[receiver_sort],
                    Sort::seq(Sort::Int),
                );
                self.safe_apply("to_utf8", &func, &[receiver_term])
            }
            "insert" | "insert_ghost" if args.len() == 2 => {
                self.encode_fmap_method(receiver, "insert", args, prefix)
            }
            // FSet insert: 1-arg variant inserts an element into a set.
            // Ghost variant `insert_ghost` is an alias. Part of #1581.
            "insert" | "insert_ghost" if args.len() == 1 => {
                self.encode_fset_method(receiver, "insert", args, prefix)
            }
            "merge" if args.len() == 2 => self.encode_fmap_method(receiver, method, args, prefix),
            "into_seq" if args.is_empty() => {
                self.encode_fmap_method(receiver, method, args, prefix)
            }
            // Ambiguous collection methods: Seq/FMap/FSet/Mapping dispatch (#756)
            "len" | "len_ghost" => self.encode_len_dispatch(receiver, args, prefix),
            "index" | "get" | "get_ghost" | "get_mut_ghost" => {
                self.encode_index_get_dispatch(receiver, method, args, prefix)
            }
            // len_logic: alias for len (Creusot compat -- user-defined on List, but
            // for Seq receivers we treat it as seq_len) (#690)
            "len_logic" => self.encode_seq_operation_impl(receiver, "len", args, prefix),
            // Type invariant predicate methods.
            // Registered logic functions take precedence (#1296): when a logic
            // function named "invariant" exists, its defining axiom and ground
            // pool registration provide the semantics. Without this check,
            // the call creates a disconnected `method_invariant_1_i` UF with
            // no axiom link, causing quantifier-unhandled failures.
            _ if args.is_empty() && is_invariant_method_name(method) => {
                if let Some(result) = self.try_logic_fn_dispatch(method, receiver, args, prefix) {
                    result
                } else {
                    self.encode_bool_method_predicate(receiver, method, args, prefix)
                }
            }
            // SliceIndexSpec predicates: concrete semantics for usize indices,
            // Bool UF fallback for range types. (#1609)
            "in_bounds" => self.encode_in_bounds(receiver, args, prefix),
            "has_value" => self.encode_has_value(receiver, args, prefix),
            "resolve_elsewhere" => self.encode_resolve_elsewhere(receiver, args, prefix),
            // Closure-spec predicate methods (uninterpreted Bool functions)
            "precondition" | "postcondition" | "postcondition_once" | "postcondition_mut" => {
                if let Some(result) =
                    self.try_inline_closure_postcondition(receiver, method, args, prefix)
                {
                    result
                } else {
                    self.encode_closure_spec_method(receiver, method, args, prefix)
                }
            }
            // Iterator protocol: completed() is a Bool predicate (#690)
            "completed" => {
                let result = self.encode_bool_method_predicate(receiver, method, args, prefix)?;
                // Assert completed-produces ground link for IterMut (#2238):
                // completed(it) ==> it@.len() == 0
                self.assert_iter_mut_completed_produces_link(receiver, result, prefix)?;
                // Assert completed delegation for iterator adapters (#2688):
                // completed(adapter) ==> completed(adapter.iter())
                self.assert_adapter_completed_delegation(receiver, result, prefix)?;
                Ok(result)
            }
            // Invariant public-state accessor: returns the protocol's `Public`
            // carrier, not a Bool predicate. Until method return sorts become
            // associated-type-aware, keep it on the value-UF lane. (#994)
            "public" if args.is_empty() => {
                self.encode_int_method_uf(receiver, "public", args, prefix)
            }
            // Option/Result spec methods (constructor testers + accessors)
            "is_some" | "is_none" | "unwrap" | "unwrap_logic" | "is_ok" | "is_err"
            | "unwrap_err" | "unwrap_or_default" => {
                self.encode_datatype_spec_method(receiver, method, prefix)
            }
            // as_ref/as_mut on Option/Result: identity in SMT (no ref/mut distinction)
            "as_ref" | "as_mut" if args.is_empty() => {
                self.encode_datatype_spec_method(receiver, method, prefix)
            }
            // FSet methods: peek(), remove(elem), intersection(other), difference(other)
            // — registered logic functions take precedence when names overlap (#1124)
            "peek" if args.is_empty() => {
                if let Some(result) = self.try_logic_fn_dispatch(method, receiver, args, prefix) {
                    result
                } else {
                    self.encode_fset_method(receiver, method, args, prefix)
                }
            }
            // Collection methods with sort-aware dispatch
            "remove" | "remove_ghost" if args.len() == 1 => {
                self.encode_remove_dispatch(receiver, args, prefix)
            }
            "intersection" | "difference" if args.len() == 1 => {
                self.encode_set_op_dispatch(receiver, method, args, prefix)
            }
            "is_empty" | "is_empty_ghost" if args.is_empty() => {
                self.encode_is_empty_dispatch(receiver, args, prefix)
            }
            "contains" | "contains_ghost" if args.len() == 1 => {
                self.encode_contains_dispatch(receiver, args, prefix)
            }
            // Seq: subsequence(from, to) — slice extraction (#737)
            "subsequence" if args.len() == 2 => {
                self.encode_seq_operation_impl(receiver, method, args, prefix)
            }
            // Seq: ext_eq(other) — pointwise equality (#737)
            "ext_eq" if args.len() == 1 => self.encode_ext_eq(receiver, &args[0], prefix),
            // Seq multiset/permutation theory (gap no-permutation-multiset-theory).
            // Registered logic functions take precedence (user ADTs may define a
            // `count` etc.), else route to the seq UF + permutation axiom module.
            "permutation_of" if args.len() == 1 => {
                if let Some(result) = self.try_logic_fn_dispatch(method, receiver, args, prefix) {
                    result
                } else {
                    self.encode_seq_operation_impl(receiver, method, args, prefix)
                }
            }
            "exchange" if args.len() == 3 => {
                if let Some(result) = self.try_logic_fn_dispatch(method, receiver, args, prefix) {
                    result
                } else {
                    self.encode_seq_operation_impl(receiver, method, args, prefix)
                }
            }
            "count" if args.len() == 1 && self.base_var_has_seq_hint(receiver, prefix) => {
                self.encode_seq_operation_impl(receiver, method, args, prefix)
            }
            // Iterator/ghost: produces(visited, o) — Bool predicate (#379)
            // The `visited` arg (args[0]) is a Seq; override sort inference which
            // would default to Int for bare variables.
            "produces" => self.encode_produces_predicate(receiver, args, prefix),
            // FMapInsertLocalUpdate is tuple-lowered by the driver. Ground its
            // local-update methods directly so Authority::update postconditions
            // reduce to the same FMap UFs as ordinary insert/contains specs.
            "premise" if args.len() == 2 => {
                if let Some(result) =
                    self.try_encode_fmap_insert_local_update_premise(receiver, args, prefix)?
                {
                    Ok(result)
                } else if let Some(result) =
                    self.try_logic_fn_dispatch(method, receiver, args, prefix)
                {
                    result
                } else {
                    self.encode_bool_method_predicate(receiver, method, args, prefix)
                }
            }
            "update" if args.len() == 2 => {
                if let Some(result) =
                    self.try_encode_fmap_insert_local_update_update(receiver, args, prefix)?
                {
                    Ok(result)
                } else if let Some(result) =
                    self.try_logic_fn_dispatch(method, receiver, args, prefix)
                {
                    result
                } else {
                    Err(EncodingError::unsupported(format!(
                        "unknown method `{method}` is not a registered logic function \
                         and has no built-in encoding — add it to the method dispatch \
                         table or register it as a #[logic] function"
                    )))
                }
            }
            // pow2: Creusot Int::pow2 builtin. Ground receivers fold to the
            // exact arithmetic term; symbolic receivers stay on the Int-UF
            // lane so spec axioms still encode. (#994)
            "pow2" if args.is_empty() => self.encode_pow2_method(receiver, prefix),
            "rem_euclid" if args.len() == 1 => {
                let lhs = self.encode_pure_impl(receiver, prefix)?;
                let rhs = self.encode_pure_impl(&args[0], prefix)?;
                self.encode_binop(lhs, BinOp::Mod, rhs, None)
            }
            // NumExt bit-count logic methods: Int-returning UFs used by
            // Creusot bitvector specs and by MIR extraction of primitive
            // integer methods such as `usize::leading_zeros`.
            "leading_zeros_logic"
            | "trailing_zeros_logic"
            | "leading_ones_logic"
            | "trailing_ones_logic"
                if args.is_empty() =>
            {
                self.encode_int_method_uf(receiver, method, args, prefix)
            }
            // deep_model: Int-returning uninterpreted function (#737)
            "deep_model" if args.is_empty() => self.encode_deep_model_uf(receiver, prefix),
            // capacity: Int-returning uninterpreted function (#737)
            "capacity" if args.is_empty() => {
                self.encode_int_method_uf(receiver, "capacity", args, prefix)
            }
            // Range iterator spec accessors: Int-returning uninterpreted
            // functions seeded by the IntoIterator contract and consumed by the
            // range `produces` rewrite. (#2171)
            "start_log" | "end_log" if args.is_empty() => {
                self.encode_int_method_uf(receiver, method, args, prefix)
            }
            // Iterator adapter accessor surface from trust-wp-std specs:
            // `iter`, `func`, `n`, `itera`, `iterb`, and `a` are opaque
            // structural projections that only exist to connect adapter specs
            // like `result.iter() == self` and `result.func() == f`.
            // Keep them on the value-UF lane so spec postconditions can encode
            // instead of failing on unknown methods. (#2689, cc/collections.rs)
            "iter" | "func" | "n" | "itera" | "iterb" | "a" if args.is_empty() => {
                self.encode_int_method_uf(receiver, method, args, prefix)
            }
            // set: Seq/Mapping/Int UF dispatch (#969, #2317)
            "set" if args.len() == 2 => self.encode_set_dispatch(receiver, args, prefix),
            // set with unexpected arity: fall back to Int UF
            "set" => self.encode_int_method_uf(receiver, "set", args, prefix),
            // namespace/id: Int-returning uninterpreted functions (#737)
            "namespace" if args.is_empty() => {
                self.encode_int_method_uf(receiver, "namespace", args, prefix)
            }
            "id" if args.is_empty() => self.encode_int_method_uf(receiver, "id", args, prefix),
            // map/filter: collection-returning methods — sort-aware dispatch (#885)
            // FSet.map(f) and FSet.filter(f) return new FSets (Int), not Bool.
            // Previously encoded as Bool predicates (#737), causing sort mismatch
            // panics when the result was passed to FSet methods like contains().
            "map" | "filter" => self.encode_int_method_uf(receiver, method, args, prefix),
            // addr_logic: Int-returning UF for pointer address (#737)
            "addr_logic" if args.is_empty() => {
                self.encode_int_method_uf(receiver, "addr_logic", args, prefix)
            }
            // discriminant: Int-returning UF for enum discriminant value (#947).
            // Generated by `Rvalue::Discriminant` in MIR for match/if-let on enums.
            // The discriminant is an integer used by SwitchInt to select branches.
            "discriminant" if args.is_empty() => {
                self.encode_int_method_uf(receiver, "discriminant", args, prefix)
            }
            // Ghost permission accessors: `perm.ward()` and `perm.val()` return
            // references to the guarded value. Sort inference already treats
            // these as conservative Int-returning value accessors (#994), but
            // method dispatch was missing a corresponding arm, causing them to
            // fall through to the generic unknown-method error. (#2507)
            "ward" | "val" if args.is_empty() => {
                self.encode_int_method_uf(receiver, method, args, prefix)
            }
            // Snapshot::inner() — returns the inner value of a Snapshot<T>.
            // In verification context this is an identity/accessor operation.
            // Encode as Int-returning UF since we don't track the inner type. (#2697)
            "inner" | "into_inner" if args.is_empty() => {
                self.encode_int_method_uf(receiver, method, args, prefix)
            }
            // char::to_utf8() — returns Seq<u8> (UTF-8 byte sequence).
            // Encode as Seq-returning UF: receiver (Int/char) -> Seq(Int). (#2697)
            "to_utf8" if args.is_empty() => {
                let receiver_term = self.encode_pure_impl(receiver, prefix)?;
                let seq_sort = self.get_seq_sort();
                let func =
                    self.get_or_declare_method_func("method_to_utf8_1_i", &[Sort::Int], seq_sort);
                self.safe_apply("method_call::to_utf8", &func, &[receiver_term])
            }
            // empty(): Seq::empty() returns the seq_empty constant.
            // The ext_eq normalizer recognizes this at the PureExpr level, but
            // when encoding passes through the method dispatch, it needs a
            // concrete encoding path. Route to the logic function encoder which
            // handles `seq_empty` / `Seq::empty`. (#2652)
            "empty" if args.is_empty() => self.encode_logic_fn_call_impl("seq_empty", &[], prefix),
            // view(): delegate to encode_view_expr. The `@` operator is lowered
            // to PureExpr::View by the contract parser, but explicit `.view()`
            // method calls (e.g., in mutex.rs) arrive here instead. (#1963)
            "view" if args.is_empty() => self.encode_view_expr(receiver, prefix),
            // auth()/frag(): View resource-algebra projections. The trust-wp-std
            // `View<R>` stub exposes the authority/fragment halves as named struct
            // fields with `#[logic(open)]` accessors of the same names. When the
            // receiver is a literal `View` value (e.g., `resource@.frag()` after
            // `join_shared`), the accessor body is erased for the generic
            // instantiation, so the method call arrives here instead of resolving
            // to a registered logic function — previously failing as an
            // "unknown method `frag`" encoding error.
            //
            // Route through the named-field logic-fn (`__trust_wp_field_<name>`),
            // exactly as a struct-field projection would lower. This reuses the
            // existing named-field machinery: a native datatype selector when the
            // receiver is a registered `View` datatype, else a sort-correct
            // placeholder (`frag → FMap`, `auth → Option<FMap>`). Additive: it
            // only intercepts the otherwise-unsupported case. (RA view frag/auth)
            "auth" | "frag" if args.is_empty() => {
                if let Some(result) = self.try_logic_fn_dispatch(method, receiver, args, prefix) {
                    result
                } else {
                    let field_fn = format!(
                        "{}{method}",
                        trust_wp_core::formula::internal::tuple_lowering::NAMED_FIELD_LOGIC_FN_PREFIX
                    );
                    self.encode_logic_fn_call_impl(
                        &field_fn,
                        std::slice::from_ref(receiver),
                        prefix,
                    )
                }
            }
            // Fallback: treat unknown method calls as logic function calls.
            // In Creusot, users can call logic functions in method syntax:
            //   receiver.method(a, b) ≡ method(receiver, a, b)
            // When a method name matches a registered logic function, route
            // through the logic function encoder which handles declaration
            // lookup, axiom assertion, and sort inference.
            //
            // Otherwise, for quantifier-bound contexts (e.g., `forall<x>
            // x.f() > 0` in ghost context), fall back to an uninterpreted
            // function encoding. Outside quantifier scopes, unknown methods
            // are encoding errors — silently creating an Int-returning UF
            // is unsound when the actual return type is Bool or a complex
            // sort. (#1820)
            _ => {
                if let Some(result) = self.try_logic_fn_dispatch(method, receiver, args, prefix) {
                    result
                } else if self.method_has_bool_hint(receiver, method) {
                    // Sort hints indicate Bool return — encode as Bool predicate.
                    self.encode_bool_method_predicate(receiver, method, args, prefix)
                } else if self.has_bound_quantifier_vars() {
                    // Inside a quantifier scope: the receiver may be a bound
                    // variable with no type info. Encode as Int-returning UF
                    // so quantified postconditions with abstract method calls
                    // don't block verification.
                    self.encode_int_method_uf(receiver, method, args, prefix)
                } else {
                    Err(EncodingError::unsupported(format!(
                        "unknown method `{method}` is not a registered logic function \
                         and has no built-in encoding — add it to the method dispatch \
                         table or register it as a #[logic] function"
                    )))
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use ay_dpll::api::Sort;
    use ntest::timeout;

    use super::super::AYEncoder;

    // --- method_sort_tag ---

    #[test]
    #[timeout(30000)]
    fn method_sort_tag_bool() {
        assert_eq!(AYEncoder::method_sort_tag(&Sort::Bool), "b");
    }

    #[test]
    #[timeout(30000)]
    fn method_sort_tag_int() {
        assert_eq!(AYEncoder::method_sort_tag(&Sort::Int), "i");
    }

    #[test]
    #[timeout(30000)]
    fn method_sort_tag_seq() {
        assert_eq!(AYEncoder::method_sort_tag(&Sort::seq(Sort::Int)), "s");
    }

    #[test]
    #[timeout(30000)]
    fn method_sort_tag_datatype() {
        let iter_mut = ay_dpll::api::DatatypeSort {
            name: "IterMut".to_string(),
            constructors: vec![],
        };
        assert_eq!(
            AYEncoder::method_sort_tag(&Sort::Datatype(iter_mut)),
            "d497465724d7574"
        );
    }

    // --- bool_method_symbol ---

    #[test]
    #[timeout(30000)]
    fn bool_method_symbol_no_params() {
        let sym = AYEncoder::bool_method_symbol("is_empty", &[]);
        assert_eq!(sym, "method_is_empty_0_");
    }

    #[test]
    #[timeout(30000)]
    fn bool_method_symbol_single_int() {
        let sym = AYEncoder::bool_method_symbol("contains", &[Sort::Int]);
        assert_eq!(sym, "method_contains_1_i");
    }

    #[test]
    #[timeout(30000)]
    fn bool_method_symbol_mixed_sorts() {
        let sym = AYEncoder::bool_method_symbol("eq", &[Sort::Bool, Sort::Int]);
        assert_eq!(sym, "method_eq_2_b_i");
    }

    #[test]
    #[timeout(30000)]
    fn bool_method_symbol_uninterpreted_sort() {
        let sym =
            AYEncoder::bool_method_symbol("ext_eq", &[Sort::seq(Sort::Int), Sort::seq(Sort::Int)]);
        assert_eq!(sym, "method_ext_eq_2_s_s");
    }

    #[test]
    #[timeout(30000)]
    fn bool_method_symbol_distinguishes_uninterpreted_and_datatype_iter_mut() {
        let uninterpreted = AYEncoder::bool_method_symbol(
            "completed",
            &[Sort::Uninterpreted("IterMut".to_string())],
        );
        let datatype = AYEncoder::bool_method_symbol(
            "completed",
            &[Sort::Datatype(ay_dpll::api::DatatypeSort {
                name: "IterMut".to_string(),
                constructors: vec![],
            })],
        );

        assert_eq!(uninterpreted, "method_completed_1_u497465724d7574");
        assert_eq!(datatype, "method_completed_1_d497465724d7574");
        assert_ne!(
            uninterpreted, datatype,
            "datatype carriers must not reuse uninterpreted receiver symbols"
        );
    }
}
