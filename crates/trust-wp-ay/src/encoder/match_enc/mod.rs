// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Pattern matching and algebraic datatype encoding.
//!
//! Handles encoding of Rust `match` expressions as SMT if-then-else chains,
//! and provides constructor tester/accessor functions for Option, Result,
//! and `FSet` types.
//!
//! ## Module Structure
//!
//! - `mod.rs` — Core match ITE encoding, scrutinee sort resolution, shared selectors
//! - `enum_payload` — Registered enum payload projection axioms
//! - `spec_fn_helpers` — Sort-aware spec function declaration helpers
//! - `switch_target` — Match target inference and datatype construction
//! - `exhaustiveness` — Exhaustiveness checks for ITE default soundness
//! - `field_range` — Datatype field range axioms
//! - `sort_conflict` — Scrutinee sort conflict detection and fallback
//! - `deref_collapse` — Match-arm bound-variable rewrite helpers
//! - `pattern_condition` — Pattern binding extraction and condition encoding
//! - `datatype_spec` — Option/Result spec method encoding (`is_some`, `unwrap`, etc.)
//! - `collection_methods` — FSet and FMap method encoding

#[cfg(test)]
mod binder_scoped_view_tests;
mod collection_methods;
#[cfg(test)]
mod constructor_lookup_tests;
mod datatype_spec;
pub(crate) mod deref_collapse;
mod enum_payload;
#[cfg(test)]
mod enum_payload_tests;
mod exhaustiveness;
mod field_range;
mod pattern_condition;
mod sort_conflict;
mod spec_fn_helpers;
mod switch_target;

use std::collections::{BTreeSet, HashSet};

use ay_dpll::api::{DatatypeSort, FuncDecl, Sort, Term};
use tracing::{debug, warn};
use trust_wp_core::{
    formula::{
        internal::tuple_lowering::{
            tuple_field_logic_fn_name, NAMED_FIELD_LOGIC_FN_PREFIX, TUPLE_FIELD_LOGIC_FN_PREFIX,
        },
        ExprSort, MatchArm, PureExpr,
    },
    logic::{AdtConstructorDecl, AdtDecl, AdtFieldDecl, AdtKind},
};

use self::deref_collapse::collapse_deref_for_bound_vars;
pub(crate) use self::switch_target::{
    datatype_constructor_matches, datatype_constructor_name, is_stdlib_enum_qualifier,
    is_stdlib_payload_constructor, logical_constructor_alias_for_datatype,
    normalize_constructor_name, short_constructor_name, stdlib_constructor_target,
    stdlib_option_datatype_for_payload, MatchDatatypeKind, SwitchTarget,
};
use super::{closure_sorts::closure_env_sort_name, unsoundness, AYEncoder};
use crate::{
    encoder::sort_context::{
        apply_name_prefix, is_seq_family_sort, register_adt_family_alias, resolve_adt_family_alias,
        DerivedKind,
    },
    error::EncodingError,
};

#[derive(Clone)]
struct StructFieldGroundEntry {
    symbol: String,
    application: Term,
    receiver: Term,
}

impl AYEncoder {
    fn expr_sort_contains_seq(sort: &ExprSort) -> bool {
        match sort {
            ExprSort::Seq => true,
            ExprSort::Datatype(id) => {
                let name = trust_wp_core::formula::resolve_sort_name(*id);
                let path = name.split('<').next().unwrap_or(&name);
                let bare = path.rsplit("::").next().unwrap_or(path);
                crate::encoder::sort_context::sort_inference::is_seq_model_type(bare)
            }
            ExprSort::Ref(inner) | ExprSort::MutRef(inner) => Self::expr_sort_contains_seq(inner),
            _ => false,
        }
    }

    fn adt_decl_contains_seq_field(decl: &AdtDecl) -> bool {
        decl.constructors
            .iter()
            .flat_map(|ctor| ctor.fields.iter())
            .any(|field| Self::expr_sort_contains_seq(&field.sort))
    }

    fn match_scrutinee_name(
        scrutinee: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Option<String> {
        match scrutinee {
            PureExpr::Var(name, _) => Some(apply_name_prefix(name, prefix).into_owned()),
            PureExpr::Deref(inner) => match inner.as_ref() {
                PureExpr::Var(name, _) => {
                    let current_name = DerivedKind::Current.format_name(name);
                    Some(apply_name_prefix(&current_name, prefix).into_owned())
                }
                _ => None,
            },
            _ => None,
        }
    }

    pub(crate) fn register_adt_decls(&mut self, adt_decls: &trust_wp_core::logic::AdtDecls) {
        let mut entries = adt_decls
            .iter()
            .map(|(key, decl)| (key.clone(), decl.clone()))
            .collect::<Vec<_>>();
        entries.sort_by(|(left_key, left_decl), (right_key, right_decl)| {
            left_key
                .cmp(right_key)
                .then_with(|| left_decl.adt_name.cmp(&right_decl.adt_name))
        });

        for (adt_name, decl) in &entries {
            self.adt_state
                .insert_decl_if_absent(adt_name.clone(), decl.clone());
        }

        let decls = Self::adt_decls_dependency_first(adt_decls);
        if !decls.is_empty() || decls.iter().any(Self::adt_decl_contains_seq_field) {
            self.force_uninterpreted_seq_sort_for_mixed_datatype();
        }
        if crate::trust_wp_debug_enabled() {
            for decl in &decls {
                eprintln!(
                    "  [adt-declare-order] {} rust_path={}",
                    decl.adt_name, decl.rust_path
                );
            }
        }
        // Register every family alias before materializing any field sort. A
        // dependency can use the Rust path while the native declaration uses
        // the short ADT name.
        for decl in &decls {
            if let Some(adt_alias) = synthesized_enum_alias_name(decl) {
                // Match encoding still synthesizes `Adt_*` names from
                // constructor-only patterns. Register the source enum name so
                // sort-family resolution can bridge those names. (#2699)
                register_adt_family_alias(&adt_alias, &decl.adt_name);
            }
        }

        // AY 0.4 does not permit upgrading an already-used uninterpreted sort
        // into a native datatype. Declare acyclic local dependencies first so
        // an outer ADT field never reserves its inner ADT name as
        // uninterpreted merely because HashMap iteration visited it first.
        for decl in &decls {
            let datatype = self.datatype_from_adt_decl(decl);
            self.ensure_datatype_declared(&datatype);
        }

        for decl in &decls {
            self.assert_struct_field_placeholder_aliases_for_decl(decl);
        }
    }

    /// Order driver-extracted ADT declarations dependency-first: any
    /// declaration whose fields reference a sibling in `adt_decls` comes
    /// after that sibling. AY 0.4 registers a named-but-unknown field sort
    /// as an opaque sort on sight and refuses to upgrade it to a datatype
    /// later, so declaring a parent before its child leaves the child's own
    /// declare-datatype colliding with its opaque twin (#2706 generalized
    /// from OptionInt/ResultIntInt to the whole extracted graph).
    ///
    /// Ties break by name for determinism. Mutually recursive groups have no
    /// collision-free order without a group declaration form (which ay does
    /// not offer); their members fall back to name order and
    /// `ensure_datatype_declared` absorbs the residual collision.
    fn adt_decls_dependency_first(adt_decls: &trust_wp_core::logic::AdtDecls) -> Vec<AdtDecl> {
        let mut pending: Vec<(String, BTreeSet<String>, AdtDecl)> = adt_decls
            .iter()
            .map(|(adt_name, decl)| {
                let mut deps = BTreeSet::new();
                for field in decl.constructors.iter().flat_map(|ctor| ctor.fields.iter()) {
                    Self::collect_adt_field_sort_deps(&field.sort, adt_decls, &mut deps);
                }
                deps.remove(adt_name);
                (adt_name.clone(), deps, decl.clone())
            })
            .collect();
        pending.sort_by(|(a, _, _), (b, _, _)| a.cmp(b));

        let mut declared: HashSet<String> = HashSet::with_capacity(pending.len());
        let mut ordered = Vec::with_capacity(pending.len());
        while !pending.is_empty() {
            let next = pending
                .iter()
                .position(|(_, deps, _)| deps.iter().all(|dep| declared.contains(dep)))
                .unwrap_or(0);
            let (adt_name, _, decl) = pending.remove(next);
            ordered.push(decl);
            declared.insert(adt_name);
        }
        ordered
    }

    /// Collect the keys of sibling declarations in `adt_decls` that a field
    /// of this sort resolves to, mirroring the full-then-bare name lookup in
    /// `adt_field_sort`.
    ///
    /// The bare-name fallback only fires when the sibling really IS the
    /// field's type: a path-qualified field sort (e.g.
    /// `std::sync::MutexGuard`) that merely SHARES a bare name with a sibling
    /// user ADT (`MutexGuard`, `rust_path == "MutexGuard"`) is a distinct
    /// type, and treating it as a dependency manufactures a spurious cycle
    /// (user `MutexGuard` → `GuardInner` → std `MutexGuard`) that deadlocks
    /// the Kahn order into the collision-producing fallback (#2706 residual,
    /// tests/should_succeed/mutex.rs).
    fn collect_adt_field_sort_deps(
        sort: &ExprSort,
        adt_decls: &trust_wp_core::logic::AdtDecls,
        deps: &mut BTreeSet<String>,
    ) {
        match sort {
            ExprSort::Datatype(id) => {
                let name = trust_wp_core::formula::resolve_sort_name(*id);
                if adt_decls.contains_key(&name) {
                    deps.insert(name);
                    return;
                }
                let bare = name.rsplit("::").next().unwrap_or(&name);
                if let Some(sibling) = adt_decls.get(bare) {
                    if !name.contains("::") || sibling.rust_path == name {
                        deps.insert(bare.to_string());
                    }
                }
            }
            ExprSort::Ref(inner) | ExprSort::MutRef(inner) => {
                Self::collect_adt_field_sort_deps(inner, adt_decls, deps);
            }
            _ => {}
        }
    }

    pub(crate) fn adt_decl_for_name(&self, name: &str) -> Option<&AdtDecl> {
        self.adt_state.decl_for_name(name)
    }

    pub(crate) fn native_named_field_selector(
        &mut self,
        receiver_sort: &Sort,
        field_name: &str,
    ) -> Option<(String, Sort)> {
        let datatype_name = match receiver_sort {
            Sort::Datatype(dt) => dt.name.as_str(),
            Sort::Uninterpreted(name) => name.as_str(),
            _ => return None,
        };
        let (field_index, fallback_selector_name, fallback_sort) = {
            let decl = self.adt_decl_for_name(datatype_name)?;
            if decl.kind != AdtKind::Struct {
                return None;
            }
            let ctor = decl.constructors.first()?;
            let (field_index, field) = ctor
                .fields
                .iter()
                .enumerate()
                .find(|(_, field)| field.name == field_name)?;
            (
                field_index,
                Self::adt_field_selector_name(decl, ctor, field, field_index),
                field.sort.clone(),
            )
        };
        if let Some((selector_name, selector_sort)) =
            self.native_struct_selector_from_declared_datatype(receiver_sort, field_index)
        {
            return Some((selector_name, selector_sort));
        }
        Some((
            fallback_selector_name,
            self.sort_from_expr_sort(fallback_sort),
        ))
    }

    pub(crate) fn native_field_projection_return_sort(
        &mut self,
        fn_name: &str,
        receiver_sort: &Sort,
    ) -> Option<Sort> {
        let datatype_name = match receiver_sort {
            Sort::Datatype(dt) => dt.name.as_str(),
            Sort::Uninterpreted(name) => name.as_str(),
            _ => return None,
        };
        let field_sort = {
            let decl = self.adt_decl_for_name(datatype_name)?;
            if decl.kind != AdtKind::Struct {
                return None;
            }
            let ctor = decl.constructors.first()?;
            ctor.fields
                .iter()
                .enumerate()
                .find(|(field_index, field)| {
                    Self::adt_field_selector_name(decl, ctor, field, *field_index) == fn_name
                })?
                .1
                .sort
                .clone()
        };
        Some(self.sort_from_expr_sort(field_sort))
    }

    /// Resolve a positional tuple-get index to a native datatype selector when
    /// the receiver is a registered struct datatype.
    ///
    /// The driver rewrites `__trust_wp_field_x(p)` → `__trust_wp_tuple_get_N(p)`
    /// before the encoder sees the expression. When ADT metadata is present,
    /// this method recovers the native selector from the positional index,
    /// making struct field access use ay's native datatype theory instead of
    /// quantified tuple axioms. (#1982)
    pub(crate) fn native_positional_field_selector(
        &mut self,
        receiver_sort: &Sort,
        field_index: usize,
    ) -> Option<(String, Sort)> {
        if let Some(registered) = self.find_closure_struct_by_sort(receiver_sort) {
            let sort_name = closure_env_sort_name(&registered.sort)
                .or_else(|| closure_env_sort_name(receiver_sort))?;
            let suffix = sort_name.strip_prefix("ClosureEnv_")?;
            let (_, selector_sort, _) = registered.captures.get(field_index)?;
            return Some((
                format!("closure_capture_{suffix}_{field_index}"),
                selector_sort.clone(),
            ));
        }

        let datatype_name = match receiver_sort {
            Sort::Datatype(dt) => dt.name.as_str(),
            Sort::Uninterpreted(name) => name.as_str(),
            _ => return None,
        };
        let (fallback_selector_name, fallback_sort) = {
            let decl = self.adt_decl_for_name(datatype_name)?;
            if decl.kind != AdtKind::Struct {
                return None;
            }
            let ctor = decl.constructors.first()?;
            let field = ctor.fields.get(field_index)?;
            (
                Self::adt_field_selector_name(decl, ctor, field, field_index),
                field.sort.clone(),
            )
        };
        if let Some((selector_name, selector_sort)) =
            self.native_struct_selector_from_declared_datatype(receiver_sort, field_index)
        {
            return Some((selector_name, selector_sort));
        }
        Some((
            fallback_selector_name,
            self.sort_from_expr_sort(fallback_sort),
        ))
    }

    fn native_struct_selector_from_declared_datatype(
        &self,
        receiver_sort: &Sort,
        field_index: usize,
    ) -> Option<(String, Sort)> {
        let datatype = match receiver_sort {
            Sort::Datatype(dt) => Some(dt.clone()),
            Sort::Uninterpreted(name) => self.get_datatype_decl(name).cloned(),
            _ => None,
        }?;
        let ctor = datatype.constructors.first()?;
        let field = ctor.fields.get(field_index)?;
        Some((field.name.clone(), field.sort.clone()))
    }

    pub(crate) fn assert_struct_field_placeholder_aliases_for_accessor_name(
        &mut self,
        accessor_name: &str,
        param_sorts: &[Sort],
    ) {
        let Some(receiver_sort) = param_sorts.first() else {
            return;
        };
        if param_sorts.len() != 1 {
            return;
        }
        let Some(datatype_name) = Self::sort_datatype_name(receiver_sort) else {
            return;
        };
        let Some(decl) = self.adt_decl_for_name(datatype_name).cloned() else {
            return;
        };
        if self
            .struct_field_index_for_accessor_name(&decl, accessor_name)
            .is_some()
        {
            self.assert_struct_field_placeholder_aliases_for_decl(&decl);
        }
    }

    pub(crate) fn assert_ground_struct_field_placeholder_aliases_for_accessor_call(
        &mut self,
        accessor_name: &str,
        param_sorts: &[Sort],
        arg_terms: &[Term],
        result: Term,
    ) {
        let Some(receiver_term) = arg_terms.first().copied() else {
            return;
        };
        if arg_terms.len() != 1 {
            return;
        }
        let actual_receiver_sort = self.solver.get_sort(receiver_term);
        let decl = self
            .struct_decl_for_accessor_sort(&actual_receiver_sort, accessor_name)
            .or_else(|| {
                if param_sorts.len() != 1 {
                    return None;
                }
                let receiver_sort = param_sorts.first()?;
                self.struct_decl_for_accessor_sort(receiver_sort, accessor_name)
            });
        let Some(decl) = decl else { return };
        let Some(field_index) = self.struct_field_index_for_accessor_name(&decl, accessor_name)
        else {
            return;
        };
        let Some(ctor) = decl.constructors.first() else {
            return;
        };
        let Some(field) = ctor.fields.get(field_index) else {
            return;
        };
        self.remember_struct_field_placeholder_application(accessor_name, result, receiver_term);

        let placeholders = self.struct_field_placeholder_decls(&decl, field_index, &field.name);
        for (_, func_decl) in placeholders {
            let domain = func_decl.domain();
            if domain.len() != 1
                || domain[0].as_term_sort() != actual_receiver_sort.as_term_sort()
                || !Self::field_alias_ranges_compatible(
                    func_decl.range(),
                    &self.solver.get_sort(result),
                )
            {
                continue;
            }
            let Ok(peer) = self.solver.try_apply(&func_decl, &[receiver_term]) else {
                continue;
            };
            let eq = self.eq_term(result, peer);
            self.assert_solver_term("struct_field_alias/ground_pair", eq);
            self.assert_ground_seq_len_alias_for_equal_terms(result, peer);
        }

        let Some((selector_name, selector_sort)) =
            self.native_positional_field_selector(&actual_receiver_sort, field_index)
        else {
            return;
        };
        if !Self::field_alias_ranges_compatible(&self.solver.get_sort(result), &selector_sort) {
            return;
        }
        let Ok(native) =
            self.solver
                .try_datatype_selector(&selector_name, receiver_term, selector_sort)
        else {
            return;
        };
        let eq = self.eq_term(result, native);
        self.assert_solver_term("struct_field_alias/ground_native", eq);
        self.assert_ground_seq_len_alias_for_equal_terms(result, native);
    }

    pub(crate) fn assert_struct_field_placeholder_aliases(&mut self) {
        let decls = self.adt_state.decls_iter().cloned().collect::<Vec<_>>();
        for decl in &decls {
            self.assert_struct_field_placeholder_aliases_for_decl(decl);
        }
    }

    pub(crate) fn assert_struct_field_placeholder_ground_aliases(&mut self) -> usize {
        let decls = self.adt_state.decls_iter().cloned().collect::<Vec<_>>();
        let mut asserted = 0usize;
        for decl in &decls {
            asserted += self.assert_struct_field_placeholder_ground_aliases_for_decl(decl);
        }
        asserted
    }

    fn assert_struct_field_placeholder_aliases_for_decl(&mut self, decl: &AdtDecl) {
        if !self.traversal.supports_quantifiers || decl.kind != AdtKind::Struct {
            return;
        }
        let Some(ctor) = decl.constructors.first() else {
            return;
        };

        for (field_index, field) in ctor.fields.iter().enumerate() {
            let placeholders = self.struct_field_placeholder_decls(decl, field_index, &field.name);
            for (name, func_decl) in &placeholders {
                self.assert_struct_field_placeholder_native_alias(
                    decl,
                    field_index,
                    name,
                    func_decl,
                );
            }
            for left_index in 0..placeholders.len() {
                for right_index in (left_index + 1)..placeholders.len() {
                    let (left_name, left_decl) = &placeholders[left_index];
                    let (right_name, right_decl) = &placeholders[right_index];
                    self.assert_struct_field_placeholder_pair_alias(
                        decl,
                        field_index,
                        left_name,
                        left_decl,
                        right_name,
                        right_decl,
                    );
                }
            }
        }
    }

    fn assert_struct_field_placeholder_ground_aliases_for_decl(&mut self, decl: &AdtDecl) -> usize {
        if decl.kind != AdtKind::Struct {
            return 0;
        }
        let Some(ctor) = decl.constructors.first() else {
            return 0;
        };

        let mut asserted = 0usize;
        for (field_index, field) in ctor.fields.iter().enumerate() {
            let entries =
                self.struct_field_placeholder_ground_entries(field_index, &field.name, decl);
            for left_index in 0..entries.len() {
                for right_index in (left_index + 1)..entries.len() {
                    let left = &entries[left_index];
                    let right = &entries[right_index];
                    if left.receiver != right.receiver || left.application == right.application {
                        continue;
                    }
                    let left_sort = self.solver.get_sort(left.application);
                    let right_sort = self.solver.get_sort(right.application);
                    if !Self::field_alias_ranges_compatible(&left_sort, &right_sort) {
                        continue;
                    }
                    let key = format!(
                        "ground_pair:{}:{field_index}:{}:{}:{:?}",
                        decl.adt_name, left.symbol, right.symbol, left.receiver
                    );
                    if !self.struct_field_alias_axioms.insert(key) {
                        continue;
                    }
                    let eq = self.eq_term(left.application, right.application);
                    if self.assert_solver_term("struct_field_alias/ground_pair", eq) {
                        asserted += 1;
                    }
                    if self.assert_ground_seq_len_alias_for_equal_terms(
                        left.application,
                        right.application,
                    ) {
                        asserted += 1;
                    }
                }
            }

            for entry in &entries {
                let receiver_sort = self.solver.get_sort(entry.receiver);
                let Some((selector_name, selector_sort)) =
                    self.native_positional_field_selector(&receiver_sort, field_index)
                else {
                    continue;
                };
                let application_sort = self.solver.get_sort(entry.application);
                if !Self::field_alias_ranges_compatible(&application_sort, &selector_sort) {
                    continue;
                }
                let Ok(native) = self.solver.try_datatype_selector(
                    &selector_name,
                    entry.receiver,
                    selector_sort,
                ) else {
                    continue;
                };
                let key = format!(
                    "ground_native:{}:{field_index}:{}:{:?}",
                    decl.adt_name, entry.symbol, entry.receiver
                );
                if !self.struct_field_alias_axioms.insert(key) {
                    continue;
                }
                let eq = self.eq_term(entry.application, native);
                if self.assert_solver_term("struct_field_alias/ground_native", eq) {
                    asserted += 1;
                }
                if self.assert_ground_seq_len_alias_for_equal_terms(entry.application, native) {
                    asserted += 1;
                }
            }
        }
        asserted
    }

    pub(in crate::encoder) fn assert_ground_seq_len_alias_for_equal_terms(
        &mut self,
        left: Term,
        right: Term,
    ) -> bool {
        let left_sort = self.solver.get_sort(left).as_term_sort();
        let right_sort = self.solver.get_sort(right).as_term_sort();
        if !left_sort.is_seq() || left_sort != right_sort {
            return false;
        }
        let Ok(left_len) = self.seq_len_term(left) else {
            return false;
        };
        let Ok(right_len) = self.seq_len_term(right) else {
            return false;
        };
        if left_len == right_len {
            return false;
        }
        let eq = self.eq_term(left_len, right_len);
        self.assert_solver_term("struct_field_alias/ground_seq_len", eq)
    }

    fn struct_decl_for_accessor_sort(
        &self,
        receiver_sort: &Sort,
        accessor_name: &str,
    ) -> Option<AdtDecl> {
        let datatype_name = Self::sort_datatype_name(receiver_sort)?;
        let decl = self.adt_decl_for_name(datatype_name)?;
        if decl.kind != AdtKind::Struct {
            return None;
        }
        self.struct_field_index_for_accessor_name(decl, accessor_name)?;
        Some(decl.clone())
    }

    fn struct_field_placeholder_ground_entries(
        &mut self,
        field_index: usize,
        field_name: &str,
        decl: &AdtDecl,
    ) -> Vec<StructFieldGroundEntry> {
        let mut accessor_names = vec![tuple_field_logic_fn_name(field_index)];
        if !field_name.is_empty() {
            accessor_names.push(format!("{NAMED_FIELD_LOGIC_FN_PREFIX}{field_name}"));
        }

        let accessor_symbols = accessor_names
            .iter()
            .map(|name| trust_wp_core::logic::logic_fn_smt_name(name))
            .collect::<Vec<_>>();
        let mut entries = Vec::new();
        for symbol in &accessor_symbols {
            let Some(ground_entries) = self.ground_pool.entries_for(symbol) else {
                continue;
            };
            for entry in ground_entries {
                let [receiver] = entry.arg_terms.as_slice() else {
                    continue;
                };
                let receiver_sort = self.solver.get_sort(*receiver);
                if !Self::sort_matches_adt_name(&receiver_sort, &decl.adt_name) {
                    continue;
                }
                entries.push(StructFieldGroundEntry {
                    symbol: symbol.clone(),
                    application: entry.application,
                    receiver: *receiver,
                });
            }
        }
        for (symbol, application, receiver) in &self.struct_field_ground_applications {
            if !accessor_symbols.iter().any(|known| known == symbol) {
                continue;
            }
            let receiver_sort = self.solver.get_sort(*receiver);
            if !Self::sort_matches_adt_name(&receiver_sort, &decl.adt_name) {
                continue;
            }
            if entries.iter().any(|entry| {
                entry.symbol == symbol.as_str()
                    && entry.application == *application
                    && entry.receiver == *receiver
            }) {
                continue;
            }
            entries.push(StructFieldGroundEntry {
                symbol: symbol.clone(),
                application: *application,
                receiver: *receiver,
            });
        }
        let placeholders = self.struct_field_placeholder_decls(decl, field_index, field_name);
        for (symbol, func_decl) in &placeholders {
            let domain = func_decl.domain();
            let Some(expected_receiver_sort) = domain.first() else {
                continue;
            };
            if domain.len() != 1
                || !Self::sort_matches_adt_name(expected_receiver_sort, &decl.adt_name)
            {
                continue;
            }
            for var_name in self.var_env.var_names() {
                let Some(receiver) = self.var_env.var_term(&var_name) else {
                    continue;
                };
                let receiver_sort = self.solver.get_sort(receiver);
                if receiver_sort.as_term_sort() != expected_receiver_sort.as_term_sort()
                    || !Self::sort_matches_adt_name(&receiver_sort, &decl.adt_name)
                {
                    continue;
                }
                let Ok(application) = self.solver.try_apply(func_decl, &[receiver]) else {
                    continue;
                };
                if entries.iter().any(|entry| {
                    entry.symbol == symbol.as_str()
                        && entry.application == application
                        && entry.receiver == receiver
                }) {
                    continue;
                }
                entries.push(StructFieldGroundEntry {
                    symbol: symbol.clone(),
                    application,
                    receiver,
                });
            }
        }
        entries
    }

    fn remember_struct_field_placeholder_application(
        &mut self,
        accessor_name: &str,
        application: Term,
        receiver: Term,
    ) {
        let symbol = trust_wp_core::logic::logic_fn_smt_name(accessor_name);
        if self.struct_field_ground_applications.iter().any(
            |(known_symbol, known_application, known_receiver)| {
                *known_symbol == symbol
                    && *known_application == application
                    && *known_receiver == receiver
            },
        ) {
            return;
        }
        self.struct_field_ground_applications
            .push((symbol, application, receiver));
    }

    fn struct_field_placeholder_decls(
        &self,
        decl: &AdtDecl,
        field_index: usize,
        field_name: &str,
    ) -> Vec<(String, FuncDecl)> {
        let mut prefixes = vec![format!(
            "{}__placeholder_",
            trust_wp_core::logic::logic_fn_smt_name(&tuple_field_logic_fn_name(field_index))
        )];
        if !field_name.is_empty() {
            prefixes.push(format!(
                "{}__placeholder_",
                trust_wp_core::logic::logic_fn_smt_name(&format!(
                    "{NAMED_FIELD_LOGIC_FN_PREFIX}{field_name}"
                ))
            ));
        }

        self.logic_funcs_iter()
            .filter_map(|(name, func_decl)| {
                if !prefixes.iter().any(|prefix| name.starts_with(prefix)) {
                    return None;
                }
                let domain = func_decl.domain();
                let receiver_sort = domain.first()?;
                if domain.len() != 1 || !Self::sort_matches_adt_name(receiver_sort, &decl.adt_name)
                {
                    return None;
                }
                Some((name.clone(), func_decl.clone()))
            })
            .collect()
    }

    fn assert_struct_field_placeholder_pair_alias(
        &mut self,
        decl: &AdtDecl,
        field_index: usize,
        left_name: &str,
        left_decl: &FuncDecl,
        right_name: &str,
        right_decl: &FuncDecl,
    ) {
        if left_decl.domain() != right_decl.domain()
            || !Self::field_alias_ranges_compatible(left_decl.range(), right_decl.range())
        {
            return;
        }
        let key = format!(
            "pair:{}:{field_index}:{left_name}:{right_name}",
            decl.adt_name
        );
        if !self.struct_field_alias_axioms.insert(key) {
            return;
        }

        let Some(receiver_sort) = left_decl.domain().first().cloned() else {
            return;
        };
        let receiver = self.solver.fresh_var(
            &format!("struct_field_alias_{}_{}", decl.adt_name, field_index),
            receiver_sort,
        );
        let left = self.solver.apply(left_decl, &[receiver]);
        let right = self.solver.apply(right_decl, &[receiver]);
        let eq = self.eq_term(left, right);
        let axiom = self
            .solver
            .forall_with_triggers(&[receiver], eq, &[&[left]]);
        self.assert_solver_term("struct_field_alias/pair", axiom);
    }

    fn assert_struct_field_placeholder_native_alias(
        &mut self,
        decl: &AdtDecl,
        field_index: usize,
        placeholder_name: &str,
        placeholder_decl: &FuncDecl,
    ) {
        let Some(receiver_sort) = placeholder_decl.domain().first().cloned() else {
            return;
        };
        if placeholder_decl.domain().len() != 1
            || !Self::sort_matches_adt_name(&receiver_sort, &decl.adt_name)
        {
            return;
        }
        let key = format!("native:{}:{field_index}:{placeholder_name}", decl.adt_name);

        let Some((selector_name, selector_sort)) =
            self.native_positional_field_selector(&receiver_sort, field_index)
        else {
            return;
        };
        if !Self::field_alias_ranges_compatible(placeholder_decl.range(), &selector_sort) {
            return;
        }

        let receiver = self.solver.fresh_var(
            &format!(
                "struct_field_native_alias_{}_{}",
                decl.adt_name, field_index
            ),
            receiver_sort,
        );
        let placeholder = self.solver.apply(placeholder_decl, &[receiver]);
        let Ok(native) = self
            .solver
            .try_datatype_selector(&selector_name, receiver, selector_sort)
        else {
            return;
        };
        if !self.struct_field_alias_axioms.insert(key) {
            return;
        }
        let eq = self.eq_term(placeholder, native);
        let axiom = self
            .solver
            .forall_with_triggers(&[receiver], eq, &[&[placeholder]]);
        self.assert_solver_term("struct_field_alias/native", axiom);
    }

    fn field_alias_ranges_compatible(left: &Sort, right: &Sort) -> bool {
        left == right
            || matches!(
                (left, right),
                (Sort::Bool, Sort::Int) | (Sort::Int, Sort::Bool)
            )
    }

    fn struct_field_index_for_accessor_name(
        &self,
        decl: &AdtDecl,
        accessor_name: &str,
    ) -> Option<usize> {
        if let Some(index_str) = accessor_name.strip_prefix(TUPLE_FIELD_LOGIC_FN_PREFIX) {
            return index_str.parse::<usize>().ok();
        }
        let field_name = accessor_name.strip_prefix(NAMED_FIELD_LOGIC_FN_PREFIX)?;
        let ctor = decl.constructors.first()?;
        ctor.fields
            .iter()
            .position(|field| field.name == field_name)
    }

    fn sort_datatype_name(sort: &Sort) -> Option<&str> {
        match sort {
            Sort::Datatype(dt) => Some(dt.name.as_str()),
            Sort::Uninterpreted(name) => Some(name.as_str()),
            _ => None,
        }
    }

    fn sort_matches_adt_name(sort: &Sort, adt_name: &str) -> bool {
        let Some(sort_name) = Self::sort_datatype_name(sort) else {
            return false;
        };
        sort_name == adt_name
            || sort_name.rsplit("::").next() == Some(adt_name)
            || adt_name.rsplit("::").next() == Some(sort_name)
    }

    pub(crate) fn datatype_from_adt_decl(&mut self, decl: &AdtDecl) -> DatatypeSort {
        let constructors = decl
            .constructors
            .iter()
            .map(|ctor| ay_dpll::api::DatatypeConstructor {
                name: ctor.smt_name.clone(),
                fields: ctor
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(field_index, field)| {
                        let sort = self.adt_field_sort(field);
                        ay_dpll::api::DatatypeField {
                            name: Self::adt_field_selector_name_for_sort(
                                decl,
                                ctor,
                                field,
                                field_index,
                                &sort,
                            ),
                            sort,
                        }
                    })
                    .collect(),
            })
            .collect();
        DatatypeSort {
            name: decl.adt_name.clone(),
            constructors,
        }
    }

    fn adt_field_sort(&mut self, field: &AdtFieldDecl) -> Sort {
        match &field.sort {
            ExprSort::Datatype(id) => {
                let name = trust_wp_core::formula::resolve_sort_name(*id);
                // #prophecy-slots (Fix B M1): an `Option<&mut T>` field sort
                // routes through `sort_from_expr_sort`, which declares the
                // specialized carrier Option family (payload at the mutref
                // record sort) before the enclosing datatype mentions it —
                // the same declare-before-use discipline as the
                // OptionInt/ResultIntInt block below (#2706).
                if crate::encoder::sort_context::sort_mapping::parse_mutref_instantiated_option(
                    &name,
                )
                .is_some()
                    || crate::encoder::sort_context::sort_mapping::parse_mutref_carrier_tuple(&name)
                        .is_some()
                {
                    return self.sort_from_expr_sort(field.sort.clone());
                }
                let bare = name.rsplit("::").next().unwrap_or(&name);
                // Declare reserved stdlib datatypes before an outer datatype
                // mentions them as field sorts. AY 0.4 registers an
                // undeclared datatype field as an uninterpreted sort and
                // correctly refuses to upgrade that sort later. Nested
                // patterns such as `OwnResult::Ok(Some(x))` therefore need
                // OptionInt in the registry before OwnResult is declared.
                // (#2706)
                if matches!(bare, "OptionInt" | "ResultIntInt") {
                    let datatype = match bare {
                        "OptionInt" => SwitchTarget::OptionInt.datatype(),
                        "ResultIntInt" => SwitchTarget::ResultIntInt.datatype(),
                        _ => unreachable!("guarded standard datatype name"),
                    };
                    self.ensure_datatype_declared(&datatype);
                    return Sort::Datatype(
                        self.get_datatype_decl(bare).cloned().unwrap_or(datatype),
                    );
                }
                // A path-qualified field sort that merely SHARES a bare name
                // with a registered user ADT (e.g. std `std::sync::Mutex`
                // inside `MutexInner` vs the user's `Mutex`) is a DISTINCT
                // type. Emitting `Uninterpreted(bare)` for it would register
                // the user ADT's name as an opaque sort in ay before its own
                // declare-datatype runs (AY 0.4 registers field sorts on
                // sight and refuses the upgrade), and resolving it through
                // the bare registry fallback would conflate the two types.
                // Keep the full path as the opaque sort name instead —
                // conservative: an unconstrained opaque field, no false
                // proofs. (#2706 residual, tests/should_succeed/mutex.rs)
                if name.contains("::") {
                    let conflates_sibling_adt = self
                        .adt_decl_for_name(bare)
                        .is_some_and(|sibling| sibling.rust_path != name);
                    if conflates_sibling_adt {
                        return self.get_datatype_decl(&name).map_or_else(
                            || Sort::Uninterpreted(name.clone()),
                            |dt| Sort::Datatype(dt.clone()),
                        );
                    }
                }
                self.get_datatype_decl(&name)
                    .or_else(|| self.get_datatype_decl(bare))
                    .map_or_else(
                        || Sort::Uninterpreted(bare.to_string()),
                        |dt| Sort::Datatype(dt.clone()),
                    )
            }
            _ => self.sort_from_expr_sort(field.sort.clone()),
        }
    }

    fn adt_field_selector_name(
        decl: &AdtDecl,
        ctor: &AdtConstructorDecl,
        field: &AdtFieldDecl,
        field_index: usize,
    ) -> String {
        let field_suffix = if field.name.is_empty() {
            field_index.to_string()
        } else {
            field.name.clone()
        };
        match decl.kind {
            AdtKind::Struct => format!("{}_{}", decl.adt_name.to_lowercase(), field_suffix),
            AdtKind::Enum => format!(
                "{}_{}_{}",
                decl.adt_name.to_lowercase(),
                ctor.smt_name.to_lowercase(),
                field_suffix
            ),
            _ => format!(
                "{}_{}_{}",
                decl.adt_name.to_lowercase(),
                ctor.smt_name.to_lowercase(),
                field_suffix
            ),
        }
    }

    fn adt_field_selector_name_for_sort(
        decl: &AdtDecl,
        ctor: &AdtConstructorDecl,
        field: &AdtFieldDecl,
        field_index: usize,
        sort: &Sort,
    ) -> String {
        let base = Self::adt_field_selector_name(decl, ctor, field, field_index);
        if decl.adt_name == "List"
            && short_constructor_name(&ctor.smt_name) == "Cons"
            && field_index == 0
        {
            let tag = selector_sort_tag(sort);
            format!("{base}__ret_{tag}")
        } else {
            base
        }
    }

    /// Encode a match expression as nested if-then-else.
    ///
    /// Match expressions are encoded by building an ITE (if-then-else) chain:
    /// - Start with the last arm's body as the default
    /// - For each arm (in reverse), wrap with `ite(condition, arm_body, previous)`
    ///
    /// # Pattern Conditions
    ///
    /// - `Wildcard` / `Binding(_)`: Always true (matches everything)
    /// - `Literal(lit)`: `scrutinee == lit`
    /// - `Constructor { name, .. }`: Uses constructor tester function
    ///   - `Some`: `is_some(scrutinee)`
    ///   - `None`: `not(is_some(scrutinee))`
    ///   - Other: `is_<name>(scrutinee)`
    pub(super) fn encode_match_impl(
        &mut self,
        scrutinee: &PureExpr,
        arms: &[MatchArm],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        if arms.is_empty() {
            return Ok(self.solver.bool_const(false));
        }

        // #prophecy-slots (Fix B M2): a scrutinee annotated with an
        // instantiation-suffixed `Option<&mut ..>` name must have its
        // specialized carrier family DECLARED before `match_datatype` runs.
        // `match_datatype` is `&self` and resolves the annotation through the
        // STATELESS converter, which by design returns the family name as an
        // uninterpreted sort — so without this the family is never in the
        // registry, the match falls back to `OptionInt`, `datatype` ends up
        // `None`, and the payload is extracted through the Int-ranged
        // `spec_unwrap` UF: the prophecy slot is silently dropped one step
        // before the binder. `Sort::Datatype(dt).as_term_sort()` IS
        // `Uninterpreted(dt.name)`, so a scrutinee already declared at the
        // opaque spelling stays sort-compatible with the declared family.
        self.ensure_instantiated_option_family_for_scrutinee(scrutinee);

        let mut datatype = self.match_datatype(scrutinee, arms, prefix);
        if let Some(ref dt) = datatype {
            if self.scrutinee_has_conflicting_sort(scrutinee, dt, prefix) {
                datatype = self.scrutinee_existing_datatype(scrutinee, prefix);
            }
        }
        if let Some(dt) = datatype.take() {
            self.ensure_datatype_declared(&dt);
            datatype = Some(self.canonical_declared_datatype(&dt));
        }
        let exhaustiveness_datatype = datatype
            .as_ref()
            .filter(|dt| Self::datatype_matches_arms(dt, arms))
            .cloned()
            .or_else(|| {
                SwitchTarget::from_arms(arms).map(|target| {
                    let target_datatype = target.datatype();
                    self.canonical_declared_datatype(&target_datatype)
                })
            });
        let scrutinee_term = self.encode_match_scrutinee(scrutinee, datatype.as_ref(), prefix)?;

        if let Some(dt) = datatype.as_ref() {
            self.assert_ground_field_range_constraints(scrutinee_term, dt);
        }

        let last_arm = arms.last().expect("non-empty by early return above");

        if !Self::is_catch_all_pattern(&last_arm.pattern) {
            let exhaustive = Self::is_constructor_exhaustive(
                arms,
                exhaustiveness_datatype.as_ref().or(datatype.as_ref()),
            );
            if !exhaustive {
                return Err(EncodingError::unsupported(format!(
                    "match expression last arm is not a catch-all pattern \
                     (found {:?}) and match is not exhaustive over a known datatype; \
                     non-exhaustive contract matches are unsound in the ITE encoding",
                    last_arm.pattern,
                )));
            }
        }

        let mut result =
            self.encode_match_arm_body(scrutinee_term, last_arm, datatype.as_ref(), prefix, false)?;

        for arm in arms[..arms.len() - 1].iter().rev() {
            let cond = self.encode_pattern_condition_impl(
                scrutinee_term,
                &arm.pattern,
                datatype.as_ref(),
                prefix,
            )?;
            let body =
                self.encode_match_arm_body(scrutinee_term, arm, datatype.as_ref(), prefix, false)?;
            // Use safe_ite which harmonizes branch sorts and catches ay panics
            // from residual sort mismatches (e.g., OptionInt vs Option). (#2699)
            result = self.safe_ite(cond, body, result);
        }

        Ok(result)
    }

    /// Look up a declared datatype that owns the given constructor name.
    ///
    /// Returns `Some(dt)` when a previously declared datatype has a constructor
    /// matching `ctor_name` (e.g., `"Some"` → OptionInt, `"Ok"` → ResultIntInt,
    /// `"OwnResult::Ok"` → OwnResult). Returns `None` if no matching
    /// datatype has been declared yet.
    ///
    /// Handles both unqualified names (`"Ok"`) and qualified names
    /// (`"OwnResult::Ok"`). For qualified names, the prefix is compared
    /// against the datatype's ADT name to avoid ambiguity when multiple
    /// enums share constructor names. (#967, #1296)
    ///
    /// Used by `encode_logic_fn_call_impl` to route constructor calls
    /// through the native ay datatype constructor path instead of an
    /// uninterpreted function, preventing sort mismatches.
    pub(crate) fn constructor_datatype(&self, ctor_name: &str) -> Option<DatatypeSort> {
        let normalized = normalize_constructor_name(ctor_name);
        let short = short_constructor_name(normalized);
        let qualifier = normalized
            .rsplit_once("::")
            .map(|(prefix, _)| prefix.replace("::", "_"));
        let stdlib_qualified = is_stdlib_enum_qualifier(normalized, short) && qualifier.is_some();
        let candidates = self.datatypes_for_constructor(short).collect::<Vec<_>>();
        if let Some(ref q) = qualifier {
            if let Some(dt) = candidates
                .iter()
                .copied()
                .find(|dt| resolve_adt_family_alias(&dt.name).as_deref() == Some(q.as_str()))
            {
                return Some(dt.clone());
            }
        }

        if qualifier.is_none() {
            if let Some(dt) = candidates
                .iter()
                .copied()
                .find(|dt| resolve_adt_family_alias(&dt.name).is_some())
            {
                return Some(dt.clone());
            }
        }

        for dt in candidates {
            if let Some(ref q) = qualifier {
                let allow_stdlib_fallback =
                    stdlib_qualified && matches!(dt.name.as_str(), "OptionInt" | "ResultIntInt");
                let allow_family_alias =
                    resolve_adt_family_alias(&dt.name).as_deref() == Some(q.as_str());
                if dt.name != *q && !allow_stdlib_fallback && !allow_family_alias {
                    continue;
                }
            }
            return Some(dt.clone());
        }
        None
    }

    /// Look up a declared datatype only when `ctor_name` is a zero-field constructor.
    ///
    /// Bare parser tokens like `Var("On")` should route through the native
    /// constructor path only for nullary variants. Non-nullary constructors such as
    /// `Some` remain `LogicFnCall` nodes and must not be mistaken for free vars.
    /// (#1982 Slice 5)
    pub(crate) fn nullary_constructor_datatype(&self, ctor_name: &str) -> Option<DatatypeSort> {
        let datatype = self.constructor_datatype(ctor_name)?;
        datatype
            .constructors
            .iter()
            .any(|ctor| {
                datatype_constructor_matches(&datatype, &ctor.name, ctor_name)
                    && ctor.fields.is_empty()
            })
            .then_some(datatype)
    }

    pub(crate) fn stdlib_option_datatype_for_payload_sort(
        &mut self,
        payload_sort: Sort,
    ) -> DatatypeSort {
        let payload_sort = if is_seq_family_sort(&payload_sort) {
            self.get_seq_sort()
        } else {
            payload_sort
        };
        stdlib_option_datatype_for_payload(payload_sort.as_term_sort())
    }

    /// Canonicalize a reserved native-encoding sort name before it reaches a
    /// solver declaration. `OptionInt`/`ResultIntInt` are RESERVED datatype
    /// names: `normalize_sort` already rewrites variable declarations from
    /// `Uninterpreted("OptionInt")` to the declared datatype, but UF
    /// signatures (`declare_fun`) bypassed that path. AY 0.4 registers an
    /// unknown sort named in a `declare_fun` on sight as an opaque sort and
    /// then refuses the later declare-datatype upgrade, leaving every
    /// constructor/selector lookup in the VC failing (`option_some_value`
    /// not declared). Declaring the datatype first and using its sort keeps
    /// both sides consistent. (#2706 residual: ghost_vec, list_index_mut)
    pub(crate) fn canonicalize_reserved_uf_sort(&mut self, sort: Sort) -> Sort {
        if let Sort::Uninterpreted(ref name) = sort {
            let well_known = match name.as_str() {
                "OptionInt" => Some(SwitchTarget::OptionInt.datatype()),
                "ResultIntInt" => Some(SwitchTarget::ResultIntInt.datatype()),
                _ => None,
            };
            if let Some(datatype) = well_known {
                let datatype = self.get_datatype_decl(name).cloned().unwrap_or(datatype);
                self.ensure_datatype_declared(&datatype);
                return Sort::Datatype(datatype);
            }
        }
        sort
    }

    pub(crate) fn ensure_datatype_declared(&mut self, datatype: &DatatypeSort) {
        if self.has_datatype_decl(&datatype.name) {
            return;
        }

        self.force_uninterpreted_seq_sort_for_mixed_datatype();
        if let Err(e) = self.solver.try_declare_datatype(datatype) {
            // AY 0.4 already registered this name as an opaque sort (it was
            // seen first as a field of an earlier declaration) and refuses
            // the upgrade. Keep the opaque view on both sides: registering
            // in trust-wp's registry without a solver declaration would
            // route later constructor lookups into the panicking
            // `datatype_constructor` path. The opaque fallback is
            // conservative (unconstrained terms, no false proofs), but
            // track it as a skipped construct for observability. (#2706)
            warn!(
                "skipping datatype declaration '{}' rejected by solver: {e}",
                datatype.name
            );
            unsoundness::increment(unsoundness::UnsoundnessCategory::UnsupportedConstructSkip);
            return;
        }
        self.register_datatype(datatype.name.clone(), datatype.clone());

        self.assert_adt_field_range_ground_assumptions(datatype);
        self.assert_datatype_discriminant_axioms(datatype);
    }

    pub(crate) fn canonical_declared_datatype(&self, datatype: &DatatypeSort) -> DatatypeSort {
        self.get_datatype_decl(&datatype.name)
            .cloned()
            .or_else(|| {
                resolve_adt_family_alias(&datatype.name)
                    .and_then(|alias| self.get_datatype_decl(&alias).cloned())
            })
            .unwrap_or_else(|| datatype.clone())
    }

    fn encode_match_scrutinee(
        &mut self,
        scrutinee: &PureExpr,
        datatype: Option<&DatatypeSort>,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        if let (PureExpr::Var(name, _), Some(datatype)) = (scrutinee, datatype) {
            let var_name = apply_name_prefix(name, prefix);
            return self.get_or_declare_var(&var_name, Sort::Datatype(datatype.clone()));
        }
        if let (PureExpr::Deref(inner), Some(datatype)) = (scrutinee, datatype) {
            if let PureExpr::Var(name, _) = inner.as_ref() {
                let base_current = DerivedKind::Current.format_name(name);
                let current_name = apply_name_prefix(&base_current, prefix).into_owned();
                return self.get_or_declare_var(&current_name, Sort::Datatype(datatype.clone()));
            }
        }

        if let PureExpr::Var(name, _) = scrutinee {
            let var_name = apply_name_prefix(name, prefix).into_owned();
            if let Some(term) = self.var_term(&var_name) {
                return Ok(term);
            }
        }

        self.preseed_tuple_getter_placeholder_for_match_scrutinee(scrutinee, datatype, prefix);
        self.encode_pure_impl(scrutinee, prefix)
    }

    /// Preseed a sort-typed tuple-getter placeholder for a match SCRUTINEE,
    /// using the match arms' resolved datatype (#getters2).
    ///
    /// The open-logic-fn inliner rewrites `sum(get_1(t))` into
    /// `Match { scrutinee: get_1(t), arms: <sum's body> }` BEFORE encoding, so
    /// the getter reaches the placeholder mint as a bare scrutinee: the
    /// callee-domain preseed (87b48b9 seam 2) never sees a callee, and the
    /// ctor-domain derivation (seam 1) has no `__trust_wp_tupleN` declaration
    /// yet in requires-phase scopes. The getter then defaults to `Int` and the
    /// arm encoding degrades to the non-datatype tester fallback.
    ///
    /// That stale `Int`-ranged getter is what poisoned the FRESH-REBUILD base
    /// recheck (`solver_tail::fresh_base_recheck` → the disposable encoder):
    /// it survives into `assert_tuple_axioms`, where it pairs with the
    /// non-Int component the later body-phase `__trust_wp_tupleN` ctor
    /// declares. `eq_term` cannot bridge `Int` × `Uninterpreted("List")`, so
    /// `coerce_ite_sorts` replaces the accessor side with a fresh GLOBAL
    /// constant and the projection axiom degenerates to
    /// `forall x0, x1. __trust_wp_coerce_N = x1` — collapsing the whole `List`
    /// sort to one element and making every base/vacuity recheck that carried
    /// it spuriously UNSAT (rusthorn `take_some_rest`, ghost_vec's four
    /// `vacuous proof` obligations). Minting the getter at the arms' sort
    /// removes the pathological pairing at the source: the `Int` variant is
    /// never declared, so no cross-sort projection axiom is ever built.
    ///
    /// Here the match arms ARE the authority on the scrutinee sort: the arms
    /// resolved to a declared datatype (e.g. `Cons`/`Nil` → `List`), so
    /// pre-declare the signature-keyed getter placeholder over the receiver's
    /// opaque `Uninterpreted("TupleN")` carrier with that datatype return sort
    /// before the scrutinee is encoded. The mint then resolves it via
    /// `existing_placeholder_return_sort` (non-Int preferred).
    ///
    /// Soundness: declares a UF symbol with a refined sort — no assertions.
    /// Conservative guards mirror the 87b48b9 seams: single-receiver getters,
    /// receiver term carrying the opaque `Uninterpreted("TupleN")` sort only,
    /// non-LogicFnCall receivers (ctor-application receivers keep their
    /// existing routes), and only when the family has no non-Int variant yet.
    fn preseed_tuple_getter_placeholder_for_match_scrutinee(
        &mut self,
        scrutinee: &PureExpr,
        datatype: Option<&DatatypeSort>,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) {
        let Some(datatype) = datatype else {
            return;
        };
        let Some((getter_name, getter_args)) = self.peel_tuple_getter_call(scrutinee) else {
            return;
        };
        let Some(index) =
            trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_index(
                getter_name,
            )
        else {
            return;
        };
        let [receiver] = getter_args else {
            return;
        };
        // Constructor-application receivers (`get_I(tupleN(..))`) already have
        // exact routes (ctor-domain derivation / component inference).
        if matches!(receiver, PureExpr::LogicFnCall { .. }) {
            return;
        }
        let receiver = receiver.clone();
        // Sort INFERENCE (never encoding) — mirrors the 87b48b9 callee-domain
        // seam. Encoding the receiver here to read its term sort would double
        // the side effects of any non-trivial receiver.
        let receiver_sort = self.infer_expr_sort_with_context(&receiver, prefix);
        let Sort::Uninterpreted(carrier) = &receiver_sort else {
            return;
        };
        if carrier
            .strip_prefix("Tuple")
            .and_then(|arity| arity.parse::<usize>().ok())
            .is_none()
        {
            return;
        }
        let getter_smt = trust_wp_core::logic::logic_fn_smt_name(getter_name);
        let param_sorts = std::slice::from_ref(&receiver_sort);
        if self
            .existing_placeholder_return_sort(&getter_smt, param_sorts)
            .is_some_and(|sort| sort != Sort::Int)
        {
            return;
        }
        // Prefer the ctor-domain derivation whenever a `__trust_wp_tupleN`
        // constructor is already declared: `placeholder_return_sort` consults
        // that arm BEFORE `existing_placeholder_return_sort`, so preseeding a
        // different FLAVOR of the same term sort here (`Datatype("List")` vs
        // the ctor domain's `Uninterpreted("List")`) would fragment the getter
        // into two distinct symbols over one solver signature instead of
        // unifying the family.
        let return_sort = self
            .tuple_getter_return_sort_from_ctor_domain(index, param_sorts)
            .unwrap_or_else(|| Sort::Datatype(datatype.clone()));
        let decl_key = Self::placeholder_smt_name(&getter_smt, param_sorts, &return_sort);
        debug!(
            "[match-scrutinee-preseed] getter={getter_smt} carrier={carrier} \
             return_sort={return_sort:?} (#getters2)"
        );
        self.get_or_declare_logic_func(&decl_key, param_sorts, return_sort);
    }

    /// #prophecy-slots (Fix B M2): declare the specialized carrier `Option`
    /// family named by the scrutinee's own annotation, if it has one.
    ///
    /// Narrow by construction: only names minted by
    /// `mutref_instantiated_option_name` parse, and only their declared
    /// payload sort is used. Non-`Option` and non-instantiated annotations
    /// return without touching the registry, so the passing corpus sees no
    /// new declarations.
    fn ensure_instantiated_option_family_for_scrutinee(&mut self, scrutinee: &PureExpr) {
        let Some(annotation) =
            crate::encoder::sort_context::extract_inner_var_annotation(scrutinee)
        else {
            return;
        };
        let ExprSort::Datatype(id) = annotation else {
            return;
        };
        let name = trust_wp_core::formula::resolve_sort_name(*id);
        if crate::encoder::sort_context::sort_mapping::parse_mutref_instantiated_option(&name)
            .is_none()
        {
            return;
        }
        // `sort_from_expr_sort` owns the declaration (and the payload's own
        // recursive resolution); its return value is discarded here — this is
        // a declare-before-use step, not a sort query.
        let _ = self.sort_from_expr_sort(annotation.clone());
    }

    fn encode_match_arm_body(
        &mut self,
        scrutinee: Term,
        arm: &MatchArm,
        datatype: Option<&DatatypeSort>,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
        synthesize_branch_facts: bool,
    ) -> Result<Term, EncodingError> {
        let scrutinee_sort = datatype.map(|dt| Sort::Datatype(dt.clone()));
        let preseeded_sorts = self.preseed_match_arm_binding_sorts(arm, prefix);
        let bindings = match self.pattern_bindings(
            scrutinee,
            &arm.pattern,
            datatype,
            scrutinee_sort.as_ref(),
            prefix,
        ) {
            Ok(bindings) => bindings,
            Err(err) => {
                self.restore_match_arm_binding_sorts(preseeded_sorts);
                return Err(err);
            }
        };
        if bindings.is_empty() {
            if synthesize_branch_facts {
                // Selected-arm lowering is the first point where a branch-specific
                // postcondition is known to be active. Only seed seq bridges in
                // that mode; normal match ITE encoding must not let inactive arms
                // mutate global sequence facts.
                self.try_synthesize_len_zero_seq_value(&arm.body, prefix)?;
                self.try_synthesize_index_mut_seq_value(&arm.body, prefix)?;
            }
            let body_result = self.encode_pure_impl(&arm.body, prefix);
            self.restore_match_arm_binding_sorts(preseeded_sorts);
            return body_result;
        }

        let mut old_bindings = Vec::new();
        for (name, term, sort) in &bindings {
            let old_term = self.insert_var(name.clone(), *term);
            let old_sort = self.insert_var_sort(name.clone(), sort.clone());
            old_bindings.push((name.clone(), old_term, old_sort));
            // Match-arm pattern binders are pure logical values scoped to this
            // arm, exactly like logic-function formal parameters. Mark them as
            // binder-scoped so wrapper/view encodings (`a@`, `old(a)`, `*a`,
            // `^a`) collapse to the bound payload-projection term instead of
            // synthesizing a GLOBAL derived constant (`a_view`, `old_a`, ...).
            // A global `a_view` is shared across every instantiation of the
            // same match body (e.g. the one-level unfolds of a recursive
            // #[logic] fn at self / ^self / subtree scrutinees), asserting that
            // all those distinct payloads are EQUAL — an unsound assumption set
            // (binder-scoped view collapse; #1635 analog for match arms).
            self.bind_quantifier_var(name.clone());
            // Fix A (Final-collapse audit): additionally mark the binder as a
            // MATCH binder. The Phase-1 Final-collapse guard fires only for
            // match binders — their bound term is a destructor payload with
            // no prophecy slot, so `^v` collapsing onto it would assert
            // `^v == *v`. Logic-fn formals / genuine quantifier binders keep
            // the legacy collapse (driver-split lane).
            self.bind_match_binder_var(name.clone());
        }
        // The wrapper-collapse fast paths test `is_quantifier_bound` with the
        // RAW source name and then resolve the term under the prefixed name.
        // When a derived-name prefix is active, the bindings above were
        // inserted under prefixed names only, so additionally mark the raw
        // pattern names that have a prefixed binding in scope.
        let mut raw_binder_names: Vec<String> = Vec::new();
        if prefix.is_some() {
            let inserted: std::collections::HashSet<&str> =
                bindings.iter().map(|(name, _, _)| name.as_str()).collect();
            for raw in arm.pattern.bound_names() {
                if inserted.contains(apply_name_prefix(raw, prefix).as_ref()) {
                    self.bind_quantifier_var(raw.to_string());
                    self.bind_match_binder_var(raw.to_string());
                    raw_binder_names.push(raw.to_string());
                }
            }
        }

        let bound_names: std::collections::HashSet<&str> =
            bindings.iter().map(|(name, _, _)| name.as_str()).collect();
        // #prophecy-slots (Fix B M4): the binders whose bound TERM is a real
        // prophecy carrier. This is the term-level authority the rewriter's
        // own annotation test cannot reach (contract-parsed pattern binders
        // arrive unannotated), and it is what stops `*r` from being stripped
        // to the whole `(current, final, id)` record. Empty before M1/M2 made
        // any binder carrier-sorted, so the legacy lane is byte-identical.
        let carrier_binders: std::collections::HashSet<&str> = bindings
            .iter()
            .filter(|(_, term, _)| self.is_mut_ref_sorted(*term))
            .map(|(name, _, _)| name.as_str())
            .collect();
        let rewritten_body =
            collapse_deref_for_bound_vars(&arm.body, &bound_names, &carrier_binders);

        // No `?` between bind/insert and the restore loops below: an early
        // return would leak the binder-scope marks and var bindings.
        let body_result = (|| {
            if synthesize_branch_facts {
                self.try_synthesize_len_zero_seq_value(&rewritten_body, prefix)?;
                self.try_synthesize_index_mut_seq_value(&rewritten_body, prefix)?;
            }
            self.encode_pure_impl(&rewritten_body, prefix)
        })();

        for raw in raw_binder_names.iter().rev() {
            self.unbind_match_binder_var(raw);
            self.unbind_quantifier_var(raw);
        }
        for (name, old_term, old_sort) in old_bindings {
            self.unbind_match_binder_var(&name);
            self.unbind_quantifier_var(&name);
            self.restore_var(&name, old_term);
            self.restore_var_sort(&name, old_sort);
        }
        self.restore_match_arm_binding_sorts(preseeded_sorts);

        body_result
    }

    fn preseed_match_arm_binding_sorts(
        &mut self,
        arm: &MatchArm,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Vec<(String, Option<Sort>)> {
        let bound_names = arm.pattern.bound_names();
        if bound_names.is_empty() {
            return Vec::new();
        }

        let planned = crate::encoder::sort_context::preseed::collect_declared_fn_domain_sorts_batch(
            self.decls(),
            &[&arm.body],
        );
        if planned.is_empty() {
            return Vec::new();
        }

        let mut old_sorts = Vec::new();
        for bound_name in bound_names {
            let scoped_name = apply_name_prefix(bound_name, prefix).into_owned();
            let Some(sort) = planned
                .get(bound_name)
                .or_else(|| planned.get(scoped_name.as_str()))
                .cloned()
            else {
                continue;
            };
            if sort == Sort::Int {
                continue;
            }
            let should_insert = self.var_sort(&scoped_name).is_none_or(|existing| {
                match_arm_binding_sort_specificity(&sort)
                    > match_arm_binding_sort_specificity(existing)
            });
            if should_insert {
                let old_sort = self.insert_var_sort(scoped_name.clone(), sort);
                old_sorts.push((scoped_name, old_sort));
            }
        }
        old_sorts
    }

    fn restore_match_arm_binding_sorts(&mut self, old_sorts: Vec<(String, Option<Sort>)>) {
        for (name, old_sort) in old_sorts.into_iter().rev() {
            self.restore_var_sort(&name, old_sort);
        }
    }

    /// Encode one selected match arm body without encoding sibling arms.
    ///
    /// This is used by obligation slicing when a slice-local antecedent proves
    /// which return-body match arm is active. It preserves the normal match
    /// arm binding behavior for variables introduced by the selected pattern,
    /// but avoids constructing branch bodies that are irrelevant to that slice.
    pub(crate) fn encode_selected_match_arm_body(
        &mut self,
        scrutinee: &PureExpr,
        arms: &[MatchArm],
        arm_index: usize,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        let Some(arm) = arms.get(arm_index) else {
            return Err(EncodingError::unsupported(format!(
                "selected match arm index {arm_index} out of range for {} arms",
                arms.len()
            )));
        };

        self.ensure_instantiated_option_family_for_scrutinee(scrutinee);
        let mut datatype = self.match_datatype(scrutinee, arms, prefix);
        if let Some(ref dt) = datatype {
            if self.scrutinee_has_conflicting_sort(scrutinee, dt, prefix) {
                datatype = self.scrutinee_existing_datatype(scrutinee, prefix);
            }
        }
        if let Some(dt) = datatype.take() {
            self.ensure_datatype_declared(&dt);
            datatype = Some(self.canonical_declared_datatype(&dt));
        }
        let scrutinee_term = self.encode_match_scrutinee(scrutinee, datatype.as_ref(), prefix)?;

        if let Some(dt) = datatype.as_ref() {
            self.assert_ground_field_range_constraints(scrutinee_term, dt);
        }

        self.encode_match_arm_body(scrutinee_term, arm, datatype.as_ref(), prefix, true)
    }

    pub(crate) fn encode_match_arm_active_guards(
        &mut self,
        scrutinee: &PureExpr,
        arms: &[MatchArm],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Vec<Term>, EncodingError> {
        // #prophecy-slots (Fix B M2): the third match-datatype election site;
        // same declare-before-election step as `encode_match_impl`, so an
        // arm's ACTIVE GUARD is computed against the same family its BODY is.
        self.ensure_instantiated_option_family_for_scrutinee(scrutinee);
        let mut datatype = self.match_datatype(scrutinee, arms, prefix);
        if let Some(ref dt) = datatype {
            if self.scrutinee_has_conflicting_sort(scrutinee, dt, prefix) {
                datatype = self.scrutinee_existing_datatype(scrutinee, prefix);
            }
        }
        if let Some(dt) = datatype.take() {
            self.ensure_datatype_declared(&dt);
            datatype = Some(self.canonical_declared_datatype(&dt));
        }
        let scrutinee_term = self.encode_match_scrutinee(scrutinee, datatype.as_ref(), prefix)?;

        let mut guards = Vec::with_capacity(arms.len());
        let mut prior_arms_false: Option<Term> = None;
        for arm in arms {
            let condition = self.encode_pattern_condition_impl(
                scrutinee_term,
                &arm.pattern,
                datatype.as_ref(),
                prefix,
            )?;
            let active = match prior_arms_false.clone() {
                Some(prior_false) => self.solver.and(prior_false, condition.clone()),
                None => condition.clone(),
            };
            guards.push(active);

            let not_condition = self.solver.not(condition);
            prior_arms_false = Some(match prior_arms_false {
                Some(prior_false) => self.solver.and(prior_false, not_condition),
                None => not_condition,
            });
        }

        Ok(guards)
    }

    pub(crate) fn constructor_payload_selector<'a>(
        datatype: &'a DatatypeSort,
        constructor_name: &str,
    ) -> Option<(&'a str, &'a Sort)> {
        let ctor = datatype
            .constructors
            .iter()
            .find(|ctor| datatype_constructor_matches(datatype, &ctor.name, constructor_name))?;
        if ctor.fields.len() != 1 {
            return None;
        }
        let field = ctor.fields.first()?;
        Some((field.name.as_str(), &field.sort))
    }

    /// Look up all field selectors for a multi-field constructor.
    ///
    /// Returns `Some(fields)` when the constructor has 2+ fields, allowing
    /// per-field native datatype selectors. Returns `None` for single-field
    /// constructors (handled by `constructor_payload_selector`) and nullary
    /// constructors. (#1965, #2002)
    pub(crate) fn constructor_multi_field_selectors<'a>(
        datatype: &'a DatatypeSort,
        constructor_name: &str,
    ) -> Option<&'a [ay_dpll::api::DatatypeField]> {
        let ctor = datatype
            .constructors
            .iter()
            .find(|ctor| datatype_constructor_matches(datatype, &ctor.name, constructor_name))?;
        if ctor.fields.len() < 2 {
            return None;
        }
        Some(&ctor.fields)
    }
}

fn synthesized_enum_alias_name(decl: &AdtDecl) -> Option<String> {
    if decl.kind != AdtKind::Enum || decl.adt_name.starts_with("Adt_") {
        return None;
    }

    let mut names: Vec<&str> = decl
        .constructors
        .iter()
        .map(|ctor| short_constructor_name(&ctor.smt_name))
        .collect();
    if names.is_empty() {
        return None;
    }

    names.sort_unstable();
    let synthesized = format!("Adt_{}", names.join("_"));
    (synthesized != decl.adt_name).then_some(synthesized)
}

fn match_arm_binding_sort_specificity(sort: &Sort) -> u8 {
    match sort {
        Sort::Int => 0,
        Sort::Bool => 1,
        Sort::Seq(_) => 2,
        Sort::Uninterpreted(name) if name == "FMap" => 3,
        Sort::Datatype(_) | Sort::Uninterpreted(_) => 4,
        _ => 2,
    }
}

fn selector_sort_tag(sort: &Sort) -> String {
    let mut encoded = String::new();
    for byte in sort.as_term_sort().to_string().as_bytes() {
        let _ = std::fmt::Write::write_fmt(&mut encoded, format_args!("{byte:02x}"));
    }
    encoded
}
