// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! View (`@`) encoding helpers.
//!
//! Handles scalar identity semantics, Seq-view variable declaration,
//! and quantifier-bound variable collapse for `PureExpr::View`.

use std::{collections::HashMap, sync::Arc};

use ay_dpll::api::{Sort, Term};
use tracing::debug;
use trust_wp_core::{
    formula::{
        intern_sort_name,
        internal::tuple_lowering::{
            tuple_logic_fn_arity, NAMED_FIELD_LOGIC_FN_PREFIX, TUPLE_FIELD_LOGIC_FN_PREFIX,
        },
        resolve_sort_name, ExprSort, MatchArm, PureExpr,
    },
    logic::{AdtDecl, AdtKind, LogicFnDef, LogicMode},
};

use super::{
    logic_fn::transparent_adapter_inner,
    sort_context::{
        apply_name_prefix, effective_expr_annotation, is_seq_family_sort,
        reference_like_inner_sort, resolve_nameable_expr, resolve_registered_non_int_sort,
        same_structural_family, DerivedKind,
    },
    type_resolve::resolve_qualified_int_constant,
    AYEncoder, DirectViewFn, ViewReturnFn,
};
use crate::error::EncodingError;

/// Stable string key for a ay Sort, used for polymorphic UF naming.
fn sort_display_key(sort: &Sort) -> String {
    match sort {
        Sort::Int => "Int".to_string(),
        Sort::Bool => "Bool".to_string(),
        Sort::Uninterpreted(name) => name.replace("::", "_"),
        Sort::Datatype(dt) => dt.name.replace("::", "_"),
        other => format!("{other:?}"),
    }
}

fn wrapped_var_name(expr: &PureExpr) -> Option<&str> {
    match expr {
        PureExpr::Var(name, _) => Some(name.as_str()),
        PureExpr::Deref(inner) | PureExpr::Final(inner) | PureExpr::Old(inner) => {
            wrapped_var_name(inner)
        }
        _ => None,
    }
}

fn expr_annotation_is_predcell_slice(expr: &PureExpr) -> bool {
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

    receiver_annotation(expr).is_some_and(expr_sort_is_predcell_slice)
}

fn indexed_predcell_slice_view_parts(inner: &PureExpr) -> Option<(&PureExpr, &PureExpr)> {
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = inner
    else {
        return None;
    };
    if !matches!(method.as_str(), "index" | "index_logic") || args.len() != 1 {
        return None;
    }
    if !expr_annotation_is_predcell_slice(receiver) {
        return None;
    }
    Some((receiver.as_ref(), &args[0]))
}

fn datatype_sort_name(sort: &ExprSort) -> Option<String> {
    match sort {
        ExprSort::Datatype(id) => Some(resolve_sort_name(*id)),
        ExprSort::Ref(inner) | ExprSort::MutRef(inner) => datatype_sort_name(inner),
        _ => None,
    }
}

fn is_hash_map_iterator_sort_name(name: &str) -> bool {
    matches!(
        name,
        "std::collections::hash_map::IntoIter"
            | "std::collections::hash_map::Iter"
            | "std::collections::hash_map::IterMut"
            | "std::collections::hash::map::IntoIter"
            | "std::collections::hash::map::Iter"
            | "std::collections::hash::map::IterMut"
    )
}

fn is_hash_set_iterator_sort_name(name: &str) -> bool {
    matches!(
        name,
        "Intersection"
            | "Difference"
            | "std::collections::hash_set::IntoIter"
            | "std::collections::hash_set::Iter"
            | "std::collections::hash_set::Intersection"
            | "std::collections::hash_set::Difference"
            | "std::collections::hash::set::IntoIter"
            | "std::collections::hash::set::Iter"
            | "std::collections::hash::set::Intersection"
            | "std::collections::hash::set::Difference"
    )
}

fn collection_iterator_view_return_sort(inner: &PureExpr) -> Option<Sort> {
    let annotation = effective_expr_annotation(inner)?;
    let sort_name = datatype_sort_name(annotation)?;
    if is_hash_map_iterator_sort_name(&sort_name) {
        return Some(Sort::Uninterpreted("FMap".to_string()));
    }
    if is_hash_set_iterator_sort_name(&sort_name) {
        return Some(Sort::Int);
    }
    None
}

pub(in crate::encoder) fn is_direct_view_candidate(
    logic_fn: &LogicFnDef,
    _effective_mode: LogicMode,
) -> bool {
    if logic_fn.name() != "view"
        || logic_fn.params().len() != 1
        || !logic_fn.requires().is_empty()
        || logic_fn.is_opaque()
    {
        return false;
    }

    let param = &logic_fn.params()[0];
    if !crate::expr::expr_mentions_var(logic_fn.body(), param) {
        return false;
    }

    !matches!(logic_fn.body(), PureExpr::Var(name, _) if name == param)
        && !matches!(
            logic_fn.body(),
            PureExpr::View(inner)
                if matches!(inner.as_ref(), PureExpr::Var(name, _) if name == param)
        )
}

fn is_first_field_projection(expr: &PureExpr) -> bool {
    let PureExpr::LogicFnCall { name, args } = expr else {
        return false;
    };
    if args.len() != 1 {
        return false;
    }
    name.strip_prefix(TUPLE_FIELD_LOGIC_FN_PREFIX)
        .is_some_and(|suffix| suffix.parse::<usize>().ok() == Some(0))
}

fn final_tuple_projection_root_view(
    inner_final: &PureExpr,
    _prefix: Option<DerivedKind>,
) -> Option<PureExpr> {
    let mut final_depth = 1usize;
    let mut base = inner_final;
    while let PureExpr::Final(next) = base {
        final_depth += 1;
        base = next;
    }

    let PureExpr::LogicFnCall { name, args } = base else {
        return None;
    };
    if !name.starts_with(TUPLE_FIELD_LOGIC_FN_PREFIX) || args.len() != 1 {
        return None;
    }

    let root = &args[0];
    let mut final_root_name = resolve_nameable_expr(root, None)?;
    for _ in 0..final_depth {
        final_root_name = DerivedKind::Final.format_name(&final_root_name);
    }
    let annotation = match root {
        PureExpr::Var(_, ann) => ann.clone(),
        _ => None,
    };

    Some(PureExpr::LogicFnCall {
        name: name.clone(),
        args: vec![PureExpr::Var(final_root_name, annotation)],
    })
}

fn strip_generic_args(path: &str) -> String {
    let mut stripped = String::new();
    let mut depth = 0usize;
    for ch in path.chars() {
        match ch {
            '<' => depth += 1,
            '>' if depth > 0 => depth -= 1,
            _ if depth == 0 => stripped.push(ch),
            _ => {}
        }
    }
    stripped.trim().trim_matches('>').to_string()
}

fn push_direct_view_owner_candidate(out: &mut Vec<String>, candidate: &str) {
    let normalized = strip_generic_args(candidate);
    if normalized.is_empty() {
        return;
    }
    if !out.iter().any(|existing| existing == &normalized) {
        out.push(normalized.clone());
    }
    let bare = normalized.rsplit("::").next().unwrap_or(&normalized);
    if !bare.is_empty() && !out.iter().any(|existing| existing == bare) {
        out.push(bare.to_string());
    }
}

fn direct_view_owner_type_candidates(full_path: &str) -> Vec<String> {
    let owner = full_path.strip_suffix("::view").unwrap_or(full_path);
    let mut candidates = Vec::new();
    push_direct_view_owner_candidate(&mut candidates, owner);

    if let Some((before_trait, _)) = owner.rsplit_once(" as ") {
        if let Some((_, impl_self)) = before_trait.rsplit_once("::<") {
            push_direct_view_owner_candidate(&mut candidates, impl_self);
        } else if let Some((_, impl_self)) = before_trait.rsplit_once('<') {
            push_direct_view_owner_candidate(&mut candidates, impl_self);
        }
    }

    candidates
}

fn expr_sorts_match_for_direct_view(expected: &ExprSort, actual: &ExprSort) -> bool {
    if expected == actual {
        return true;
    }
    match (expected, actual) {
        (ExprSort::Datatype(expected_id), ExprSort::Datatype(actual_id)) => {
            let expected_name = resolve_sort_name(*expected_id);
            let actual_name = resolve_sort_name(*actual_id);
            expected_name == actual_name
                || expected_name.rsplit("::").next() == actual_name.rsplit("::").next()
        }
        _ => false,
    }
}

fn ay_sorts_match_for_direct_view(expected: &Sort, actual: &Sort) -> bool {
    expected == actual || same_structural_family(expected, actual).is_some()
}

fn direct_view_owner_matches_expr_sort(full_path: &str, sort: &ExprSort) -> bool {
    let ExprSort::Datatype(sort_id) = sort else {
        return false;
    };
    let sort_name = resolve_sort_name(*sort_id);
    let short_name = sort_name.rsplit("::").next().unwrap_or(&sort_name);
    direct_view_owner_type_candidates(full_path)
        .iter()
        .any(|owner| owner == &sort_name || owner == short_name)
}

fn direct_view_owner_matches_ay_sort(full_path: &str, sort: &Sort) -> bool {
    let sort_name = match sort {
        Sort::Uninterpreted(name) => name.as_str(),
        Sort::Datatype(dt) => dt.name.as_str(),
        _ => return false,
    };
    let short_name = sort_name.rsplit("::").next().unwrap_or(sort_name);
    direct_view_owner_type_candidates(full_path)
        .iter()
        .any(|owner| owner == sort_name || owner == short_name)
}

impl AYEncoder {
    pub(crate) fn register_view_return_sort_if_supported(&mut self, logic_fn: &LogicFnDef) -> bool {
        let Some(return_sort) = logic_fn.return_sort() else {
            return false;
        };
        if logic_fn.name() != "view" || logic_fn.params().len() != 1 {
            return false;
        }
        let return_sort = self.sort_from_expr_sort(return_sort);

        if self
            .view_return_fns
            .iter()
            .any(|existing| existing.full_path == logic_fn.full_path())
        {
            return true;
        }

        self.view_return_fns.push(ViewReturnFn {
            full_path: logic_fn.full_path().to_string(),
            param_sort: logic_fn.param_sorts().first().cloned().flatten(),
            return_sort,
        });
        true
    }

    pub(crate) fn register_direct_view_fn_if_supported(
        &mut self,
        logic_fn: &LogicFnDef,
        effective_mode: LogicMode,
    ) -> bool {
        if !is_direct_view_candidate(logic_fn, effective_mode) {
            return false;
        }

        if self
            .direct_view_fns
            .iter()
            .any(|existing| existing.full_path == logic_fn.full_path())
        {
            return true;
        }

        self.direct_view_fns.push(DirectViewFn {
            full_path: logic_fn.full_path().to_string(),
            param: logic_fn.params()[0].clone(),
            param_sort: logic_fn.param_sorts().first().cloned().flatten(),
            body: logic_fn.body().clone(),
        });
        true
    }

    fn select_direct_view_fn(
        &mut self,
        inner: &PureExpr,
        prefix: Option<DerivedKind>,
    ) -> Option<DirectViewFn> {
        if self.direct_view_fns.is_empty() {
            return None;
        }

        let candidates = self.direct_view_fns.clone();
        let candidates: Vec<DirectViewFn> = candidates
            .into_iter()
            .filter(|candidate| self.direct_view_candidate_matches_inner(candidate, inner, prefix))
            .collect();

        (candidates.len() == 1).then(|| candidates[0].clone())
    }

    fn direct_view_struct_decl(&self, candidate: &DirectViewFn) -> Option<&AdtDecl> {
        if let Some(ExprSort::Datatype(sort_id)) = candidate.param_sort.as_ref() {
            let sort_name = resolve_sort_name(*sort_id);
            let short_name = sort_name.rsplit("::").next().unwrap_or(&sort_name);
            if let Some(decl) = self
                .adt_decl_for_name(&sort_name)
                .or_else(|| self.adt_decl_for_name(short_name))
            {
                return Some(decl);
            }
        }

        for owner in direct_view_owner_type_candidates(&candidate.full_path) {
            if let Some(decl) = self.adt_decl_for_name(&owner) {
                return Some(decl);
            }
        }

        None
    }

    fn view_return_struct_decl(&self, candidate: &ViewReturnFn) -> Option<&AdtDecl> {
        if let Some(ExprSort::Datatype(sort_id)) = candidate.param_sort.as_ref() {
            let sort_name = resolve_sort_name(*sort_id);
            let short_name = sort_name.rsplit("::").next().unwrap_or(&sort_name);
            if let Some(decl) = self
                .adt_decl_for_name(&sort_name)
                .or_else(|| self.adt_decl_for_name(short_name))
            {
                return Some(decl);
            }
        }

        for owner in direct_view_owner_type_candidates(&candidate.full_path) {
            if let Some(decl) = self.adt_decl_for_name(&owner) {
                return Some(decl);
            }
        }

        None
    }

    fn direct_view_candidate_param_sort(&self, candidate: &DirectViewFn) -> Option<ExprSort> {
        candidate.param_sort.clone().or_else(|| {
            self.direct_view_struct_decl(candidate)
                .map(|decl| ExprSort::Datatype(intern_sort_name(&decl.adt_name)))
        })
    }

    fn view_return_candidate_param_sort(&self, candidate: &ViewReturnFn) -> Option<ExprSort> {
        candidate.param_sort.clone().or_else(|| {
            self.view_return_struct_decl(candidate)
                .map(|decl| ExprSort::Datatype(intern_sort_name(&decl.adt_name)))
        })
    }

    fn direct_view_candidate_matches_inner(
        &mut self,
        candidate: &DirectViewFn,
        inner: &PureExpr,
        prefix: Option<DerivedKind>,
    ) -> bool {
        let Some(expected) = self.direct_view_candidate_param_sort(candidate) else {
            return true;
        };

        if let Some(actual) = effective_expr_annotation(inner) {
            return expr_sorts_match_for_direct_view(&expected, actual);
        }

        if self.direct_view_constructor_arity_matches(candidate, inner) {
            return true;
        }

        let Some(inner_name) = resolve_nameable_expr(inner, prefix) else {
            return false;
        };
        let Some(actual_sort) = self.var_sort(&inner_name).cloned() else {
            return false;
        };
        let expected_sort = self.sort_from_expr_sort(expected);
        ay_sorts_match_for_direct_view(&expected_sort, &actual_sort)
    }

    fn direct_view_constructor_arity_matches(
        &self,
        candidate: &DirectViewFn,
        inner: &PureExpr,
    ) -> bool {
        let PureExpr::LogicFnCall { name, args } = inner else {
            return false;
        };
        if tuple_logic_fn_arity(name) != Some(args.len()) {
            return false;
        }
        self.direct_view_struct_decl(candidate)
            .and_then(|decl| decl.constructors.first())
            .is_some_and(|ctor| ctor.fields.len() == args.len())
    }

    fn view_return_candidate_matches_inner(
        &mut self,
        candidate: &ViewReturnFn,
        inner: &PureExpr,
        prefix: Option<DerivedKind>,
    ) -> bool {
        let Some(expected) = self.view_return_candidate_param_sort(candidate) else {
            return false;
        };

        if let Some(actual) = effective_expr_annotation(inner) {
            if direct_view_owner_matches_expr_sort(&candidate.full_path, actual) {
                return true;
            }
            return expr_sorts_match_for_direct_view(&expected, actual);
        }

        if self.view_return_constructor_arity_matches(candidate, inner) {
            return true;
        }

        let Some(inner_name) = resolve_nameable_expr(inner, prefix) else {
            return false;
        };
        let Some(actual_sort) = self.var_sort(&inner_name).cloned() else {
            return false;
        };
        if direct_view_owner_matches_ay_sort(&candidate.full_path, &actual_sort) {
            return true;
        }
        if matches!(expected, ExprSort::TypeParam(_)) {
            return false;
        }
        let expected_sort = self.sort_from_expr_sort(expected);
        ay_sorts_match_for_direct_view(&expected_sort, &actual_sort)
    }

    fn view_return_constructor_arity_matches(
        &self,
        candidate: &ViewReturnFn,
        inner: &PureExpr,
    ) -> bool {
        let PureExpr::LogicFnCall { name, args } = inner else {
            return false;
        };
        if tuple_logic_fn_arity(name) != Some(args.len()) {
            return false;
        }
        self.view_return_struct_decl(candidate)
            .and_then(|decl| decl.constructors.first())
            .is_some_and(|ctor| ctor.fields.len() == args.len())
    }

    fn view_return_sort_for_inner(
        &mut self,
        inner: &PureExpr,
        prefix: Option<DerivedKind>,
    ) -> Option<Sort> {
        if self.view_return_fns.is_empty() {
            return None;
        }

        let candidates = self.view_return_fns.clone();
        let candidates: Vec<ViewReturnFn> = candidates
            .into_iter()
            .filter(|candidate| self.view_return_candidate_matches_inner(candidate, inner, prefix))
            .collect();

        (candidates.len() == 1).then(|| candidates[0].return_sort.clone())
    }

    fn direct_view_struct_field_index(
        &self,
        candidate: &DirectViewFn,
        field_name: &str,
    ) -> Option<usize> {
        let decl = self.direct_view_struct_decl(candidate)?;
        if decl.kind != AdtKind::Struct {
            return None;
        }
        let ctor = decl.constructors.first()?;
        ctor.fields
            .iter()
            .position(|field| field.name == field_name)
    }

    fn direct_view_constructor_field_arg<'a>(
        &self,
        candidate: &DirectViewFn,
        constructor: &'a PureExpr,
        field_name: &str,
    ) -> Option<&'a PureExpr> {
        let field_index = self.direct_view_struct_field_index(candidate, field_name)?;
        let PureExpr::LogicFnCall { name, args } = constructor else {
            return None;
        };
        if tuple_logic_fn_arity(name) != Some(args.len()) {
            return None;
        }
        args.get(field_index)
    }

    fn beta_reduce_direct_view_constructor_fields(
        &self,
        expr: &PureExpr,
        candidate: &DirectViewFn,
        constructor: &PureExpr,
    ) -> PureExpr {
        match expr {
            PureExpr::LogicFnCall { name, args } => {
                if let Some(field_name) = name.strip_prefix(NAMED_FIELD_LOGIC_FN_PREFIX) {
                    if args.len() == 1 && args[0] == *constructor {
                        if let Some(arg) = self.direct_view_constructor_field_arg(
                            candidate,
                            constructor,
                            field_name,
                        ) {
                            return arg.clone();
                        }
                    }
                }
                PureExpr::LogicFnCall {
                    name: name.clone(),
                    args: args
                        .iter()
                        .map(|arg| {
                            self.beta_reduce_direct_view_constructor_fields(
                                arg,
                                candidate,
                                constructor,
                            )
                        })
                        .collect(),
                }
            }
            PureExpr::MethodCall {
                receiver,
                method,
                args,
            } => PureExpr::MethodCall {
                receiver: Arc::new(self.beta_reduce_direct_view_constructor_fields(
                    receiver,
                    candidate,
                    constructor,
                )),
                method: method.clone(),
                args: args
                    .iter()
                    .map(|arg| {
                        self.beta_reduce_direct_view_constructor_fields(arg, candidate, constructor)
                    })
                    .collect(),
            },
            PureExpr::BinOp(left, op, right) => PureExpr::BinOp(
                Arc::new(self.beta_reduce_direct_view_constructor_fields(
                    left,
                    candidate,
                    constructor,
                )),
                *op,
                Arc::new(self.beta_reduce_direct_view_constructor_fields(
                    right,
                    candidate,
                    constructor,
                )),
            ),
            PureExpr::UnOp(op, inner) => PureExpr::UnOp(
                *op,
                Arc::new(self.beta_reduce_direct_view_constructor_fields(
                    inner,
                    candidate,
                    constructor,
                )),
            ),
            PureExpr::Ite(cond, then_expr, else_expr) => PureExpr::Ite(
                Arc::new(self.beta_reduce_direct_view_constructor_fields(
                    cond,
                    candidate,
                    constructor,
                )),
                Arc::new(self.beta_reduce_direct_view_constructor_fields(
                    then_expr,
                    candidate,
                    constructor,
                )),
                Arc::new(self.beta_reduce_direct_view_constructor_fields(
                    else_expr,
                    candidate,
                    constructor,
                )),
            ),
            PureExpr::Old(inner) => PureExpr::Old(Arc::new(
                self.beta_reduce_direct_view_constructor_fields(inner, candidate, constructor),
            )),
            PureExpr::Deref(inner) => PureExpr::Deref(Arc::new(
                self.beta_reduce_direct_view_constructor_fields(inner, candidate, constructor),
            )),
            PureExpr::Final(inner) => PureExpr::Final(Arc::new(
                self.beta_reduce_direct_view_constructor_fields(inner, candidate, constructor),
            )),
            PureExpr::View(inner) => PureExpr::View(Arc::new(
                self.beta_reduce_direct_view_constructor_fields(inner, candidate, constructor),
            )),
            PureExpr::Forall {
                var,
                var_sort,
                body,
                triggers,
            } => PureExpr::Forall {
                var: var.clone(),
                var_sort: var_sort.clone(),
                body: Arc::new(self.beta_reduce_direct_view_constructor_fields(
                    body,
                    candidate,
                    constructor,
                )),
                triggers: triggers
                    .iter()
                    .map(|trigger| {
                        trigger
                            .iter()
                            .map(|expr| {
                                self.beta_reduce_direct_view_constructor_fields(
                                    expr,
                                    candidate,
                                    constructor,
                                )
                            })
                            .collect()
                    })
                    .collect(),
            },
            PureExpr::Exists {
                var,
                var_sort,
                body,
                triggers,
            } => PureExpr::Exists {
                var: var.clone(),
                var_sort: var_sort.clone(),
                body: Arc::new(self.beta_reduce_direct_view_constructor_fields(
                    body,
                    candidate,
                    constructor,
                )),
                triggers: triggers
                    .iter()
                    .map(|trigger| {
                        trigger
                            .iter()
                            .map(|expr| {
                                self.beta_reduce_direct_view_constructor_fields(
                                    expr,
                                    candidate,
                                    constructor,
                                )
                            })
                            .collect()
                    })
                    .collect(),
            },
            PureExpr::Match { scrutinee, arms } => PureExpr::Match {
                scrutinee: Arc::new(self.beta_reduce_direct_view_constructor_fields(
                    scrutinee,
                    candidate,
                    constructor,
                )),
                arms: arms
                    .iter()
                    .map(|arm| MatchArm {
                        pattern: arm.pattern.clone(),
                        body: self.beta_reduce_direct_view_constructor_fields(
                            &arm.body,
                            candidate,
                            constructor,
                        ),
                    })
                    .collect(),
            },
            PureExpr::Let { var, value, body } => PureExpr::Let {
                var: var.clone(),
                value: Arc::new(self.beta_reduce_direct_view_constructor_fields(
                    value,
                    candidate,
                    constructor,
                )),
                body: Arc::new(self.beta_reduce_direct_view_constructor_fields(
                    body,
                    candidate,
                    constructor,
                )),
            },
            PureExpr::LetAssume { assumption, body } => PureExpr::LetAssume {
                assumption: Arc::new(self.beta_reduce_direct_view_constructor_fields(
                    assumption,
                    candidate,
                    constructor,
                )),
                body: Arc::new(self.beta_reduce_direct_view_constructor_fields(
                    body,
                    candidate,
                    constructor,
                )),
            },
            PureExpr::LetObligation { obligation, body } => PureExpr::LetObligation {
                obligation: Arc::new(self.beta_reduce_direct_view_constructor_fields(
                    obligation,
                    candidate,
                    constructor,
                )),
                body: Arc::new(self.beta_reduce_direct_view_constructor_fields(
                    body,
                    candidate,
                    constructor,
                )),
            },
            PureExpr::Closure { params, body } => PureExpr::Closure {
                params: params.clone(),
                body: Arc::new(self.beta_reduce_direct_view_constructor_fields(
                    body,
                    candidate,
                    constructor,
                )),
            },
            PureExpr::Bool(_) | PureExpr::Int(_) | PureExpr::Float(_) | PureExpr::Var(_, _) => {
                expr.clone()
            }
            #[allow(unreachable_patterns)]
            _ => expr.clone(),
        }
    }

    fn try_encode_direct_view_body(
        &mut self,
        inner: &PureExpr,
        prefix: Option<DerivedKind>,
    ) -> Result<Option<Term>, EncodingError> {
        let Some(candidate) = self.select_direct_view_fn(inner, prefix) else {
            return Ok(None);
        };

        let substitution_inner = match inner {
            PureExpr::Var(name, _) => self
                .var_expr_alias(name)
                .cloned()
                .unwrap_or_else(|| inner.clone()),
            _ => inner.clone(),
        };
        let mut substitutions = HashMap::new();
        substitutions.insert(candidate.param.clone(), substitution_inner.clone());
        let instantiated = candidate.body.substitute(&substitutions);
        let instantiated = self.beta_reduce_direct_view_constructor_fields(
            &instantiated,
            &candidate,
            &substitution_inner,
        );
        if matches!(
            &instantiated,
            PureExpr::View(view_inner) if view_inner.as_ref() == &substitution_inner
        ) {
            return Ok(None);
        }

        if is_first_field_projection(&instantiated) {
            let seq_sort = self.get_seq_sort();
            let projection = self.encode_structural_receiver_with_expected_sort(
                &instantiated,
                &seq_sort,
                prefix,
            )?;
            let projection_sort = self.solver.get_sort(projection);
            if is_seq_family_sort(&projection_sort) {
                debug!(
                    view_fn = %candidate.full_path,
                    ?projection_sort,
                    "encoded direct Seq view body through structural projection fallback"
                );
                return Ok(Some(projection));
            }
        }

        let term = self.encode_pure_impl(&instantiated, prefix)?;
        let sort = self.solver.get_sort(term);
        if is_seq_family_sort(&sort) {
            debug!(
                view_fn = %candidate.full_path,
                ?sort,
                "encoded direct Seq view body for @ expression"
            );
            Ok(Some(term))
        } else {
            debug!(
                view_fn = %candidate.full_path,
                ?sort,
                "direct view body did not encode as Seq; falling back to view variable"
            );
            Ok(None)
        }
    }

    pub(super) fn encode_view_expr(
        &mut self,
        inner: &PureExpr,
        prefix: Option<DerivedKind>,
    ) -> Result<Term, EncodingError> {
        // `@` is idempotent on already-viewed expressions. Without this collapse,
        // collection specs like `collect` can synthesize nested views (`xs@@`)
        // that become fresh placeholder terms instead of reusing the original
        // logical collection view. (#2116)
        if let PureExpr::View(nested_inner) = inner {
            return self.encode_view_expr(nested_inner, prefix);
        }

        // Bound logic parameters are pure values. Temporal wrappers around them
        // must collapse before `View(Final(param))` synthesizes
        // `param_final`/`final_param_view` placeholders in the caller scope.
        if collection_iterator_view_return_sort(inner).is_none() {
            if let Some(name) = wrapped_var_name(inner) {
                if self.is_quantifier_bound(name) {
                    let lookup = apply_name_prefix(name, prefix).into_owned();
                    if let Some(term) = self.var_term(&lookup) {
                        return Ok(term);
                    }
                }
            }
        }

        if effective_expr_annotation(inner).is_some_and(|ann| matches!(ann, ExprSort::MutRef(_))) {
            let derefed = PureExpr::Deref(Arc::new(inner.clone()));
            return self.encode_view_expr(&derefed, prefix);
        }

        // Transparent iterator adapters like `Copied` / `Cloned` should not
        // force a fresh outer view term. Their logical view is the same as the
        // underlying iterator view, so recurse through the adapter wrapper
        // before the generic identity logic sees it.
        if let Some(inner_adapter) = transparent_adapter_inner(inner) {
            return self.encode_pure_impl(inner_adapter, prefix);
        }

        if let Some((receiver, index)) = indexed_predcell_slice_view_parts(inner) {
            let receiver_term = self.encode_pure_impl(receiver, prefix)?;
            let index_term = self.encode_pure_impl(index, prefix)?;
            let receiver_sort = self.solver.get_sort(receiver_term);
            let mapping_sort = Sort::Uninterpreted("Mapping".to_string());
            // Sort-aware UF name to prevent domain sort collision when the
            // PredCellSlice receiver is declared with different sorts across
            // precondition and body encoding paths. (#2316)
            let uf_name = format!(
                "__predcell_slice_elem_view_{}",
                sort_display_key(&receiver_sort)
            );
            let func =
                self.get_or_declare_spec_fn(&uf_name, &[receiver_sort, Sort::Int], mapping_sort);
            return self.safe_apply(&uf_name, &func, &[receiver_term, index_term]);
        }

        // View(Var(name, MutRef(_))) → View(Deref(Var(name, MutRef(_)))) redirect.
        // Viewing a `&mut T` is semantically viewing its current value: `x@` and
        // `(*x)@` must produce the same ay variable (`x_current_view`). Without
        // this, `x@` creates `x_view` (connected to a fresh `x` variable) while
        // `(*x)@` creates `x_current_view` (connected to the actual mut-borrow
        // current value), making `x@ == (*x)@` unprovable. (#2670)
        if let PureExpr::Var(_, Some(ann)) = inner {
            if matches!(ann, ExprSort::MutRef(_)) {
                let derefed = PureExpr::Deref(Arc::new(inner.clone()));
                return self.encode_view_expr(&derefed, prefix);
            }
        }

        // Positive preconditions may establish a source-level alias for a
        // wrapper-derived name such as `Deref(call_80) == tuple_get_0(call_10)`.
        // Use that alias before declaring `<name>_view`; otherwise the view path
        // loses congruence and creates a fresh `call_80_current_view` key.
        if matches!(inner, PureExpr::Deref(_) | PureExpr::Final(_)) {
            if let Some(inner_name) = resolve_nameable_expr(inner, prefix) {
                if let Some(alias) = self.var_expr_alias(&inner_name).cloned() {
                    if alias != *inner {
                        return self.encode_view_expr(&alias, prefix);
                    }
                }
            }
        }

        // View(Var(..)) fast paths: type constants and quantifier-bound collapse.
        if let PureExpr::Var(name, _) = inner {
            // Type-level constant resolution: View(Var("Self::MIN")) => exact encoding.
            // Returns exact symbolic expressions for types wider than i64. (#2315)
            if let Some(value) = self.type_constant_cloned(name.as_str()) {
                return self.encode_pure_impl(&value, prefix);
            }
            if let Some(value) = resolve_qualified_int_constant(name) {
                return self.encode_pure_impl(&value, prefix);
            }
            // Quantifier bound variable: View(Var(v)) collapses to the bound
            // variable itself — @ is identity for bound vars. (#579)
            if self.is_quantifier_bound(name.as_str())
                && collection_iterator_view_return_sort(inner).is_none()
            {
                let lookup = apply_name_prefix(name, prefix).into_owned();
                if let Some(term) = self.var_term(&lookup) {
                    return Ok(term);
                }
            }
        }

        // Special case: View(Final(..)) uses "final_{name}_view" format.
        if let PureExpr::Final(inner_final) = inner {
            if let Some(rewritten) = final_tuple_projection_root_view(inner_final, prefix) {
                return self.encode_pure_impl(&rewritten, prefix);
            }
            if let Some(inner_name) = resolve_nameable_expr(inner_final, prefix) {
                let var_name = DerivedKind::format_chain(
                    &inner_name,
                    &[DerivedKind::FinalPrefix, DerivedKind::View],
                );
                let base = DerivedKind::Final.format_name(&inner_name);
                // Use effective_expr_annotation to peel reference wrappers so
                // View(Final(Var("ma", MutRef(Int)))) uses Int, not MutRef(Int). (#2593)
                //
                // When effective_expr_annotation(inner) returns None, try the
                // inner_final subexpression directly. This handles
                // View(Final(Deref(Var("self.0", MutRef(Int))))) where Final
                // and Deref each try to peel one MutRef layer but there's only
                // one layer to peel. The Deref peeling produces Int, and Final
                // finds Int (not a reference) → None. But the inner_final
                // expression (Deref(Var(...))) correctly resolves to Int. (#2694)
                let effective_ann = effective_expr_annotation(inner)
                    .or_else(|| effective_expr_annotation(inner_final));
                let view_return_sort = collection_iterator_view_return_sort(inner_final)
                    .or_else(|| self.view_return_sort_for_inner(inner_final, prefix));
                let prefer_fallback = view_return_sort.is_some();
                let fallback = view_return_sort.unwrap_or_else(|| match effective_ann {
                    Some(ann) => self.sort_from_expr_sort(ann.clone()),
                    None => self.infer_expr_sort_with_context(inner_final, prefix),
                });
                return self.declare_view_var(&var_name, &base, fallback, prefer_fallback);
            }
        }
        // General case: resolve inner and append _view
        if let Some(inner_name) = resolve_nameable_expr(inner, prefix) {
            if let Some(term) = self.try_encode_direct_view_body(inner, prefix)? {
                return Ok(term);
            }
            let var_name = DerivedKind::View.format_name(&inner_name);
            // Use effective_expr_annotation for proper sort peeling when the
            // inner expression is a wrapper over an annotated variable.
            // Without this, View(Deref(Var("ma", MutRef(Int)))) would declare
            // ma_current_view with __trust_wp_mutref::int instead of Int. (#2593)
            let effective_ann = effective_expr_annotation(inner);
            // Newtype view: the `@` of a single-scalar-field struct IS its
            // field's view — the driver's aggregate collapse (`Self(n)` → `n`,
            // #2004/#2669) rewrites `x.0@` to `x@` on that convention, and MIR
            // body scopes see the param at the scalar sort so it just works.
            // A SPEC-ONLY scope (trait refinement) keeps the ADT annotation,
            // and declaring `x_view` at the opaque carrier sort then feeds a
            // non-numeric term into the comparison, where the numeric-operand
            // coercion replaces it with a fresh unconstrained constant and the
            // #knights_tour goal guard demotes the counterexample — the
            // InvariantRefinementTooStrong e2e red (a genuine refinement
            // failure degraded to unknown). Same disease and same cure as the
            // canonical-Int transparent wrappers in `sort_from_expr_sort`
            // (adtpa): the view of a transparent single-field carrier is the
            // payload's sort.
            let newtype_view_sort = effective_ann.and_then(|ann| {
                let trust_wp_core::formula::ExprSort::Datatype(id) = ann else {
                    return None;
                };
                let name = trust_wp_core::formula::resolve_sort_name(*id);
                let bare = name.rsplit("::").next().unwrap_or(&name);
                let dt = self
                    .get_datatype_decl(&name)
                    .or_else(|| self.get_datatype_decl(bare))?;
                let [ctor] = dt.constructors.as_slice() else {
                    return None;
                };
                let [field] = ctor.fields.as_slice() else {
                    return None;
                };
                matches!(field.sort, Sort::Int | Sort::Bool | Sort::Real)
                    .then(|| field.sort.clone())
            });
            let view_return_sort = collection_iterator_view_return_sort(inner)
                .or_else(|| self.view_return_sort_for_inner(inner, prefix))
                .or(newtype_view_sort);
            let prefer_fallback = view_return_sort.is_some();
            let fallback = view_return_sort.unwrap_or_else(|| match effective_ann {
                Some(ann) => self.sort_from_expr_sort(ann.clone()),
                None => self.infer_expr_sort_with_context(inner, prefix),
            });
            self.declare_view_var(&var_name, &inner_name, fallback, prefer_fallback)
        } else {
            // Complex inner expression (e.g., LogicFnCall, MethodCall, BinOp, Ite).
            let inner_term = self.encode_pure_impl(inner, prefix)?;
            let preserve_set_adapter_view = {
                let inner_debug = format!("{inner:?}");
                inner_debug.contains("Intersection")
                    || inner_debug.contains("Difference")
                    || inner_debug.contains("intersection")
                    || inner_debug.contains("difference")
            };
            if preserve_set_adapter_view {
                let inner_expr = inner.clone();
                let view_term =
                    self.apply_logic_fn("view", &[inner_term], Some(&[inner_expr]), prefix)?;
                let bridge = self.eq_term(view_term, inner_term);
                self.assert_solver_term("set_adapter_view_bridge", bridge);
                return Ok(view_term);
            }
            let inner_sort = self.infer_expr_sort_with_context(inner, prefix);
            // Also check the actual ay sort of the encoded term. Expression-level
            // inference can lag behind the ground truth (e.g., method calls encoded
            // as Int UFs but inferred as Seq/Datatype due to receiver propagation).
            // Applying `view` to an Int/Bool term is always identity — skipping the
            // placeholder avoids domain sort mismatches. (#994, 09_capacity)
            let term_sort = self.solver.get_sort(inner_term);
            // View is identity for scalar sorts (Int, Bool) and for logical
            // collection sorts (Seq, FMap) — these ARE the deep model, so
            // viewing them again is a no-op. Without this, View(seq_empty())
            // creates an opaque UF `logic_fn_view(seq_empty)` that breaks
            // concat left-identity axiom matching in ay-dpll's single-round
            // E-matching. (#2116)
            let is_identity = |s: &Sort| {
                matches!(s, Sort::Int | Sort::Bool)
                    || is_seq_family_sort(s)
                    || matches!(s, Sort::Uninterpreted(ref n) if n == "FMap")
            };
            if !preserve_set_adapter_view && (is_identity(&inner_sort) || is_identity(&term_sort)) {
                Ok(inner_term)
            } else {
                let inner_expr = inner.clone();
                self.apply_logic_fn("view", &[inner_term], Some(&[inner_expr]), prefix)
            }
        }
    }

    /// Resolve sort, declare a `_view` variable, and assert view identity.
    ///
    /// Shared by the `View(Final(..))` and general `View(nameable)` paths.
    fn declare_view_var(
        &mut self,
        var_name: &str,
        base_name: &str,
        fallback: Sort,
        prefer_fallback: bool,
    ) -> Result<Term, EncodingError> {
        let hint = self.sort_hint_cloned(var_name);
        let mut sort = if prefer_fallback {
            fallback
        } else {
            resolve_registered_non_int_sort(self, var_name).unwrap_or_else(|| {
                // When no registered view/base evidence exists yet, fall back to
                // the usual declaration cascade (base sort + local fallback).
                self.resolve_decl_sort(var_name, Some(base_name), fallback)
            })
        };
        // View sort consistency: when the resolved sort is Int (the universal
        // fallback from sort inference) but the base variable has already been
        // declared with a more specific sort (Seq, Datatype, Uninterpreted),
        // inherit the base variable's sort. This prevents view terms from
        // losing Seq/Datatype sort information due to inference fallback,
        // which would cause sort mismatches when the view term is later used
        // in Seq operations or equality comparisons with Datatype-sorted
        // terms. (#2699)
        if sort == Sort::Int && !prefer_fallback {
            if let Some(base_sort) = self.var_sort(base_name).cloned() {
                if base_sort != Sort::Int && base_sort != Sort::Bool {
                    debug!(
                        var = %var_name,
                        base = %base_name,
                        base_sort = ?base_sort,
                        "view sort consistency: inheriting base sort instead of Int (#2699)"
                    );
                    sort = base_sort;
                }
            }
        }
        debug!(var = %var_name, base = %base_name, ?sort, ?hint, "encode_view_expr");
        let is_seq_sort = is_seq_family_sort(&sort);
        let view_term = self.get_or_declare_var(var_name, sort.clone())?;
        let same_as_base = self
            .var_sort(base_name)
            .is_some_and(|base_sort| ay_sorts_match_for_direct_view(&sort, base_sort));
        let should_assert_identity = same_as_base
            || (!prefer_fallback && (matches!(sort, Sort::Int | Sort::Bool) || is_seq_sort));
        if should_assert_identity {
            self.assert_view_identity(base_name, view_term, is_seq_sort, &sort);
        }
        Ok(view_term)
    }

    pub(crate) fn maybe_assert_declared_seq_view_identity(
        &mut self,
        name: &str,
        _term: Term,
        sort: &Sort,
    ) {
        if !is_seq_family_sort(sort) {
            return;
        }

        if let Some((DerivedKind::View, base_name)) = DerivedKind::strip_from(name) {
            if base_name.is_empty() {
                return;
            }
            if self
                .var_sort(base_name)
                .is_some_and(|base_sort| ay_sorts_match_for_direct_view(sort, base_sort))
            {
                if let Some(view_term) = self.var_term(name) {
                    self.assert_view_identity(base_name, view_term, true, sort);
                }
            }
            return;
        }

        let view_name = DerivedKind::View.format_name(name);
        if self
            .var_sort(&view_name)
            .is_some_and(|view_sort| ay_sorts_match_for_direct_view(sort, view_sort))
        {
            if let Some(view_term) = self.var_term(&view_name) {
                self.assert_view_identity(name, view_term, true, sort);
            }
        }
    }

    /// Assert `base = view` identity and propagate SeqValue when applicable.
    ///
    /// For scalar sorts, always asserts identity (@ is a no-op on scalars).
    /// For Seq sorts, only asserts when the base variable is also Seq-sorted,
    /// connecting body Seq results to postcondition view terms. (#359, #1317)
    fn assert_view_identity(
        &mut self,
        base_name: &str,
        view_term: Term,
        is_seq_sort: bool,
        sort: &Sort,
    ) {
        let already_asserted = self.has_view_identity(base_name);
        if already_asserted && !is_seq_sort {
            return;
        }
        let base_sort_matches = if is_seq_sort {
            self.var_sort(base_name).is_none_or(is_seq_family_sort)
        } else {
            true
        };
        if !base_sort_matches {
            return;
        }
        let Ok(base_term) = self.get_or_declare_var(base_name, sort.clone()) else {
            return;
        };
        // The finite ground Seq lane represents equality extensionally through
        // Array+Length+Offset components. Emitting the redundant native Seq
        // equality here leaves an opaque non-string carrier leaf that AY's
        // independent SAT gate cannot certify. Bound and non-finite lanes keep
        // the native identity for UF congruence.
        if !is_seq_sort
            || !self.use_seq_len_proxies()
            || self.quantifier_state.quantifier_depth() != 0
        {
            let eq = self.eq_term(base_term, view_term);
            self.assert_term(eq);
        }
        if is_seq_sort {
            self.assert_seq_view_identity_components(base_term, view_term);
        }
        if !already_asserted {
            self.record_view_identity(base_name.to_string());
        }
        // Propagate SeqValue so fast-path accessors work for view terms (#1317).
        if is_seq_sort {
            if let Some(sv) = self.get_seq_value_cloned(base_term) {
                self.insert_seq_value(view_term, sv);
            }
        }
    }

    fn assert_seq_view_identity_components(&mut self, base_term: Term, view_term: Term) {
        let Ok(view_arr) = self.seq_array_term(view_term) else {
            return;
        };
        let Ok(view_len) = self.seq_len_term(view_term) else {
            return;
        };
        let Ok(view_off) = self.seq_offset_term(view_term) else {
            return;
        };
        let Ok(base_arr) = self.seq_array_term(base_term) else {
            return;
        };
        let Ok(base_len) = self.seq_len_term(base_term) else {
            return;
        };
        let Ok(base_off) = self.seq_offset_term(base_term) else {
            return;
        };

        let arr_eq = self.eq_term(base_arr, view_arr);
        let len_eq = self.eq_term(base_len, view_len);
        let off_eq = self.eq_term(base_off, view_off);
        // Dedup component identities at scope 0. `assert_view_identity` is
        // intentionally called multiple times for Seq sorts (after scope pop
        // the per-name HashSet stays stale, and re-asserting reattaches the
        // identity in the new scope), but at scope 0 the components are
        // identical Term IDs across calls and re-emitting them only inflates
        // the assertion count. Key by the canonical formatted equality term
        // so the dedup HashSet survives concurrent base/view pairs.
        let scope_zero = self.solver.num_scopes() == 0;
        let arr_key = scope_zero.then(|| {
            format!(
                "view_identity/seq_array::{}",
                self.solver.format_term(arr_eq)
            )
        });
        if arr_key
            .as_ref()
            .is_none_or(|k| self.mark_logic_fn_axiom_asserted(k.clone()))
        {
            self.assert_solver_term("view_identity/seq_array", arr_eq);
        }
        let len_key = scope_zero
            .then(|| format!("view_identity/seq_len::{}", self.solver.format_term(len_eq)));
        if len_key
            .as_ref()
            .is_none_or(|k| self.mark_logic_fn_axiom_asserted(k.clone()))
        {
            self.assert_solver_term("view_identity/seq_len", len_eq);
        }
        let off_key = scope_zero.then(|| {
            format!(
                "view_identity/seq_offset::{}",
                self.solver.format_term(off_eq)
            )
        });
        if off_key
            .as_ref()
            .is_none_or(|k| self.mark_logic_fn_axiom_asserted(k.clone()))
        {
            self.assert_solver_term("view_identity/seq_offset", off_eq);
        }
        self.propagate_seq_value(base_term, view_term);
    }
}

#[cfg(test)]
mod tests;
