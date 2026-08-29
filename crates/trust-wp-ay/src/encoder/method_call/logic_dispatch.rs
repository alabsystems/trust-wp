// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::{FuncDecl, Sort, Term};
use trust_wp_core::formula::{
    internal::tuple_lowering::{NAMED_FIELD_LOGIC_FN_PREFIX, TUPLE_FIELD_LOGIC_FN_PREFIX},
    PureExpr,
};

use super::AYEncoder;
use crate::{
    encoder::{
        sort_context::{is_seq_family_sort, same_structural_family},
        unsoundness,
    },
    error::EncodingError,
};

#[derive(Clone)]
enum LogicMethodDecl {
    Direct(FuncDecl),
    Qualified { smt_name: String, decl: FuncDecl },
}

impl AYEncoder {
    fn is_structural_field_receiver(receiver: &PureExpr) -> bool {
        matches!(
            receiver,
            PureExpr::LogicFnCall { name, .. }
                if name.starts_with(TUPLE_FIELD_LOGIC_FN_PREFIX)
                    || name.starts_with(NAMED_FIELD_LOGIC_FN_PREFIX)
        )
    }

    fn logic_fn_placeholder_sort_tag(sort: &Sort) -> String {
        match sort {
            Sort::Bool => "b".to_string(),
            Sort::Int => "i".to_string(),
            Sort::Uninterpreted(name) => format!("u{}", Self::encode_method_sort_tag(name)),
            Sort::Datatype(dt) => format!("d{}", Self::encode_method_sort_tag(&dt.name)),
            other => format!("x{}", Self::encode_method_sort_tag(&format!("{other:?}"))),
        }
    }

    fn logic_fn_placeholder_decl_key(
        smt_name: &str,
        param_sorts: &[Sort],
        return_sort: &Sort,
    ) -> String {
        let params = if param_sorts.is_empty() {
            "nullary".to_string()
        } else {
            param_sorts
                .iter()
                .map(Self::logic_fn_placeholder_sort_tag)
                .collect::<Vec<_>>()
                .join("_")
        };
        // Keep structural receiver placeholders on the same naming scheme as
        // the generic placeholder path in logic_fn/call_encoding/placeholder.rs.
        // Using method_sort_tag here splits one placeholder family into two
        // SMT names for Seq returns (`...__ret_s` vs `...__ret_x536571...`),
        // which breaks declaration reuse. (#1988 audit)
        let ret = Self::logic_fn_placeholder_sort_tag(return_sort);
        format!("{smt_name}__placeholder_{params}__ret_{ret}")
    }

    fn qualified_logic_method_decl(
        &mut self,
        method: &str,
        receiver: &PureExpr,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Option<(String, FuncDecl)> {
        let direct_smt = trust_wp_core::logic::logic_fn_smt_name(method);
        let smt_suffix = direct_smt.strip_prefix("logic_").unwrap_or(&direct_smt);
        let smt_suffix = format!("_P__P_{smt_suffix}");
        let expected_arity = args.len() + 1;
        let receiver_sort = self
            .infer_expr_sort_with_context(receiver, prefix)
            .as_term_sort();
        let mut fallback = None;

        for (decl_name, decl) in self.logic_funcs_iter() {
            if decl_name.contains("__placeholder_")
                || !decl_name.ends_with(&smt_suffix)
                || decl.domain().len() != expected_arity
            {
                continue;
            }
            let candidate = (decl_name.clone(), decl.clone());
            if decl
                .domain()
                .first()
                .is_some_and(|sort| sort.as_term_sort() == receiver_sort)
            {
                return Some(candidate);
            }
            fallback.get_or_insert(candidate);
        }

        fallback
    }

    fn logic_method_decl(
        &mut self,
        method: &str,
        receiver: &PureExpr,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Option<LogicMethodDecl> {
        let smt_name = trust_wp_core::logic::logic_fn_smt_name(method);
        if let Some(func_decl) = self.logic_func_decl_cloned(&smt_name) {
            return Some(LogicMethodDecl::Direct(func_decl));
        }
        self.qualified_logic_method_decl(method, receiver, args, prefix)
            .map(|(smt_name, decl)| LogicMethodDecl::Qualified { smt_name, decl })
    }

    fn encode_qualified_logic_method_call(
        &mut self,
        method: &str,
        smt_name: &str,
        func_decl: &FuncDecl,
        receiver: &PureExpr,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        let mut all_args = vec![receiver.clone()];
        all_args.extend(args.iter().cloned());

        let mut arg_terms = Vec::with_capacity(all_args.len());
        if Self::is_structural_field_receiver(receiver)
            && func_decl
                .domain()
                .first()
                .is_some_and(|sort| *sort != Sort::Int)
        {
            arg_terms.push(
                self.encode_structural_receiver_with_expected_sort(
                    receiver,
                    func_decl
                        .domain()
                        .first()
                        .expect("guard checked receiver sort"),
                    prefix,
                )?,
            );
            for arg in args {
                arg_terms.push(self.encode_pure_impl(arg, prefix)?);
            }
        } else {
            arg_terms = all_args
                .iter()
                .map(|arg| self.encode_pure_impl(arg, prefix))
                .collect::<Result<Vec<_>, _>>()?;
        }

        let domain = func_decl.domain();
        let mut coerced_args = arg_terms.clone();
        for (i, arg_term) in coerced_args.iter_mut().enumerate() {
            let Some(expected_sort) = domain.get(i) else {
                continue;
            };
            let expected_term_sort = expected_sort.as_term_sort();
            let actual_sort = self.solver.get_sort(*arg_term);
            if actual_sort == expected_term_sort {
                continue;
            }
            if let Some(restored) =
                self.try_restore_seq_element_from_int(*arg_term, &expected_term_sort)
            {
                *arg_term = restored;
                continue;
            }
            let fresh_name = format!("__apply_coerce_{method}_{i}_{}", self.var_count());
            unsoundness::increment(unsoundness::UnsoundnessCategory::SortCoercionBridge);
            *arg_term = self.solver.declare_const(&fresh_name, expected_term_sort);
        }

        let context = format!("logic_method_call:{method}");
        let result = self.safe_apply(&context, func_decl, &coerced_args)?;
        if self.quantifier_state.quantifier_depth() == 0 {
            self.ground_pool
                .register(smt_name, result, coerced_args, all_args);
        }
        Ok(result)
    }

    fn structural_native_field_selector_with_expected_sort(
        &mut self,
        name: &str,
        arg_terms: &[Term],
        param_sorts: &[Sort],
        expected_sort: &Sort,
    ) -> Result<Option<Term>, EncodingError> {
        if arg_terms.len() != 1 || param_sorts.len() != 1 {
            return Ok(None);
        }
        let selector = if let Some(field_name) = name.strip_prefix(NAMED_FIELD_LOGIC_FN_PREFIX) {
            self.native_named_field_selector(&param_sorts[0], field_name)
        } else if let Some(field_index) = name
            .strip_prefix(TUPLE_FIELD_LOGIC_FN_PREFIX)
            .and_then(|index| index.parse::<usize>().ok())
        {
            self.native_positional_field_selector(&param_sorts[0], field_index)
        } else {
            None
        };
        let Some((selector_name, selector_sort)) = selector else {
            return Ok(None);
        };

        let compatible = selector_sort == *expected_sort
            || (is_seq_family_sort(&selector_sort) && is_seq_family_sort(expected_sort))
            || same_structural_family(&selector_sort, expected_sort).is_some();
        if !compatible {
            return Ok(None);
        }

        match self
            .solver
            .try_datatype_selector(&selector_name, arg_terms[0], selector_sort)
        {
            Ok(term) => Ok(Some(term)),
            Err(_) => Ok(None),
        }
    }

    /// Check if `method` is a registered logic function and dispatch to the
    /// logic function encoder if so. Returns `None` when no logic function
    /// is registered under this name.
    ///
    /// When the receiver is a tuple-field placeholder and the registered
    /// logic function expects a non-Int receiver, reuse that declared sort for
    /// the placeholder range instead of falling back to `Int`. This keeps
    /// tuple-return contracts connected to downstream ADT method calls. (#1322)
    pub(super) fn try_logic_fn_dispatch(
        &mut self,
        method: &str,
        receiver: &PureExpr,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Option<Result<Term, EncodingError>> {
        match self.logic_method_decl(method, receiver, args, prefix)? {
            LogicMethodDecl::Direct(func_decl) => {
                if Self::is_structural_field_receiver(receiver)
                    && func_decl
                        .domain()
                        .first()
                        .is_some_and(|sort| *sort != Sort::Int)
                {
                    return Some(
                        self.encode_logic_fn_dispatch_with_receiver_hint(
                            method,
                            receiver,
                            args,
                            prefix,
                            func_decl
                                .domain()
                                .first()
                                .expect("guard checked receiver sort"),
                        ),
                    );
                }
                let mut all_args = vec![receiver.clone()];
                all_args.extend(args.iter().cloned());
                Some(self.encode_logic_fn_call_impl(method, &all_args, prefix))
            }
            LogicMethodDecl::Qualified { smt_name, decl } => {
                Some(self.encode_qualified_logic_method_call(
                    method, &smt_name, &decl, receiver, args, prefix,
                ))
            }
        }
    }

    fn encode_logic_fn_dispatch_with_receiver_hint(
        &mut self,
        method: &str,
        receiver: &PureExpr,
        args: &[PureExpr],
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
        expected_receiver_sort: &Sort,
    ) -> Result<Term, EncodingError> {
        let mut all_args = vec![receiver.clone()];
        all_args.extend(args.iter().cloned());

        let mut arg_terms = Vec::with_capacity(all_args.len());
        arg_terms.push(self.encode_structural_receiver_with_expected_sort(
            receiver,
            expected_receiver_sort,
            prefix,
        )?);
        for arg in args {
            arg_terms.push(self.encode_pure_impl(arg, prefix)?);
        }

        let result = self.apply_logic_fn(method, &arg_terms, Some(&all_args), prefix)?;
        if self.quantifier_state.quantifier_depth() == 0 {
            let smt_name = trust_wp_core::logic::logic_fn_smt_name(method);
            self.ground_pool
                .register(&smt_name, result, arg_terms, all_args);
        }
        Ok(result)
    }

    pub(in crate::encoder) fn encode_structural_receiver_with_expected_sort(
        &mut self,
        receiver: &PureExpr,
        expected_sort: &Sort,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        if let PureExpr::View(inner) = receiver {
            let inner_term =
                self.encode_structural_receiver_with_expected_sort(inner, expected_sort, prefix)?;
            let inner_sort = self.solver.get_sort(inner_term);
            let view_is_identity = matches!(&inner_sort, Sort::Int | Sort::Bool)
                || is_seq_family_sort(&inner_sort)
                || matches!(&inner_sort, Sort::Uninterpreted(name) if name == "FMap");
            return if view_is_identity {
                Ok(inner_term)
            } else {
                let inner_expr = inner.as_ref().clone();
                self.apply_logic_fn("view", &[inner_term], Some(&[inner_expr]), prefix)
            };
        }

        let PureExpr::LogicFnCall { name, args } = receiver else {
            return self.encode_pure_impl(receiver, prefix);
        };
        if !Self::is_structural_field_receiver(receiver) {
            return self.encode_pure_impl(receiver, prefix);
        }

        let smt_name = trust_wp_core::logic::logic_fn_smt_name(name);
        if self.has_logic_func_decl(&smt_name) {
            return self.encode_pure_impl(receiver, prefix);
        }

        let arg_terms = args
            .iter()
            .map(|arg| self.encode_pure_impl(arg, prefix))
            .collect::<Result<Vec<_>, _>>()?;
        let param_sorts = arg_terms
            .iter()
            .map(|term| self.solver.get_sort(*term))
            .collect::<Vec<_>>();
        if args.len() == 1
            && name
                .strip_prefix(
                    trust_wp_core::formula::internal::tuple_lowering::TUPLE_FIELD_LOGIC_FN_PREFIX,
                )
                .and_then(|index| index.parse::<usize>().ok())
                == Some(0)
            && is_seq_family_sort(expected_sort)
            && param_sorts
                .first()
                .is_some_and(|sort| sort == expected_sort)
        {
            return Ok(arg_terms[0]);
        }
        if let Some(native_selector) = self.structural_native_field_selector_with_expected_sort(
            name,
            &arg_terms,
            &param_sorts,
            expected_sort,
        )? {
            return Ok(native_selector);
        }
        let decl_key = Self::logic_fn_placeholder_decl_key(&smt_name, &param_sorts, expected_sort);
        let func_decl =
            self.get_or_declare_logic_func(&decl_key, &param_sorts, expected_sort.clone());
        self.safe_apply(
            &format!("logic_fn_receiver_hint:{name}"),
            &func_decl,
            &arg_terms,
        )
    }
}
