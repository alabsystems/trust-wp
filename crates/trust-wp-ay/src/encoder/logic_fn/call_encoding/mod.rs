// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Logic function call-site encoding.
//!
//! Contains:
//! - `infer_expr_sort_with_context` — sort inference with logic function declaration context
//! - `apply_logic_fn` — UF declaration lookup/creation and application with sort coercion
//! - `encode_logic_fn_call_impl` — top-level call dispatch (builtins, datatypes, UF fallback)
//! - `propagate_domain_sort_hints` — pre-encoding domain sort hint propagation

mod dispatch;
mod placeholder;
mod uf_ctor_axioms;

use ay_dpll::api::{DatatypeSort, Sort};
use trust_wp_core::formula::PureExpr;

use crate::encoder::{
    match_enc::{
        datatype_constructor_matches, datatype_constructor_name, short_constructor_name,
        stdlib_constructor_target, SwitchTarget,
    },
    sort_context::{
        extract_inner_var_annotation, is_seq_family_sort, resolve_nameable_expr,
        resolve_registered_non_int_sort, resolve_view_var_name, DerivedKind,
    },
    AYEncoder,
};

pub(crate) fn transparent_adapter_inner(expr: &PureExpr) -> Option<&PureExpr> {
    let PureExpr::LogicFnCall { name, args } = expr else {
        return None;
    };
    let short_name = name.rsplit("::").next().unwrap_or(name.as_str());
    if matches!(short_name, "Copied" | "Cloned") && args.len() == 1 {
        Some(&args[0])
    } else {
        None
    }
}

impl AYEncoder {
    pub(in crate::encoder) fn native_constructor_call(
        &mut self,
        name: &str,
        args: &[PureExpr],
        prefix: Option<DerivedKind>,
    ) -> Option<(DatatypeSort, String, Vec<Sort>)> {
        let dt = self
            .preferred_option_some_datatype(name, args, prefix)
            .or_else(|| self.constructor_datatype(name))
            .or_else(|| self.try_auto_register_stdlib_constructor(name, args, prefix))?;
        let actual_name = datatype_constructor_name(&dt, name);
        let field_sorts: Vec<Sort> = dt
            .constructors
            .iter()
            .find(|ctor| datatype_constructor_matches(&dt, &ctor.name, name))?
            .fields
            .iter()
            .map(|field| field.sort.clone())
            .collect();
        if args.len() != field_sorts.len() {
            return None;
        }
        let args_compatible = args.iter().zip(field_sorts.iter()).all(|(arg, expected)| {
            let actual = self.infer_expr_sort_with_context(arg, prefix);
            // Compare via as_term_sort() to treat Sort::Datatype(dt) and
            // Sort::Uninterpreted(dt.name) as equivalent. Without this,
            // OwnResult::Ok(Some(sk_t)) fails the pre-encoding check when
            // the Ok field is OptionInt (Uninterpreted) but infer_expr_sort
            // returns Datatype(OptionInt) for Some(sk_t). This forces the UF
            // fallback path and creates a different UF than the body's
            // OwnResult::Ok(x:Int), breaking congruence. (#1296)
            actual.as_term_sort() == expected.as_term_sort()
                || (actual == Sort::Bool && *expected == Sort::Int)
        });
        args_compatible.then_some((dt, actual_name, field_sorts))
    }

    fn preferred_option_some_datatype(
        &mut self,
        ctor_name: &str,
        args: &[PureExpr],
        prefix: Option<DerivedKind>,
    ) -> Option<DatatypeSort> {
        if !matches!(
            stdlib_constructor_target(ctor_name),
            Some(SwitchTarget::OptionInt)
        ) || short_constructor_name(ctor_name) != "Some"
        {
            return None;
        }
        let [payload] = args else {
            return None;
        };
        let datatype = if ctor_name == short_constructor_name(ctor_name) {
            let payload_sort = self.infer_expr_sort_with_context(payload, prefix);
            self.stdlib_option_datatype_for_payload_sort(payload_sort)
        } else {
            SwitchTarget::OptionInt.datatype()
        };
        self.ensure_datatype_declared(&datatype);
        Some(datatype)
    }

    pub(super) fn tuple_getter_return_sort(
        &mut self,
        name: &str,
        args: &[PureExpr],
        prefix: Option<DerivedKind>,
    ) -> Option<Sort> {
        let index = name
            .strip_prefix(
                trust_wp_core::formula::internal::tuple_lowering::TUPLE_FIELD_LOGIC_FN_PREFIX,
            )?
            .parse::<usize>()
            .ok()?;
        let [receiver] = args else {
            return None;
        };
        let PureExpr::LogicFnCall {
            name: tuple_name,
            args: tuple_args,
        } = receiver
        else {
            return None;
        };
        let arity =
            trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_arity(tuple_name)?;
        if index >= arity || index >= tuple_args.len() {
            return None;
        }
        Some(self.infer_expr_sort_with_context(&tuple_args[index], prefix))
    }

    /// Peek at a receiver expression's sort without encoding it.
    ///
    /// Returns `Some(sort)` when the receiver is either:
    /// - a nameable wrapper chain with a known registered sort or hint, or
    /// - a registered datatype constructor call that is eligible for the
    ///   native constructor path.
    ///
    /// This avoids the side effects of full encoding (variable declarations,
    /// sort preseeding) that would break downstream encoding paths for
    /// tuple-lowered expressions.
    ///
    /// Used by the positional tuple-get → native selector upgrade (#1982).
    pub(super) fn peek_receiver_sort(
        &mut self,
        expr: &PureExpr,
        prefix: Option<DerivedKind>,
    ) -> Option<Sort> {
        if let PureExpr::LogicFnCall { name, args } = expr {
            return self
                .native_constructor_call(name, args, prefix)
                .map(|(dt, _, _)| Sort::Datatype(dt));
        }
        if let Some(annotation) = extract_inner_var_annotation(expr) {
            let sort = self.sort_from_expr_sort(annotation.clone());
            if sort != Sort::Int {
                return Some(sort);
            }
        }
        if let Some(view_name) = resolve_view_var_name(expr, prefix) {
            if let Some(sort) = resolve_registered_non_int_sort(self, &view_name) {
                return Some(sort);
            }
        }
        resolve_nameable_expr(expr, prefix)
            .and_then(|name| resolve_registered_non_int_sort(self, &name))
    }

    pub(super) fn is_incompatible_declared_constructor_call(
        &mut self,
        expr: &PureExpr,
        prefix: Option<DerivedKind>,
    ) -> bool {
        let PureExpr::LogicFnCall { name, args } = expr else {
            return false;
        };
        self.constructor_datatype(name).is_some()
            && self.native_constructor_call(name, args, prefix).is_none()
    }

    pub(crate) fn infer_expr_sort_with_context(
        &mut self,
        expr: &PureExpr,
        prefix: Option<DerivedKind>,
    ) -> Sort {
        if let PureExpr::View(inner) = expr {
            let inner_sort = self.infer_expr_sort_with_context(inner, prefix);
            if is_seq_family_sort(&inner_sort)
                || matches!(&inner_sort, Sort::Uninterpreted(name) if matches!(name.as_str(), "FMap" | "Mapping"))
            {
                return inner_sort;
            }
        }
        if let PureExpr::LogicFnCall { name, args } = expr {
            if let [receiver] = args.as_slice() {
                let receiver_sort = self.infer_expr_sort_with_context(receiver, prefix);
                if let Some(sort) = self.native_field_projection_return_sort(name, &receiver_sort) {
                    return sort;
                }
            }
            if let Some(sort) = self.tuple_getter_return_sort(name, args, prefix) {
                return sort;
            }
            if let Some((dt, _, _)) = self.native_constructor_call(name, args, prefix) {
                return Sort::Datatype(dt);
            }
            let smt_name = trust_wp_core::logic::logic_fn_smt_name(name);
            // Resolve Self-parametric trait method calls for sort inference.
            // When `Self::method()` has no declaration, try the bare method name.
            let smt_name = if !self.has_logic_func_decl(&smt_name) {
                if let Some(method) = name.strip_prefix("Self::") {
                    let bare = trust_wp_core::logic::logic_fn_smt_name(method);
                    if self.has_logic_func_decl(&bare) {
                        bare
                    } else {
                        smt_name
                    }
                } else {
                    smt_name
                }
            } else {
                smt_name
            };
            if let Some(func_decl) = self.logic_func_decl_cloned(&smt_name) {
                return func_decl.range().clone();
            }
            let param_sorts = args
                .iter()
                .map(|arg| self.infer_expr_sort_with_context(arg, prefix))
                .collect::<Vec<_>>();
            if let Some(existing) = self.existing_placeholder_return_sort(&smt_name, &param_sorts) {
                return existing;
            }
            if let Some(hint) = self.sort_hint_cloned(&smt_name) {
                return self.sort_from_expr_sort(hint);
            }
        }
        self.infer_encoded_sort(expr, prefix)
    }

    /// Auto-register a stdlib datatype when an unqualified constructor name
    /// (e.g., `Some`, `None`) is encountered but the corresponding datatype
    /// (OptionInt) hasn't been declared yet.
    ///
    /// This handles postconditions like `result == Some(t)` where the
    /// function returns `Option<T>` but the body encoding hasn't triggered
    /// OptionInt registration (because the body's match was on a different
    /// type like OwnResult). (#1296)
    ///
    /// Only registers when the constructor arguments are sort-compatible
    /// with the stdlib datatype fields (all Int). This prevents registering
    /// OptionInt for `Some(OwnResult::Err(e))` where the inner type is a
    /// Datatype, not Int — which would cause a sort mismatch for nested
    /// ADT patterns like `OwnResult<Option<T>, E>::transpose`.
    fn try_auto_register_stdlib_constructor(
        &mut self,
        ctor_name: &str,
        args: &[PureExpr],
        prefix: Option<DerivedKind>,
    ) -> Option<DatatypeSort> {
        let short = short_constructor_name(ctor_name);
        let target = match stdlib_constructor_target(ctor_name) {
            Some(SwitchTarget::OptionInt) => SwitchTarget::OptionInt,
            Some(SwitchTarget::ResultIntInt) => SwitchTarget::ResultIntInt,
            _ => return None,
        };
        let dt = if matches!(target, SwitchTarget::OptionInt) && short == "Some" && args.len() == 1
        {
            let payload_sort = self.infer_expr_sort_with_context(&args[0], prefix);
            self.stdlib_option_datatype_for_payload_sort(payload_sort)
        } else {
            target.datatype()
        };
        // Check that args are compatible with the stdlib field sorts
        // BEFORE registering. For Some(T), the datatype above is specialized
        // to the payload sort when the payload is non-Int.
        let ctor = dt
            .constructors
            .iter()
            .find(|c| datatype_constructor_matches(&dt, &c.name, short))?;
        if args.len() != ctor.fields.len() {
            return None;
        }
        let compatible = args.iter().zip(ctor.fields.iter()).all(|(arg, field)| {
            let actual = self.infer_expr_sort_with_context(arg, prefix);
            actual.as_term_sort() == field.sort.as_term_sort()
                || (is_seq_family_sort(&actual) && is_seq_family_sort(&field.sort))
                || (actual == Sort::Bool && field.sort == Sort::Int)
        });
        if !compatible {
            return None;
        }
        self.ensure_datatype_declared(&dt);
        Some(dt)
    }
}
