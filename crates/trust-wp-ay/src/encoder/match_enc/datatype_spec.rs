// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Option/Result spec method encoding.
//!
//! Maps Rust `Option` and `Result` method calls (`is_some`, `unwrap`, etc.)
//! to SMT constructor testers and field accessors.

use ay_dpll::api::{DatatypeSort, Sort, Term};
use trust_wp_core::formula::{intern_sort_name, ExprSort, PureExpr};

use super::{datatype_constructor_name, short_constructor_name, AYEncoder, SwitchTarget};
use crate::{encoder::sort_context::resolve_nameable_expr, error::EncodingError};

impl AYEncoder {
    fn fmap_get_receiver_parts(receiver: &PureExpr) -> Option<(&PureExpr, &PureExpr)> {
        let PureExpr::MethodCall {
            receiver,
            method,
            args,
        } = receiver
        else {
            return None;
        };
        if !matches!(method.as_str(), "get" | "get_ghost" | "get_mut_ghost") || args.len() != 1 {
            return None;
        }
        Some((receiver.as_ref(), &args[0]))
    }

    fn direct_constructor_payload_expr<'a>(
        receiver: &'a PureExpr,
        ctor_names: &[&str],
    ) -> Option<&'a PureExpr> {
        let PureExpr::LogicFnCall { name, args } = receiver else {
            return None;
        };
        (args.len() == 1
            && ctor_names
                .iter()
                .any(|ctor| short_constructor_name(name) == *ctor))
        .then(|| &args[0])
    }

    /// Evaluate a tester on a concrete constructor at the PureExpr level.
    ///
    /// When the receiver is a direct constructor call (e.g., `None()`, `Some(1)`,
    /// `Ok(v)`, `Err(e)`), we can determine the tester result statically without
    /// the solver. This is critical for postcondition substitution patterns where
    /// `self` is replaced by a concrete value: `None().is_some()` -> `false`,
    /// `Some(1).is_none()` -> `false`, etc. Without this, the solver sees UF calls
    /// with no connecting axioms when sort_fallback_to_int is active. (#2670)
    fn direct_constructor_tester(receiver: &PureExpr, positive_ctors: &[&str]) -> Option<bool> {
        // Unwrap Deref wrapper: `(*None()).is_some()` should also resolve.
        let inner = match receiver {
            PureExpr::Deref(inner) => inner.as_ref(),
            other => other,
        };
        let PureExpr::LogicFnCall { name, .. } = inner else {
            return None;
        };
        let short = short_constructor_name(name);
        // Only resolve for known Option/Result constructors to avoid false
        // positives on arbitrary logic function calls.
        let known_ctors = ["Some", "None", "Ok", "Err"];
        if !known_ctors.iter().any(|c| short == *c) {
            return None;
        }
        Some(positive_ctors.iter().any(|c| short == *c))
    }

    /// Encode an Option/Result spec method call as constructor tester or accessor.
    ///
    /// Maps method names to the SMT-level constructor testers and field accessors:
    /// - `is_some()` -> `is_some(receiver)` (Bool)
    /// - `is_none()` -> `not(is_some(receiver))` (Bool)
    /// - `unwrap()` / `unwrap_logic()` -> `spec_unwrap(receiver)` (Int) -- type-agnostic accessor
    /// - `is_ok()` -> `is_ok(receiver)` (Bool)
    /// - `is_err()` -> `not(is_ok(receiver))` (Bool)
    /// - `unwrap_err()` -> `result_err_error(receiver)` (Int)
    /// - `as_ref()` / `as_mut()` -> `receiver` (identity -- no ref/mut distinction in SMT)
    /// - `unwrap_or_default()` -> `ite(is_some/is_ok, unwrap, 0)` (Int default)
    ///
    /// `unwrap()` uses a single `spec_unwrap` function regardless of whether the
    /// receiver is `Option` or `Result`. Since `PureExpr` has no type info and the
    /// SMT encoding is untyped (`Int`), a single accessor is correct: the
    /// constructor testers (`is_some`/`is_ok`) provide the type discrimination.
    #[allow(clippy::too_many_lines)] // Dispatch across Option/Result spec methods
    pub(in crate::encoder) fn encode_datatype_spec_method(
        &mut self,
        receiver: &PureExpr,
        method: &str,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        // Fast path: evaluate tester on concrete constructor without involving
        // the solver. When postcondition substitution replaces `self` with a
        // concrete value (e.g., `None().is_some()` -> false), the UF encoding
        // cannot establish the connection between the constructor UF and tester
        // UF without additional axioms. Short-circuiting here avoids the
        // sort_fallback_to_int UF mismatch entirely. (#2670)
        match method {
            "is_some" => {
                if let Some(val) = Self::direct_constructor_tester(receiver, &["Some"]) {
                    return Ok(self.solver.bool_const(val));
                }
            }
            "is_none" => {
                if let Some(val) = Self::direct_constructor_tester(receiver, &["None"]) {
                    return Ok(self.solver.bool_const(val));
                }
            }
            "is_ok" => {
                if let Some(val) = Self::direct_constructor_tester(receiver, &["Ok"]) {
                    return Ok(self.solver.bool_const(val));
                }
            }
            "is_err" => {
                if let Some(val) = Self::direct_constructor_tester(receiver, &["Err"]) {
                    return Ok(self.solver.bool_const(val));
                }
            }
            _ => {}
        }

        if matches!(method, "unwrap" | "unwrap_logic") {
            if let Some((map_receiver, key)) = Self::fmap_get_receiver_parts(receiver) {
                if self.is_fmap_receiver(map_receiver, prefix) {
                    return self.encode_fmap_method(
                        map_receiver,
                        "lookup",
                        std::slice::from_ref(key),
                        prefix,
                    );
                }
            }
        }

        self.seed_datatype_spec_receiver_hint(receiver, method, prefix);
        let receiver_term = self.encode_pure_impl(receiver, prefix)?;
        let receiver_sort = self.solver.get_sort(receiver_term);

        match method {
            "is_some" => {
                // Try native datatype tester first — handles OptionInt/Option-sorted
                // receivers without the Int→Bool UF sort mismatch (#994, #2155).
                if let Some(is_some) =
                    self.try_native_tester_or_cross_family_constant(receiver_term, "Some")
                {
                    return Ok(is_some);
                }
                // UF fallback for Int-sorted receivers
                if !Self::is_result_constructor(receiver) {
                    self.assert_is_option(receiver_term)?;
                }
                let tester =
                    self.get_or_declare_constructor_tester_for_sort("is_some", &receiver_sort);
                self.safe_apply("is_some_method", &tester, &[receiver_term])
            }
            "is_none" => {
                // Try native datatype tester first (#994, #2155).
                if let Some(is_some) =
                    self.try_native_tester_or_cross_family_constant(receiver_term, "Some")
                {
                    return Ok(self.solver.not(is_some));
                }
                // UF fallback
                if !Self::is_result_constructor(receiver) {
                    self.assert_is_option(receiver_term)?;
                }
                let tester =
                    self.get_or_declare_constructor_tester_for_sort("is_some", &receiver_sort);
                let is_some = self.safe_apply("is_none_method", &tester, &[receiver_term])?;
                Ok(self.solver.not(is_some))
            }
            "is_ok" => {
                // Try native datatype tester first (#994, #2155).
                if let Some(is_ok) =
                    self.try_native_tester_or_cross_family_constant(receiver_term, "Ok")
                {
                    return Ok(is_ok);
                }
                // UF fallback
                let tester =
                    self.get_or_declare_constructor_tester_for_sort("is_ok", &receiver_sort);
                self.safe_apply("is_ok_method", &tester, &[receiver_term])
            }
            "is_err" => {
                // Try native datatype tester first (#994, #2155).
                if let Some(is_ok) =
                    self.try_native_tester_or_cross_family_constant(receiver_term, "Ok")
                {
                    return Ok(self.solver.not(is_ok));
                }
                // UF fallback
                let tester =
                    self.get_or_declare_constructor_tester_for_sort("is_ok", &receiver_sort);
                let is_ok = self.safe_apply("is_err_method", &tester, &[receiver_term])?;
                Ok(self.solver.not(is_ok))
            }
            "unwrap" | "unwrap_logic" => {
                if let Some(payload_expr) =
                    Self::direct_constructor_payload_expr(receiver, &["Some", "Ok"])
                {
                    return self.encode_pure_impl(payload_expr, prefix);
                }
                // Try native datatype selector first — handles OptionInt/Option-sorted
                // receivers without Int→Int UF sort mismatch (#994, #2155).
                if let Some(payload) =
                    self.try_native_payload_selector_for_any(receiver_term, &["Some", "Ok"])
                {
                    return Ok(payload);
                }
                let accessor = self.get_or_declare_accessor_for_sorts(
                    "spec_unwrap",
                    &receiver_sort,
                    &Sort::Int,
                );
                self.safe_apply("unwrap_method", &accessor, &[receiver_term])
            }
            "unwrap_err" => {
                if let Some(payload_expr) =
                    Self::direct_constructor_payload_expr(receiver, &["Err"])
                {
                    return self.encode_pure_impl(payload_expr, prefix);
                }
                // Try native datatype selector first (#994, #2155).
                if let Some(payload) =
                    self.try_native_payload_selector_for_any(receiver_term, &["Err"])
                {
                    return Ok(payload);
                }
                let accessor = self.get_or_declare_accessor_for_sorts(
                    "result_err_error",
                    &receiver_sort,
                    &Sort::Int,
                );
                self.safe_apply("unwrap_err_method", &accessor, &[receiver_term])
            }
            // as_ref / as_mut: identity in SMT — references and values share
            // the same sort, so Option<&T> and Option<T> are indistinguishable.
            // Returns the receiver term unchanged. (#1296)
            "as_ref" | "as_mut" => Ok(receiver_term),
            // unwrap_or_default: returns the payload if Some/Ok, else the
            // default value for T. In the Int-sorted SMT encoding, the
            // default for Int is 0. Uses ite(is_some/is_ok, unwrap, 0).
            // (#1296)
            "unwrap_or_default" => {
                if let Some(payload_expr) =
                    Self::direct_constructor_payload_expr(receiver, &["Some", "Ok"])
                {
                    return self.encode_pure_impl(payload_expr, prefix);
                }
                // Determine whether this is an Option or Result receiver.
                // Use the same heuristic as is_some/is_ok: check if the
                // receiver is a Result constructor, otherwise assume Option.
                let is_result =
                    Self::is_result_constructor(receiver) || self.is_result_sorted(receiver_term);
                let tester_ctor = if is_result { "Ok" } else { "Some" };

                // Build is_some/is_ok(receiver)
                let tester_term = if let Some(t) =
                    self.try_native_tester_or_cross_family_constant(receiver_term, tester_ctor)
                {
                    t
                } else {
                    let tester_name = if is_result { "is_ok" } else { "is_some" };
                    if !is_result {
                        self.assert_is_option(receiver_term)?;
                    }
                    let tester = self
                        .get_or_declare_constructor_tester_for_sort(tester_name, &receiver_sort);
                    self.safe_apply("unwrap_or_default_tester", &tester, &[receiver_term])?
                };

                // Build unwrap(receiver)
                let payload = if let Some(p) =
                    self.try_native_payload_selector_for_any(receiver_term, &[tester_ctor])
                {
                    p
                } else {
                    let accessor = self.get_or_declare_accessor_for_sorts(
                        "spec_unwrap",
                        &receiver_sort,
                        &Sort::Int,
                    );
                    self.safe_apply("unwrap_or_default_payload", &accessor, &[receiver_term])?
                };

                // Default value: 0 for Int sort
                let default_val = self.solver.int_const(0);

                // ite(is_some/is_ok, payload, 0) — use safe_ite to prevent
                // ay panics when payload sort differs from Int. (#2687)
                Ok(self.safe_ite(tester_term, payload, default_val))
            }
            // Defensive: callers dispatch only known spec methods here.
            _ => Err(EncodingError::unsupported(format!(
                "unknown datatype spec method: {method}"
            ))),
        }
    }

    /// Assert `is_option(term)`, lazily declaring the predicate if needed.
    /// This closes the Option domain for abstract variables, enabling the
    /// None reconstruction axiom (#1109, #1211).
    ///
    /// The assertion is deduplicated per-term to prevent redundant constraints,
    /// and guarded by the active path condition so it does not permanently
    /// over-constrain variables used outside Option match contexts (#1642).
    pub(in crate::encoder::match_enc) fn assert_is_option(
        &mut self,
        term: Term,
    ) -> Result<(), EncodingError> {
        if self.encoding_cache.is_option_asserted_contains(&term) {
            return Ok(());
        }
        // The __trust_wp_is_option UF has domain Sort::Int. When the term has
        // a non-Int sort (e.g., Datatype("Option"), Seq), the UF application
        // would panic with a sort mismatch. Non-Int sorted terms are already
        // type-safe and don't need Int-domain Option discrimination. (#2207)
        let term_sort = self.solver.get_sort(term);
        if term_sort != Sort::Int {
            return Ok(());
        }
        let is_option =
            self.get_or_declare_spec_func("__trust_wp_is_option", &[Sort::Int], Sort::Bool);
        let assertion = self.safe_apply("assert_is_option", &is_option, &[term])?;
        let guarded = self.guard_with_active_path(assertion);
        self.assert_solver_term("assert_is_option", guarded);
        self.encoding_cache.is_option_asserted_insert(term);
        Ok(())
    }

    /// Check if a `PureExpr` is a Result constructor (`Ok` or `Err`).
    /// Used to avoid asserting `is_option` for Result values (#1211).
    /// Handles both unqualified (`Ok`) and qualified (`OwnResult::Ok`) names (#1787).
    pub(in crate::encoder::match_enc) fn is_result_constructor(expr: &PureExpr) -> bool {
        matches!(
            expr,
            PureExpr::LogicFnCall { name, .. }
                if matches!(short_constructor_name(name), "Ok" | "Err")
        )
    }

    fn seed_datatype_spec_receiver_hint(
        &mut self,
        receiver: &PureExpr,
        method: &str,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) {
        let target = match method {
            "is_some" | "is_none" => Some(SwitchTarget::OptionInt.datatype()),
            "is_ok" | "is_err" | "unwrap_err" => Some(SwitchTarget::ResultIntInt.datatype()),
            _ => None,
        };
        let Some(datatype) = target else {
            return;
        };
        let Some(name) = resolve_nameable_expr(receiver, prefix) else {
            return;
        };
        // If the receiver already has a Datatype sort hint (e.g., from user-defined
        // ADT declarations like OwnResult), do NOT override it with the built-in
        // ResultIntInt/OptionInt. (#1296)
        if let Some(ExprSort::Datatype(_)) = self.sort_hint(&name) {
            return;
        }
        // If a user-defined ADT with the same constructor names (Ok/Err for Result,
        // Some/None for Option) is already declared, skip the built-in seeding.
        // Declaring both a user-defined ADT and the built-in with overlapping
        // constructor names causes ay sort mismatch panics when the same constructor
        // term (e.g., Ok(x)) is interned with two different sorts. (#1296)
        let probe_ctor = match method {
            "is_some" | "is_none" => "Some",
            "is_ok" | "is_err" | "unwrap_err" => "Ok",
            _ => return,
        };
        let has_user_adt = self
            .datatypes_for_constructor(probe_ctor)
            .any(|dt| dt.name != datatype.name);
        if has_user_adt {
            return;
        }
        self.ensure_datatype_declared(&datatype);
        self.record_sort_hint_if_absent(name, ExprSort::Datatype(intern_sort_name(&datatype.name)));
    }

    /// Check whether a term has a Result-family sort (ResultIntInt or similar).
    /// Used by `unwrap_or_default` to select the correct tester (`is_ok` vs `is_some`).
    fn is_result_sorted(&self, term: Term) -> bool {
        if let Some(dt) = self.receiver_native_datatype(term) {
            dt.constructors
                .iter()
                .any(|ctor| ctor.name == "Ok" || ctor.name == "Err")
        } else {
            false
        }
    }

    fn receiver_native_datatype(&self, receiver_term: Term) -> Option<DatatypeSort> {
        match self.solver.get_sort(receiver_term) {
            Sort::Datatype(dt) => Some(dt),
            Sort::Uninterpreted(name) => self.get_datatype_decl(&name).cloned(),
            _ => None,
        }
    }

    fn try_native_tester_or_cross_family_constant(
        &mut self,
        receiver_term: Term,
        ctor_name: &str,
    ) -> Option<Term> {
        if let Ok(tester) = self.solver.try_datatype_tester(ctor_name, receiver_term) {
            return Some(tester);
        }

        let datatype = self.receiver_native_datatype(receiver_term)?;
        let actual_ctor = datatype_constructor_name(&datatype, ctor_name);
        if let Ok(tester) = self.solver.try_datatype_tester(&actual_ctor, receiver_term) {
            return Some(tester);
        }

        (!datatype
            .constructors
            .iter()
            .any(|ctor| ctor.name == actual_ctor))
        .then(|| self.solver.bool_const(false))
    }

    /// Try to extract a constructor payload using native datatype selectors.
    ///
    /// Looks up the declared datatype for `ctor_name` (e.g., "Some", "Err") and
    /// uses `try_datatype_selector` to extract the single-field payload. Returns
    /// `None` if the datatype is not declared, the constructor has != 1 field,
    /// or the selector application fails (e.g., sort mismatch).
    ///
    /// This avoids the Int→Int UF accessor sort mismatch when the receiver has
    /// a native Datatype sort (OptionInt, ResultIntInt, etc.). (#994, #2155)
    fn try_native_payload_selector_for_any(
        &mut self,
        receiver_term: Term,
        ctor_names: &[&str],
    ) -> Option<Term> {
        let datatype = self.receiver_native_datatype(receiver_term)?;
        ctor_names.iter().find_map(|ctor_name| {
            let (sel_name, sel_sort) = Self::constructor_payload_selector(&datatype, ctor_name)?;
            self.solver
                .try_datatype_selector(sel_name, receiver_term, sel_sort.clone())
                .ok()
        })
    }
}
