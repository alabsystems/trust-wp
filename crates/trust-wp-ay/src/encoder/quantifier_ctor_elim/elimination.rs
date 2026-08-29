// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Constructor equality quantifier elimination encoding.
//!
//! Implements the `AYEncoder` methods that eliminate quantifiers by substituting
//! bound variables with datatype selector terms. Handles both single-level and
//! nested (two-level) constructor equality patterns.
//!
//! Extracted from `quantifier_ctor_elim.rs` as part of #1988 structural decomposition.

use ay_dpll::api::{Sort, Term};
use tracing::debug;
use trust_wp_core::formula::{BinOp, PureExpr};

use super::{
    super::{
        match_enc::{
            datatype_constructor_matches, datatype_constructor_name, short_constructor_name,
            stdlib_constructor_target,
        },
        quantifier::QuantifierKind,
        AYEncoder,
    },
    extract_scrutinee_var_name, ConstructorEqInfo, InnerConstructorEq, OuterElimContext,
};
use crate::error::EncodingError;

impl AYEncoder {
    /// Eliminate a quantifier over a constructor equality using datatype
    /// tester/selector operations (#1752, #1765).
    ///
    /// Handles single-variable and multi-variable patterns. Each bound variable
    /// is substituted with the corresponding field selector applied to the scrutinee.
    #[allow(clippy::too_many_lines)] // Core constructor-equality quantifier elimination
    pub(in crate::encoder) fn eliminate_constructor_eq_quantifier(
        &mut self,
        kind: QuantifierKind,
        body: &PureExpr,
        info: &ConstructorEqInfo<'_>,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        // Pre-seed the scrutinee variable's sort to the constructor's datatype
        // sort before encoding. Without this, variables like `self` or `*self`
        // default to Sort::Int, and `try_datatype_tester` fails with a sort
        // mismatch because it expects a Datatype-sorted argument. (#1752)
        if let Some(var_name) = extract_scrutinee_var_name(info.scrutinee) {
            let dt_sort = Sort::Datatype(info.datatype.clone());
            if !self.has_var_sort(var_name) || matches!(self.var_sort(var_name), Some(Sort::Int)) {
                self.insert_var_sort(var_name.to_string(), dt_sort);
            }
        }
        let scrutinee_term = self.encode_pure_impl(info.scrutinee, prefix)?;
        let short_name = short_constructor_name(info.ctor_name);
        let actual_name = datatype_constructor_name(&info.datatype, short_name);
        let tester = self
            .solver
            .try_datatype_tester(&actual_name, scrutinee_term)
            .map_err(|e| {
                EncodingError::solver_error(format!(
                    "constructor equality elimination: datatype tester for {}: {e}",
                    info.ctor_name,
                ))
            })?;

        match kind {
            QuantifierKind::Exists => {
                // For a single-constructor datatype, `exists vars. x == Ctor(vars)`
                // is equivalent to reconstructing `x` from its selectors. Keep
                // the ground reconstruction equality instead of collapsing all
                // the way to `true` so datatype axioms still have concrete terms
                // to instantiate against in SAT checks.
                if info.datatype.constructors.len() == 1 {
                    let Some(ctor) = info
                        .datatype
                        .constructors
                        .iter()
                        .find(|c| c.name == short_name)
                    else {
                        return Ok(tester);
                    };

                    let mut selector_terms = Vec::with_capacity(ctor.fields.len());
                    for field in &ctor.fields {
                        let selector = self
                            .solver
                            .try_datatype_selector(
                                &field.name,
                                scrutinee_term,
                                field.sort.clone(),
                            )
                            .map_err(|e| {
                                EncodingError::solver_error(format!(
                                    "constructor equality elimination: datatype selector {}.{}: {e}",
                                    info.datatype.name, field.name,
                                ))
                            })?;
                        selector_terms.push(selector);
                    }

                    let Some(reconstructed) = self.axiom_datatype_constructor(
                        "constructor equality elimination",
                        &info.datatype,
                        short_name,
                        &selector_terms,
                    ) else {
                        return Ok(tester);
                    };
                    Ok(self.eq_term(scrutinee_term, reconstructed))
                } else {
                    Ok(tester)
                }
            }
            QuantifierKind::Forall => {
                // detect_constructor_eq guarantees Forall bodies are Implies-shaped (#1781).
                // Non-Implies bodies are rejected at detection time, so this arm is
                // unreachable via normal control flow. Return an error for defense-in-depth.
                let consequent = match body {
                    PureExpr::BinOp(_, BinOp::Implies, rhs) => rhs.as_ref(),
                    _ => {
                        return Err(EncodingError::solver_error(
                            "constructor equality elimination: Forall body is not \
                             Implies-shaped; detection should have rejected this (#1781)"
                                .to_string(),
                        ));
                    }
                };

                if info.var_field_map.is_empty() && info.inner_ctor.is_none() {
                    let consequent_term = self.encode_pure_impl(consequent, prefix)?;
                    return Ok(self.solver.implies(tester, consequent_term));
                }

                // Nested constructor elimination (#1296):
                // `forall t. self == OwnResult::Ok(Some(t)) ==> P(t)` becomes:
                // `is-Ok(self) && is_inner(selector(self)) ==> P(accessor(selector(self)))`
                if let Some(ref inner) = info.inner_ctor {
                    let outer = OuterElimContext {
                        scrutinee_term,
                        outer_tester: tester,
                        info,
                    };
                    return self.eliminate_nested_constructor_eq(&outer, inner, consequent, prefix);
                }

                let Some(ctor) = info
                    .datatype
                    .constructors
                    .iter()
                    .find(|c| c.name == short_name)
                else {
                    let consequent_term = self.encode_pure_impl(consequent, prefix)?;
                    return Ok(self.solver.implies(tester, consequent_term));
                };

                // Bind each quantifier variable to its field's selector term.
                // Each entry: (var_name, old_unprefixed_binding, old_prefixed_binding).
                #[allow(clippy::type_complexity)]
                let mut old_bindings: Vec<(
                    &str,
                    Option<Term>,
                    Option<(String, Option<Term>)>,
                )> = Vec::with_capacity(info.var_field_map.len());

                for &(qvar, field_idx) in &info.var_field_map {
                    let Some(field) = ctor.fields.get(field_idx) else {
                        return Err(EncodingError::solver_error(format!(
                            "constructor equality elimination: field index {field_idx} \
                             out of range for constructor {}",
                            info.ctor_name,
                        )));
                    };
                    let accessor_term = self
                        .solver
                        .try_datatype_selector(&field.name, scrutinee_term, field.sort.clone())
                        .map_err(|e| {
                            EncodingError::solver_error(format!(
                                "constructor equality elimination: selector {}: {e}",
                                field.name,
                            ))
                        })?;

                    let old_binding = self.insert_var(qvar.to_string(), accessor_term);
                    let old_prefixed = if let Some(kind) = prefix {
                        let prefixed = kind.format_name(qvar);
                        if prefixed == qvar {
                            None
                        } else {
                            Some((prefixed.clone(), self.insert_var(prefixed, accessor_term)))
                        }
                    } else {
                        None
                    };
                    old_bindings.push((qvar, old_binding, old_prefixed));
                }

                // Mark substituted variables as quantifier-bound so that
                // encode_deref_or_final Phase 1 collapses Deref(Var(v)) → v
                // instead of creating a disconnected `v_current` variable.
                // Without this, postconditions like `*t` (parsed as Deref(Var("t")))
                // would bypass the selector substitution. (#1296, #717)
                for &(qvar, _) in &info.var_field_map {
                    self.bind_quantifier_var(qvar.to_string());
                }

                let consequent_term = self.encode_pure_impl(consequent, prefix);

                for &(qvar, _) in &info.var_field_map {
                    self.unbind_quantifier_var(qvar);
                }

                for (qvar, old_binding, old_prefixed) in old_bindings.into_iter().rev() {
                    if let Some((name, old)) = old_prefixed {
                        self.restore_var(&name, old);
                    }
                    self.restore_var(qvar, old_binding);
                }

                let consequent_term = consequent_term?;
                Ok(self.solver.implies(tester, consequent_term))
            }
        }
    }

    /// Eliminate a nested constructor equality: `forall t. self == Outer(Inner(t)) ==> P(t)`.
    ///
    /// Produces: `outer_tester(self) && inner_tester(payload) ==> P(accessor(payload))`
    /// where `payload = outer_selector(self)`.
    ///
    /// The inner tester/accessor uses the UF-model spec functions (is_some,
    /// spec_unwrap) when the payload sort is `Int` (matching the standard axiom
    /// layer). When the payload has a native datatype sort, it uses the native
    /// datatype tester/selector. (#1296)
    #[allow(clippy::too_many_lines)]
    fn eliminate_nested_constructor_eq(
        &mut self,
        outer: &OuterElimContext<'_>,
        inner: &InnerConstructorEq<'_>,
        consequent: &PureExpr,
        prefix: Option<crate::encoder::sort_context::DerivedKind>,
    ) -> Result<Term, EncodingError> {
        let outer_short = short_constructor_name(outer.info.ctor_name);
        let inner_short = short_constructor_name(inner.ctor_name);

        debug!(
            "[trust-wp-ay] nested constructor equality elimination for \
                 {outer_short}({inner_short}(..)) on datatype {}",
            outer.info.datatype.name,
        );

        // Step 1: Extract the outer constructor's payload via native selector.
        let outer_ctor = outer
            .info
            .datatype
            .constructors
            .iter()
            .find(|c| datatype_constructor_matches(&outer.info.datatype, &c.name, outer_short));
        let Some(outer_ctor) = outer_ctor else {
            return Err(EncodingError::solver_error(format!(
                "nested ctor elim: outer constructor {outer_short} not found in {}",
                outer.info.datatype.name,
            )));
        };
        let Some(outer_field) = outer_ctor.fields.get(inner.outer_field_index) else {
            return Err(EncodingError::solver_error(format!(
                "nested ctor elim: field index {} out of range for {outer_short}",
                inner.outer_field_index,
            )));
        };
        let payload = self
            .solver
            .try_datatype_selector(
                &outer_field.name,
                outer.scrutinee_term,
                outer_field.sort.clone(),
            )
            .map_err(|e| {
                EncodingError::solver_error(format!(
                    "nested ctor elim: outer selector {}: {e}",
                    outer_field.name,
                ))
            })?;

        // Step 2: Apply the inner constructor tester on the payload.
        // Use native tester if the payload has a Datatype sort matching the
        // inner datatype. Otherwise fall back to UF testers (is_some, is_ok).
        let payload_sort = self.solver.get_sort(payload);
        let inner_actual = datatype_constructor_name(&inner.datatype, inner_short);
        let inner_tester =
            if let Ok(tester) = self.solver.try_datatype_tester(&inner_actual, payload) {
                tester
            } else {
                // Fall back to UF-model tester.
                self.encode_constructor_test(inner.ctor_name, payload, Some(&inner.datatype))?
            };

        // Combined guard: outer_tester AND inner_tester.
        let guard = self.solver.and(outer.outer_tester, inner_tester);

        // Step 3: Bind quantifier variables to inner selector results.
        if inner.var_field_map.is_empty() {
            // Nullary inner constructor (e.g., None) — no variable bindings needed.
            let consequent_term = self.encode_pure_impl(consequent, prefix)?;
            return Ok(self.solver.implies(guard, consequent_term));
        }

        let inner_ctor_decl = inner
            .datatype
            .constructors
            .iter()
            .find(|c| datatype_constructor_matches(&inner.datatype, &c.name, inner_short));

        #[allow(clippy::type_complexity)]
        let mut old_bindings: Vec<(&str, Option<Term>, Option<(String, Option<Term>)>)> =
            Vec::with_capacity(inner.var_field_map.len());

        for &(qvar, field_idx) in &inner.var_field_map {
            // Try native selector first (when payload is Datatype-sorted and
            // inner constructor has field metadata).
            let accessor_term = if let Some(inner_ctor) = inner_ctor_decl {
                if let Some(field) = inner_ctor.fields.get(field_idx) {
                    self.solver
                        .try_datatype_selector(&field.name, payload, field.sort.clone())
                        .ok()
                } else {
                    None
                }
            } else {
                None
            };
            // Fall back to UF accessor (spec_unwrap for Some/Ok, result_err_error for Err).
            let accessor_term = if let Some(term) = accessor_term {
                term
            } else {
                let accessor_name = match inner_short {
                    "Some" | "Ok" => "spec_unwrap",
                    "Err" => "result_err_error",
                    _ => {
                        return Err(EncodingError::solver_error(format!(
                            "nested ctor elim: no UF accessor for inner constructor {inner_short}"
                        )));
                    }
                };
                let accessor = self.get_or_declare_accessor_for_sorts(
                    accessor_name,
                    &payload_sort,
                    &Sort::Int,
                );
                self.safe_apply("nested_ctor_elim_accessor", &accessor, &[payload])?
            };

            let old_binding = self.insert_var(qvar.to_string(), accessor_term);
            let old_prefixed = if let Some(kind) = prefix {
                let prefixed = kind.format_name(qvar);
                if prefixed == qvar {
                    None
                } else {
                    Some((prefixed.clone(), self.insert_var(prefixed, accessor_term)))
                }
            } else {
                None
            };
            old_bindings.push((qvar, old_binding, old_prefixed));
        }

        // Mark substituted variables as quantifier-bound for collapse.
        for &(qvar, _) in &inner.var_field_map {
            self.bind_quantifier_var(qvar.to_string());
        }

        let consequent_term = self.encode_pure_impl(consequent, prefix);

        for &(qvar, _) in &inner.var_field_map {
            self.unbind_quantifier_var(qvar);
        }
        for (qvar, old_binding, old_prefixed) in old_bindings.into_iter().rev() {
            if let Some((name, old)) = old_prefixed {
                self.restore_var(&name, old);
            }
            self.restore_var(qvar, old_binding);
        }

        let consequent_term = consequent_term?;
        Ok(self.solver.implies(guard, consequent_term))
    }

    /// Pre-declare stdlib datatypes required for nested constructor equality
    /// elimination.
    ///
    /// Scans the quantifier body for nested constructor patterns like
    /// `OwnResult::Ok(Some(t))` where the inner constructor (`Some`) maps to a
    /// stdlib datatype (`OptionInt`) that may not yet be declared. Without
    /// pre-declaration, `detect_constructor_eq` cannot look up the inner
    /// constructor's datatype via `constructor_datatype`, causing the nested
    /// pattern to go unrecognized. This forces a ay `forall` quantifier that
    /// requires multi-round E-matching, which ay-dpll cannot handle. (#1296)
    ///
    /// This method is intentionally conservative: it only declares datatypes for
    /// inner constructors that are recognized stdlib names (`Some`, `None`, `Ok`,
    /// `Err`). User-defined nested constructors are not affected — they must be
    /// declared through the normal ADT registration path.
    pub(in crate::encoder) fn ensure_nested_ctor_stdlib_datatypes(
        &mut self,
        kind: QuantifierKind,
        body: &PureExpr,
        qvars: &[&str],
    ) {
        // Extract the equality expression from the body.
        // For Forall: body is `guard ==> consequent`, check guard.
        // For Exists: body is the bare equality.
        let eq_expr = match body {
            PureExpr::BinOp(lhs, BinOp::Implies, _) => lhs.as_ref(),
            _ if kind == QuantifierKind::Forall => return,
            _ => body,
        };

        // Look for `Eq(something, LogicFnCall(outer, [LogicFnCall(inner, ...)]))`
        // or the reversed form.
        let PureExpr::BinOp(left, BinOp::Eq, right) = eq_expr else {
            return;
        };

        // Check both sides for nested constructor patterns.
        for side in [left.as_ref(), right.as_ref()] {
            self.try_predeclare_nested_stdlib_dt(side, qvars);
        }
    }

    /// Check a single expression for a nested constructor pattern and
    /// pre-declare any undeclared stdlib datatypes found in the inner position.
    fn try_predeclare_nested_stdlib_dt(&mut self, expr: &PureExpr, _qvars: &[&str]) {
        let PureExpr::LogicFnCall {
            name: outer_name,
            args: outer_args,
        } = expr
        else {
            return;
        };

        // Only handle single-arg outer constructors (targeted optimization).
        if outer_args.len() != 1 {
            return;
        }

        // The single arg must be a constructor call (the inner constructor).
        let inner_arg = &outer_args[0];
        let inner_name = match inner_arg {
            PureExpr::LogicFnCall { name, .. } => name.as_str(),
            // Nullary constructor appearing as Var (e.g., None).
            PureExpr::Var(name, _) => name.as_str(),
            _ => return,
        };

        // Check if the inner constructor maps to a stdlib datatype.
        let Some(target) = stdlib_constructor_target(inner_name) else {
            return;
        };

        // If the datatype is already declared, nothing to do.
        let dt = target.datatype();
        if self.has_datatype_decl(&dt.name) {
            return;
        }

        // Also check the outer constructor — it must be recognizable as a
        // constructor (either already declared or a stdlib name). We only
        // pre-declare the *inner* datatype; the outer must come from the
        // normal ADT pipeline (e.g., OwnResult declared via adt_decls).
        // If the outer isn't declared either, nested elimination won't work
        // regardless, so skip to avoid unnecessary declarations.
        if self.constructor_datatype(outer_name).is_none()
            && stdlib_constructor_target(outer_name).is_none()
        {
            return;
        }

        if crate::trust_wp_debug_enabled() {
            eprintln!(
                "[trust-wp-ay] pre-declaring stdlib datatype {} for nested constructor \
                 pattern {outer_name}({inner_name}(...)) (#1296)",
                dt.name,
            );
        }

        self.ensure_datatype_declared(&dt);
    }
}
