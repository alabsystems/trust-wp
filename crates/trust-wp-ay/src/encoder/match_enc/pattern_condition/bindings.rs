// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::borrow::Cow;

use ay_dpll::api::{DatatypeSort, FuncDecl, Sort, Term};
use trust_wp_core::formula::{internal::tuple_lowering::tuple_field_logic_fn_name, Pattern};

use super::super::{
    datatype_constructor_matches, datatype_constructor_name, short_constructor_name,
    stdlib_constructor_target, SwitchTarget,
};
use crate::{
    encoder::{
        infer_expr_sort,
        sort_context::{apply_name_prefix, DerivedKind},
        AYEncoder,
    },
    error::EncodingError,
};

impl AYEncoder {
    /// #prophecy-slots (Fix B M1): the `ambiguous_stdlib_option` hazard is a
    /// LITERAL constructor-name collision — more than one declared `Option*`
    /// family whose constructor is literally named `"Some"` would confuse
    /// solver-level constructor→datatype resolution, so the pattern lane must
    /// fall back to the `spec_unwrap` UF accessor.
    ///
    /// Specialized families never collide: every non-`OptionInt` Option
    /// family names its constructor `{family}__Some`
    /// (`option_constructor_name_for_datatype`). The reverse index ALSO
    /// carries their LOGICAL `"Some"` alias for lookup
    /// (`insert_datatype`/`logical_constructor_alias_for_datatype`), which is
    /// not a collision. The previous census counted those alias hits, so the
    /// moment any specialized family entered scope the guard forced the UF
    /// fallback and nullified the native-selector lane — the exact failure
    /// the M0 retire-on-signal pin in `mut_ref_sort.rs` was written to catch.
    pub(crate) fn stdlib_option_some_literally_ambiguous(&self) -> bool {
        self.datatypes_for_constructor("Some")
            .filter(|dt| dt.name.starts_with("Option"))
            .filter(|dt| dt.constructors.iter().any(|ctor| ctor.name == "Some"))
            .take(2)
            .count()
            > 1
    }

    /// #prophecy-slots (Fix B M1): does the scrutinee's OWN sort resolve to a
    /// declared datatype whose payload field for `ctor_name` is the mutref
    /// record carrier? Used to refuse the Int-ranged UF accessor fallback for
    /// carrier payloads (a silent prophecy-slot drop) instead of letting the
    /// UF lane diverge from the native lane without a counter.
    fn scrutinee_payload_is_mut_ref_carrier(&self, scrutinee: Term, ctor_name: &str) -> bool {
        let dt = match self.solver.get_sort(scrutinee) {
            Sort::Datatype(dt) => Some(dt),
            Sort::Uninterpreted(name) => self.get_datatype_decl(&name).cloned(),
            _ => None,
        };
        let Some(dt) = dt else {
            return false;
        };
        Self::constructor_payload_selector(&dt, ctor_name).is_some_and(|(_, sort)| {
            matches!(sort, Sort::Uninterpreted(name) if name.starts_with("__trust_wp_mutref::"))
        })
    }

    pub(in crate::encoder::match_enc) fn selector_datatype_for_scrutinee(
        &self,
        scrutinee: Term,
        fallback: &DatatypeSort,
        ctor_name: &str,
    ) -> DatatypeSort {
        let actual_sort = self.solver.get_sort(scrutinee);
        match actual_sort {
            Sort::Datatype(actual) if Self::datatype_has_constructor(&actual, ctor_name) => actual,
            Sort::Uninterpreted(name) => self
                .get_datatype_decl(&name)
                .filter(|dt| Self::datatype_has_constructor(dt, ctor_name))
                .cloned()
                .unwrap_or_else(|| fallback.clone()),
            _ => fallback.clone(),
        }
    }

    fn datatype_has_constructor(datatype: &DatatypeSort, ctor_name: &str) -> bool {
        datatype
            .constructors
            .iter()
            .any(|ctor| datatype_constructor_matches(datatype, &ctor.name, ctor_name))
    }

    /// Collect all variable bindings introduced by a pattern.
    ///
    /// Returns a list of `(name, term, sort)` triples. For simple patterns this
    /// is 0 or 1 bindings; for tuple patterns it can be multiple (one per
    /// element).
    ///
    /// Returns `Err` when a sort mismatch prevents extracting the payload term.
    /// Previously this silently returned `vec![]`, which left destructured
    /// variables as unconstrained SMT constants - a potential soundness issue
    /// (#1560).
    #[allow(clippy::too_many_lines)]
    pub(in crate::encoder) fn pattern_bindings(
        &mut self,
        scrutinee: Term,
        pattern: &Pattern,
        datatype: Option<&DatatypeSort>,
        scrutinee_sort: Option<&Sort>,
        prefix: Option<DerivedKind>,
    ) -> Result<Vec<(String, Term, Sort)>, EncodingError> {
        match pattern {
            Pattern::Alias { alias, pattern } => {
                if pattern.binds_name(alias) {
                    return Err(EncodingError::solver_error(format!(
                        "pattern_bindings: alias pattern reuses binding name {alias}"
                    )));
                }
                let scoped_name = apply_name_prefix(alias, prefix).into_owned();
                let binding_sort = scrutinee_sort
                    .cloned()
                    .unwrap_or_else(|| self.resolve_var_sort_or_int(&scoped_name));
                let mut bindings = vec![(scoped_name, scrutinee, binding_sort)];
                bindings.extend(self.pattern_bindings(
                    scrutinee,
                    pattern,
                    datatype,
                    scrutinee_sort,
                    prefix,
                )?);
                Ok(bindings)
            }
            Pattern::Binding(binding_name) => {
                let scoped_name = apply_name_prefix(binding_name, prefix).into_owned();
                // Use resolve_var_sort_or_int to check sort hints and suffix-derived
                // base sorts before falling back to Int. (#1608)
                let binding_sort = scrutinee_sort
                    .cloned()
                    .unwrap_or_else(|| self.resolve_var_sort_or_int(&scoped_name));
                Ok(vec![(scoped_name, scrutinee, binding_sort)])
            }
            Pattern::Constructor { name, inner } => {
                let declared_datatype = datatype.map(|dt| self.canonical_declared_datatype(dt));
                let selector_datatype = declared_datatype
                    .as_ref()
                    .map(|dt| self.selector_datatype_for_scrutinee(scrutinee, dt, name));
                let datatype = selector_datatype.as_ref().or(declared_datatype.as_ref());
                let Some(inner_pat) = inner.as_deref() else {
                    return Ok(vec![]);
                };

                // Multi-field constructor with native datatype: use per-field
                // selectors directly instead of a single payload accessor.
                // For `Cons(a, l)` on a DatatypeSort, this extracts each field
                // individually via `try_datatype_selector`. (#1965, #2002)
                if let Some(bindings) =
                    self.multi_field_ctor_bindings(scrutinee, name, inner_pat, datatype, prefix)?
                {
                    return Ok(bindings);
                }

                // Extract the constructor payload term.
                // Prefer native datatype selector; fall back to UF accessor.
                let payload_term = if let Some(dt) = datatype {
                    if let Some((selector_name, selector_sort)) =
                        Self::constructor_payload_selector(dt, name)
                    {
                        let short = short_constructor_name(name);
                        let ambiguous_stdlib_option = short == "Some"
                            && dt.name.starts_with("Option")
                            && self.stdlib_option_some_literally_ambiguous();
                        let expected_sort = Sort::Datatype(dt.clone()).as_term_sort();
                        let actual_sort = self.solver.get_sort(scrutinee);
                        if actual_sort == expected_sort && !ambiguous_stdlib_option {
                            // Use try_ variant to avoid ICE on sort mismatch (#1532)
                            self.solver
                                .try_datatype_selector(
                                    selector_name,
                                    scrutinee,
                                    selector_sort.clone(),
                                )
                                .map_err(|e| {
                                    EncodingError::solver_error(format!(
                                        "pattern_bindings: datatype selector sort mismatch \
                                         for constructor {name}: {e}"
                                    ))
                                })?
                        } else {
                            let accessor_name: Cow<'_, str> = match short {
                                "Some" | "Ok" => Cow::Borrowed("spec_unwrap"),
                                "Err" => Cow::Borrowed("result_err_error"),
                                _ => Cow::Owned(format!("payload_{}", short.to_lowercase())),
                            };
                            let domain_sort =
                                self.pattern_accessor_domain_sort(scrutinee, scrutinee_sort);
                            let accessor = self.get_or_declare_accessor_for_sorts(
                                &accessor_name,
                                &domain_sort,
                                &selector_sort,
                            );
                            self.safe_apply("pattern_accessor", &accessor, &[scrutinee])?
                        }
                    } else {
                        // No selector: constructor has 0 or 2+ fields.
                        // Multi-field was already handled above; if the constructor
                        // is nullary, an inner pattern like Tag(x) is invalid — fail
                        // closed rather than synthesizing a phantom payload (#2300).
                        let short = short_constructor_name(name);
                        if dt.constructors.iter().any(|c| {
                            datatype_constructor_matches(dt, &c.name, name) && c.fields.is_empty()
                        }) {
                            return Err(EncodingError::solver_error(format!(
                                "pattern_bindings: constructor pattern {name} has no payload \
                                 (zero-field constructor) but pattern expects a binding"
                            )));
                        }
                        let generic_name = format!("payload_{}", short.to_lowercase());
                        let domain_sort =
                            self.pattern_accessor_domain_sort(scrutinee, scrutinee_sort);
                        let accessor = self.get_or_declare_accessor_for_sorts(
                            &generic_name,
                            &domain_sort,
                            &Sort::Int,
                        );
                        self.safe_apply("pattern_accessor", &accessor, &[scrutinee])?
                    }
                } else {
                    // UF fallback: use spec_unwrap for Ok/Some, result_err_error for Err,
                    // generic payload_<name> for custom constructors (#1681, #1787).
                    let short = short_constructor_name(name);
                    // #prophecy-slots (Fix B M1): when the scrutinee is
                    // actually sorted at a declared datatype whose matching
                    // payload field is a mutref record carrier, minting an
                    // Int-ranged UF accessor would silently drop the
                    // prophecy slot — the native lane and the UF lane would
                    // disagree with no counter firing. Refuse loudly instead
                    // (fail-closed; costs an honest error, never a proof).
                    if self.scrutinee_payload_is_mut_ref_carrier(scrutinee, name) {
                        return Err(EncodingError::solver_error(format!(
                            "pattern_bindings: constructor {name} payload is a mutref \
                             prophecy carrier but no native datatype context reached the \
                             pattern lane; refusing the Int-ranged UF accessor fallback \
                             (#prophecy-slots)"
                        )));
                    }
                    let accessor_name: Cow<'_, str> = match short {
                        "Some" | "Ok" => Cow::Borrowed("spec_unwrap"),
                        "Err" => Cow::Borrowed("result_err_error"),
                        _ => Cow::Owned(format!("payload_{}", short.to_lowercase())),
                    };
                    let domain_sort = self.pattern_accessor_domain_sort(scrutinee, scrutinee_sort);
                    let accessor = self.get_or_declare_accessor_for_sorts(
                        &accessor_name,
                        &domain_sort,
                        &Sort::Int,
                    );
                    // Use safe_apply to avoid ICE on sort mismatch (#1532)
                    self.safe_apply("pattern_accessor", &accessor, &[scrutinee])?
                };
                // Third-selector bridge: when the payload was reached through
                // the generic UF decomposition (`payload_<ctor>` +
                // `__trust_wp_tuple_get_i`) but the scrutinee's sort is a
                // declared datatype with a matching multi-field constructor,
                // connect each positional getter to the native field selector.
                self.bridge_uf_payload_tuple_getters_to_native_selectors(
                    scrutinee,
                    payload_term,
                    name,
                    inner_pat,
                    prefix,
                );
                // #prophecy-slots (Fix B M3): the SINGLE-field analogue — the
                // carrier `Option` payload reached positionally by the driver's
                // substitution lane vs natively by this one.
                self.bridge_carrier_option_payload_getter_to_native_selector(scrutinee);

                // Recurse into the inner pattern (handles Binding, Tuple,
                // nested Constructor, Wildcard, and Literal).
                let payload_sort = if let Some(dt) = datatype {
                    Self::constructor_payload_selector(dt, name).map(|(_, sort)| sort.clone())
                } else {
                    Some(Sort::Int)
                };
                // When the payload sort is a known datatype, pass that datatype
                // context to the inner recursion so nested constructor patterns
                // (e.g., `OwnResult::Ok(Some(x))`) use native selectors instead
                // of UF accessors. Without this, `x` would be extracted via an
                // unconstrained UF `spec_unwrap` instead of the native
                // `option_some_value` selector, disconnecting the binding from
                // the actual datatype value. (#1296)
                let inner_datatype = payload_sort.as_ref().and_then(|sort| match sort {
                    Sort::Datatype(dt) => Some(dt.clone()),
                    Sort::Uninterpreted(name) => self.get_datatype_decl(name).cloned(),
                    _ => None,
                });
                self.pattern_bindings(
                    payload_term,
                    inner_pat,
                    inner_datatype.as_ref(),
                    payload_sort.as_ref(),
                    prefix,
                )
            }
            Pattern::Tuple(elements) => {
                let mut bindings = Vec::new();
                let domain_sort = scrutinee_sort
                    .cloned()
                    .unwrap_or_else(|| self.solver.get_sort(scrutinee));
                // #prophecy-slots (Fix B M2): a CARRIER TUPLE scrutinee names
                // its element sorts. Those are AUTHORITATIVE — pattern-shape
                // inference has no way to see through the punned `Tuple{n}`
                // sort and would hand back `Int`, which is exactly the
                // prophecy-slot erasure this milestone removes. Elements
                // recorded as `legacy` keep the inference lane unchanged.
                let carrier_elements =
                    crate::encoder::sort_context::sort_mapping::carrier_tuple_element_sorts(
                        &domain_sort.as_term_sort(),
                    )
                    .filter(|decoded| decoded.len() == elements.len());
                for (i, sub_pattern) in elements.iter().enumerate() {
                    let getter_name = tuple_field_logic_fn_name(i);
                    let declared_elem_sort = carrier_elements
                        .as_ref()
                        .and_then(|decoded| decoded[i].clone())
                        .map(|sort| self.sort_from_expr_sort(sort));
                    let elem_sort = match declared_elem_sort {
                        Some(sort) => sort,
                        None => self.infer_tuple_element_sort_with_context(
                            sub_pattern,
                            prefix,
                            &getter_name,
                            &domain_sort,
                        ),
                    };
                    let elem_datatype = match &elem_sort {
                        Sort::Datatype(dt) => Some(dt),
                        _ => None,
                    };
                    let getter =
                        self.get_or_declare_tuple_getter(&getter_name, &domain_sort, &elem_sort);
                    // Use safe_apply for consistency with Constructor branch (#1560)
                    let elem_term = self.safe_apply("tuple_getter", &getter, &[scrutinee])?;
                    bindings.extend(self.pattern_bindings(
                        elem_term,
                        sub_pattern,
                        elem_datatype,
                        Some(&elem_sort),
                        prefix,
                    )?);
                }
                Ok(bindings)
            }
            Pattern::Wildcard | Pattern::Literal(_) => Ok(vec![]),
            // Pattern is #[non_exhaustive]; required for cross-crate match.
            #[allow(unreachable_patterns, clippy::match_wildcard_for_single_variants)]
            _ => Ok(vec![]),
        }
    }

    /// Get or declare a tuple element getter function (`__trust_wp_tuple_get_N`).
    ///
    /// Historical Int-carrier tuple matches still use the legacy spec-function
    /// family. The declaration helper must nevertheless check the complete
    /// signature: different tuple shapes can lower to the same Int carrier
    /// while requiring different element sorts. Non-Int carriers use a
    /// signature-keyed logic-function declaration so tuple-pattern matching
    /// shares the same symbol family as direct tuple getter calls and tuple
    /// destructor axioms. (#994, #1296)
    pub(in crate::encoder::match_enc) fn get_or_declare_tuple_getter(
        &mut self,
        name: &str,
        domain_sort: &Sort,
        range_sort: &Sort,
    ) -> FuncDecl {
        let domain_sort = domain_sort.as_term_sort();
        let range_sort = range_sort.as_term_sort();

        if domain_sort == Sort::Int {
            return self.get_or_declare_spec_fn(
                name,
                std::slice::from_ref(&domain_sort),
                range_sort,
            );
        }

        let smt_name = trust_wp_core::logic::logic_fn_smt_name(name);
        if let Some(existing) = self.logic_func_decl_cloned(&smt_name) {
            if existing.domain() == [domain_sort.clone()] && existing.range() == &range_sort {
                return existing;
            }
        }

        let decl_key =
            Self::placeholder_smt_name(&smt_name, std::slice::from_ref(&domain_sort), &range_sort);
        self.get_or_declare_logic_func(&decl_key, std::slice::from_ref(&domain_sort), range_sort)
    }

    /// Bridge the generic UF payload decomposition of a multi-field
    /// constructor pattern to the native datatype field selectors.
    ///
    /// A multi-field constructor arm (e.g. `Node(tl, a, tr)`) reaches its
    /// bindings through TWO unrelated encodings depending on context: the
    /// native per-field datatype selectors (`tree_node_i(scrut)`) or, when the
    /// match datatype is not resolved at that call site, a generic payload
    /// accessor plus positional getters
    /// (`__trust_wp_tuple_get_i(payload_node(scrut))`). Facts produced through
    /// one family (e.g. a recursive logic fn's one-level unfold at
    /// `enum_payload_get_0(self)`) are otherwise unconnectable to facts
    /// produced through the other (the unfold at `self` itself), so the solver
    /// gets stuck relating `sum(self)` to `sum(tl)`.
    ///
    /// For an `is-<Ctor>(scrut)` receiver both accessors denote the SAME field
    /// value, so emit the guarded ground equality per field `i`:
    ///   `is-<Ctor>(scrut) ==> __trust_wp_tuple_get_i(payload_<ctor>(scrut)) == <field_i>(scrut)`.
    ///
    /// CARDINAL SOUNDNESS: the equality is a true consequence of the intended
    /// interpretation (both sides read field `i` of the same constructor
    /// payload), gated to receivers whose ay sort IS the declared datatype and
    /// to the constructor actually being matched (`is-<Ctor>` guard, vacuous on
    /// other variants). Positional getters whose inferred element sort differs
    /// from the native field sort are skipped — the two accessors would denote
    /// values in different carriers. Ground-only: never emitted inside a
    /// quantifier body, where `scrut` could mention bound variables.
    fn bridge_uf_payload_tuple_getters_to_native_selectors(
        &mut self,
        scrutinee: Term,
        payload_term: Term,
        ctor_name: &str,
        inner_pat: &Pattern,
        prefix: Option<DerivedKind>,
    ) {
        if self.quantifier_state.quantifier_depth() != 0 {
            return;
        }
        let Pattern::Tuple(elements) = inner_pat else {
            return;
        };
        // Resolve the scrutinee's declared datatype from its actual ay sort.
        let scrutinee_sort = self.solver.get_sort(scrutinee);
        let dt = match &scrutinee_sort {
            Sort::Datatype(dt) => dt.clone(),
            Sort::Uninterpreted(name) => match self.get_datatype_decl(name) {
                Some(dt) => dt.clone(),
                None => return,
            },
            _ => return,
        };
        let Some(ctor) = dt
            .constructors
            .iter()
            .find(|ctor| datatype_constructor_matches(&dt, &ctor.name, ctor_name))
        else {
            return;
        };
        if ctor.fields.len() < 2 || ctor.fields.len() != elements.len() {
            return;
        }
        let fields = ctor.fields.clone();
        let short = short_constructor_name(ctor_name).to_string();
        let Ok(tester) = self.solver.try_datatype_tester(&short, scrutinee) else {
            return;
        };
        let domain_sort = self.solver.get_sort(payload_term);
        for (i, field) in fields.iter().enumerate() {
            let Ok(native) =
                self.solver
                    .try_datatype_selector(&field.name, scrutinee, field.sort.clone())
            else {
                continue;
            };
            let getter_name = tuple_field_logic_fn_name(i);
            let elem_sort = self.infer_tuple_element_sort_with_context(
                &elements[i],
                prefix,
                &getter_name,
                &domain_sort,
            );
            if elem_sort.as_term_sort() != field.sort.as_term_sort() {
                continue;
            }
            let getter = self.get_or_declare_tuple_getter(&getter_name, &domain_sort, &elem_sort);
            let Ok(tuple_get) =
                self.safe_apply("payload_tuple_get_bridge", &getter, &[payload_term])
            else {
                continue;
            };
            let eq = self.eq_term(tuple_get, native);
            let guarded = self.solver.implies(tester, eq);
            self.assert_solver_term("adt_payload_tuple_get_bridge", guarded);
        }
    }

    /// #prophecy-slots (Fix B M3): bridge the carrier `Option` payload's
    /// POSITIONAL spelling to its NATIVE datatype selector.
    ///
    /// M2 lowered `Option<(&mut T, ..)>` onto a real prophecy carrier, but it
    /// left the two lanes that reach the payload UNCONNECTED, and the
    /// take_first_mut replay shows both of them side by side:
    ///
    /// * the PREMISE lane (this file) binds the arm through the native
    ///   selector — `<family>_some_value(call) : <carrier>`;
    /// * the GOAL lane (the driver's substitution pipeline) models the same
    ///   projection as field 0 of the enclosing `Option` and reaches it
    ///   through a positional getter —
    ///   `__trust_wp_tuple_get_0(call) : <carrier>`
    ///   (declared by `prophecy_carrier_getter_return_sort`).
    ///
    /// Nothing relates the two symbols, so `^r` proved on one spelling says
    /// nothing about `^r` asserted on the other and the obligation dies with a
    /// counterexample that assigns the free getter an unrelated carrier. This
    /// is the single-field analogue of
    /// [`Self::bridge_uf_payload_tuple_getters_to_native_selectors`] and
    /// follows it exactly: an `is-<Ctor>`-guarded GROUND equality.
    ///
    /// CARDINAL SOUNDNESS: this is a definitional identity between two
    /// spellings of ONE projection, not new information. In the intended
    /// interpretation `__trust_wp_tuple_get_0` applied to a carrier `Option`
    /// receiver DENOTES that receiver's `Some` payload — that is the only
    /// meaning trust-wp ever gives it, and it is precisely the meaning
    /// `prophecy_carrier_getter_return_sort` asserts when it types the getter
    /// at the payload sort. The native selector denotes the same payload. The
    /// equality is therefore true in the intended model, so adding it cannot
    /// make a false obligation provable; the datatype already licenses
    /// everything the equation says. Guards, all fail-closed:
    ///
    /// * ground only — never inside a quantifier body, where the receiver
    ///   could mention bound variables (precedent's guard);
    /// * the receiver's own ay sort must resolve to a DECLARED datatype
    ///   carrying a single-field `Some`;
    /// * the getter's range is taken from `prophecy_carrier_getter_return_sort`
    ///   itself, so the symbol bridged is byte-identical to the one the goal
    ///   lane mints — and that function only answers for the M1/M2
    ///   prophecy-carrier families, so `OptionInt` and every other legacy
    ///   family are untouched;
    /// * the tester is the datatype's own, so the equation is vacuous on
    ///   `None` — it never asserts anything about a term that denotes nothing.
    fn bridge_carrier_option_payload_getter_to_native_selector(&mut self, scrutinee: Term) {
        if self.quantifier_state.quantifier_depth() != 0 {
            return;
        }
        let scrutinee_sort = self.solver.get_sort(scrutinee);
        let dt = match &scrutinee_sort {
            Sort::Datatype(dt) => dt.clone(),
            Sort::Uninterpreted(name) => match self.get_datatype_decl(name) {
                Some(dt) => dt.clone(),
                None => return,
            },
            _ => return,
        };
        // Only the prophecy-carrier `Option` families the goal lane spells
        // positionally. `None` here means the driver never types a
        // `__trust_wp_tuple_get_0` at this receiver sort, so there is no
        // second lane to bridge.
        let Some(getter_range) =
            self.prophecy_carrier_getter_return_sort(0, std::slice::from_ref(&scrutinee_sort))
        else {
            return;
        };
        let Some((selector_name, payload_sort)) = Self::constructor_payload_selector(&dt, "Some")
            .map(|(name, sort)| (name.to_string(), sort.clone()))
        else {
            return;
        };
        if getter_range.as_term_sort() != payload_sort.as_term_sort() {
            return;
        }
        let ctor_name = datatype_constructor_name(&dt, "Some");
        let Ok(tester) = self.solver.try_datatype_tester(&ctor_name, scrutinee) else {
            return;
        };
        let Ok(native) =
            self.solver
                .try_datatype_selector(&selector_name, scrutinee, payload_sort.clone())
        else {
            return;
        };
        let getter_name = tuple_field_logic_fn_name(0);
        let getter = self.get_or_declare_tuple_getter(&getter_name, &scrutinee_sort, &getter_range);
        let Ok(tuple_get) = self.safe_apply(
            "carrier_option_payload_getter_bridge",
            &getter,
            &[scrutinee],
        ) else {
            return;
        };
        let eq = self.eq_term(tuple_get, native);
        let guarded = self.solver.implies(tester, eq);
        self.assert_solver_term("carrier_option_payload_getter_bridge", guarded);
    }

    pub(super) fn infer_tuple_element_sort_with_context(
        &mut self,
        sub_pattern: &Pattern,
        prefix: Option<DerivedKind>,
        getter_name: &str,
        domain_sort: &Sort,
    ) -> Sort {
        let inferred = self.infer_tuple_element_sort(sub_pattern, prefix);
        if !Self::tuple_element_sort_accepts_context(sub_pattern, &inferred) {
            return inferred;
        }
        self.established_tuple_element_sort(getter_name, domain_sort, sub_pattern, &inferred)
            .unwrap_or(inferred)
    }

    fn tuple_element_sort_accepts_context(sub_pattern: &Pattern, inferred: &Sort) -> bool {
        match sub_pattern {
            Pattern::Alias { pattern, .. } => {
                Self::tuple_element_sort_accepts_context(pattern, inferred)
            }
            Pattern::Wildcard => true,
            Pattern::Constructor { name, inner: None } => {
                *inferred == Sort::Int
                    || matches!(
                        stdlib_constructor_target(name),
                        Some(SwitchTarget::OptionInt)
                    )
            }
            _ => false,
        }
    }

    fn established_tuple_element_sort(
        &self,
        getter_name: &str,
        domain_sort: &Sort,
        sub_pattern: &Pattern,
        inferred_sort: &Sort,
    ) -> Option<Sort> {
        let smt_name = trust_wp_core::logic::logic_fn_smt_name(getter_name);
        let domain_sort = domain_sort.as_term_sort();
        let inferred_term_sort = inferred_sort.as_term_sort();
        let mut better_candidates = Vec::new();

        for (decl_name, decl) in self.logic_funcs_iter() {
            if !Self::tuple_getter_decl_matches(decl_name, &smt_name) {
                continue;
            }
            if decl.domain() != [domain_sort.clone()] {
                continue;
            }
            let candidate = self.canonical_tuple_element_range_sort(decl.range());
            if candidate.as_term_sort() == inferred_term_sort {
                continue;
            }
            if !self.tuple_element_sort_matches_pattern(&candidate, sub_pattern) {
                continue;
            }
            if !better_candidates
                .iter()
                .any(|existing: &Sort| existing.as_term_sort() == candidate.as_term_sort())
            {
                better_candidates.push(candidate);
            }
        }

        match better_candidates.as_slice() {
            [candidate] => Some(candidate.clone()),
            _ => None,
        }
    }

    fn tuple_getter_decl_matches(decl_name: &str, smt_name: &str) -> bool {
        decl_name == smt_name
            || decl_name
                .strip_prefix(smt_name)
                .is_some_and(|suffix| suffix.starts_with("__placeholder_"))
    }

    fn canonical_tuple_element_range_sort(&self, sort: &Sort) -> Sort {
        match sort {
            Sort::Uninterpreted(name) => self
                .get_datatype_decl(name)
                .map_or_else(|| sort.clone(), |dt| Sort::Datatype(dt.clone())),
            _ => sort.clone(),
        }
    }

    fn tuple_element_sort_matches_pattern(&self, sort: &Sort, pattern: &Pattern) -> bool {
        match pattern {
            Pattern::Alias { pattern, .. } => {
                self.tuple_element_sort_matches_pattern(sort, pattern)
            }
            Pattern::Constructor { name, inner } => {
                let Some(datatype) = self.tuple_element_datatype(sort) else {
                    return false;
                };
                datatype
                    .constructors
                    .iter()
                    .find(|ctor| datatype_constructor_matches(&datatype, &ctor.name, name))
                    .is_some_and(|ctor| match inner.as_deref() {
                        None => ctor.fields.is_empty(),
                        Some(Pattern::Tuple(elements)) => ctor.fields.len() == elements.len(),
                        Some(_) => ctor.fields.len() == 1,
                    })
            }
            _ => true,
        }
    }

    fn tuple_element_datatype(&self, sort: &Sort) -> Option<DatatypeSort> {
        match sort {
            Sort::Datatype(dt) => Some(dt.clone()),
            Sort::Uninterpreted(name) => self.get_datatype_decl(name).cloned(),
            _ => None,
        }
    }

    /// Infer the ay sort for a tuple element from its sub-pattern.
    ///
    /// Returns `Sort::Bool` if the sub-pattern is a boolean literal, or checks
    /// the ExprSort annotation on binding variables. Falls back to `Sort::Int`
    /// (the historical default) when no sort information is available. (#994)
    pub(super) fn infer_tuple_element_sort(
        &mut self,
        sub_pattern: &Pattern,
        prefix: Option<DerivedKind>,
    ) -> Sort {
        match sub_pattern {
            Pattern::Alias { pattern, .. } => self.infer_tuple_element_sort(pattern, prefix),
            Pattern::Literal(expr) => infer_expr_sort(expr),
            Pattern::Binding(name) => {
                let scoped = apply_name_prefix(name, prefix).into_owned();
                self.resolve_var_sort_or_int(&scoped)
            }
            Pattern::Constructor { name, inner } => {
                if matches!(
                    stdlib_constructor_target(name),
                    Some(SwitchTarget::OptionInt)
                ) {
                    if short_constructor_name(name) == "None" {
                        let datatype = SwitchTarget::OptionInt.datatype();
                        self.ensure_datatype_declared(&datatype);
                        return Sort::Datatype(datatype);
                    }
                    let Some(payload_sort) = inner
                        .as_deref()
                        .and_then(|pat| self.infer_pattern_payload_sort(pat, prefix))
                    else {
                        return Sort::Int;
                    };
                    if payload_sort == Sort::Int {
                        return Sort::Int;
                    }
                    let datatype = self.stdlib_option_datatype_for_payload_sort(payload_sort);
                    self.ensure_datatype_declared(&datatype);
                    return Sort::Datatype(datatype);
                }
                self.constructor_datatype(name)
                    .map_or(Sort::Int, Sort::Datatype)
            }
            _ => Sort::Int,
        }
    }

    fn infer_pattern_payload_sort(
        &mut self,
        pattern: &Pattern,
        prefix: Option<DerivedKind>,
    ) -> Option<Sort> {
        match pattern {
            Pattern::Alias { pattern, .. } => self.infer_pattern_payload_sort(pattern, prefix),
            // A `Pattern::Binding` inside a constructor pattern (e.g. the `x`
            // in `Some(x)`) introduces a fresh, arm-scoped binding for the
            // constructor's payload. The binding does NOT inherit the sort
            // of any outer **variable** that happens to share its name.
            // Reading the full var-sort registry here would return the outer
            // scope's sort whenever the binding name shadows an enclosing
            // parameter (e.g. `fn f(x: (Option<i32>, Option<i32>)) { match x
            // { (Some(x), None) | (None, Some(x)) => x, _ => 1 } }`). The
            // outer `x: Tuple2` would leak into payload-sort inference,
            // producing `Option<Tuple2>` getters that mismatch the actual
            // `Option<i32>` element sort. (#5 or_pat shadowing bug)
            //
            // Sort *hints* (registered via `record_sort_hint`) are still
            // honoured because they describe the EXPECTED payload sort for
            // that binding name, not an outer variable's actual sort.
            Pattern::Binding(name) => {
                let scoped = apply_name_prefix(name, prefix).into_owned();
                let hint = self.sort_hint_cloned(&scoped)?;
                let sort = self.sort_from_expr_sort(hint);
                (sort != Sort::Int).then_some(sort)
            }
            Pattern::Literal(expr) => Some(infer_expr_sort(expr)),
            Pattern::Constructor { name, inner } => {
                if matches!(
                    stdlib_constructor_target(name),
                    Some(SwitchTarget::OptionInt)
                ) {
                    let payload = inner
                        .as_deref()
                        .and_then(|pat| self.infer_pattern_payload_sort(pat, prefix))
                        .unwrap_or(Sort::Int);
                    let datatype = self.stdlib_option_datatype_for_payload_sort(payload);
                    self.ensure_datatype_declared(&datatype);
                    Some(Sort::Datatype(datatype))
                } else {
                    self.constructor_datatype(name).map(Sort::Datatype)
                }
            }
            _ => None,
        }
    }

    /// Extract bindings from a multi-field constructor using native selectors.
    /// Returns `Some(bindings)` for 2+ field constructors when the inner
    /// pattern can be mapped onto native fields; `None` to fall through to the
    /// single-payload path. (#2002)
    #[allow(clippy::type_complexity)]
    pub(super) fn multi_field_ctor_bindings(
        &mut self,
        scrutinee: Term,
        ctor_name: &str,
        inner_pat: &Pattern,
        datatype: Option<&DatatypeSort>,
        prefix: Option<DerivedKind>,
    ) -> Result<Option<Vec<(String, Term, Sort)>>, EncodingError> {
        let Some(dt) = datatype else {
            return Ok(None);
        };
        let selector_datatype = self.selector_datatype_for_scrutinee(scrutinee, dt, ctor_name);
        let Some(fields) = Self::constructor_multi_field_selectors(&selector_datatype, ctor_name)
        else {
            return Ok(None);
        };
        // Verify the scrutinee has the expected Datatype sort at the ay level.
        // When first-declaration-wins lock-in has already assigned Int (e.g.,
        // from precondition encoding before match processing), native datatype
        // selectors will fail. Fall through to UF accessor path. (#1965, #2002)
        let expected_sort = Sort::Datatype(selector_datatype.clone()).as_term_sort();
        let actual_sort = self.solver.get_sort(scrutinee);
        if actual_sort != expected_sort {
            return Ok(None);
        }

        if !matches!(inner_pat, Pattern::Tuple(_)) {
            let Some(field) = fields.first() else {
                return Ok(None);
            };
            let field_term = self
                .solver
                .try_datatype_selector(&field.name, scrutinee, field.sort.clone())
                .map_err(|e| {
                    EncodingError::solver_error(format!(
                        "multi-field selector {}.{} sort mismatch: {e}",
                        ctor_name, field.name
                    ))
                })?;
            let field_datatype = match &field.sort {
                Sort::Datatype(dt) => Some(dt.clone()),
                Sort::Uninterpreted(name) => self.get_datatype_decl(name).cloned(),
                _ => None,
            };
            return self
                .pattern_bindings(
                    field_term,
                    inner_pat,
                    field_datatype.as_ref(),
                    Some(&field.sort),
                    prefix,
                )
                .map(Some);
        }

        let Pattern::Tuple(elements) = inner_pat else {
            unreachable!("handled non-tuple multi-field constructor pattern above");
        };

        let mut bindings = Vec::new();
        for (i, sub_pattern) in elements.iter().take(fields.len()).enumerate() {
            let field = &fields[i];
            let field_term = self
                .solver
                .try_datatype_selector(&field.name, scrutinee, field.sort.clone())
                .map_err(|e| {
                    EncodingError::solver_error(format!(
                        "multi-field selector {}.{} sort mismatch: {e}",
                        ctor_name, field.name
                    ))
                })?;
            let field_datatype = match &field.sort {
                Sort::Datatype(dt) => Some(dt.clone()),
                Sort::Uninterpreted(name) => self.get_datatype_decl(name).cloned(),
                _ => None,
            };
            bindings.extend(self.pattern_bindings(
                field_term,
                sub_pattern,
                field_datatype.as_ref(),
                Some(&field.sort),
                prefix,
            )?);
        }
        Ok(Some(bindings))
    }
}
