// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Tuple constructor/destructor, native datatype payload, and unit singleton axioms.

use std::collections::HashSet;

use ay_dpll::api::{DatatypeSort, FuncDecl, Sort, Term, TermKind};

use super::super::{
    sort_context::{
        sort_coercion::{select_mutref_carrier_target, select_structural_sort_target},
        sort_inference::unit_sort,
    },
    AYEncoder,
};

/// A `Bool`-ranged projection over a payload that is NOT `Bool` has no
/// faithful defining equation.
///
/// `select_structural_sort_target(Bool, Int)` answers `Some(Bool)` (the
/// inference-fallback arm), so the sort guards in this module used to admit the
/// pair, and `eq_term(get_I(..), x)` then bridged it through the 0/1 lane as
/// `ite(get_I(..), 1, 0) = x`. Quantified over `x: Int` that is
/// `forall x. x = 0 \/ x = 1` — FALSE on its own, so every query carrying it is
/// vacuously UNSAT and every contract over it "verifies" with a genuinely
/// checkable certificate. Measured on the checked-add tuple `(u64, bool)` whose
/// constructor carried an Int flag while `get_1` was declared Bool
/// (tests/adversarial/cases/s34_field_nested_struct.rs: ay certified the
/// refutation, z3 reports the lone axiom unsat).
///
/// Only the quantified constructor/destructor axiom consulted
/// `select_structural_sort_target`; the payload and ground-instance emitters
/// in this module admit a sort mismatch only for the `Bool` payload / `Int`
/// accessor bridge, so they already refuse this pair.
///
/// The opposite direction (`Bool` payload, `Int` accessor, `ite(x, 1, 0)`)
/// only constrains the uninterpreted accessor and stays allowed. Skipping
/// leaves the accessor uninterpreted on this family: strictly weaker, sound.
fn bool_accessor_over_non_bool_payload(accessor_range: &Sort, payload_sort: &Sort) -> bool {
    *accessor_range == Sort::Bool && *payload_sort != Sort::Bool
}

impl AYEncoder {
    /// Assert tuple constructor/destructor axioms.
    ///
    /// When both `__trust_wp_tupleN` (constructor) and `__trust_wp_tuple_get_I` (destructor)
    /// symbols have been declared during encoding, this asserts the defining axioms:
    ///
    /// ```text
    /// forall x0 x1. __trust_wp_tuple_get_0(__trust_wp_tuple2(x0, x1)) = x0
    /// forall x0 x1. __trust_wp_tuple_get_1(__trust_wp_tuple2(x0, x1)) = x1
    /// ```
    ///
    /// Without these axioms, tuple field access is uninterpreted — the solver treats
    /// `__trust_wp_tuple_get_0(t)` as an arbitrary function, making postconditions
    /// involving tuple fields unprovable when the tuple structure is not statically
    /// visible to the MIR projection simplifier.
    ///
    /// Trigger pattern: `__trust_wp_tupleN(x0, ..., xN-1)` (the constructor application)
    /// to guide E-matching instantiation. Using the constructor as trigger rather than
    /// the nested `get_I(tupleN(...))` term because ay's E-matching more reliably
    /// matches single-level function applications.
    ///
    /// Reference: Issue #509.
    pub(crate) fn assert_tuple_axioms(&mut self) {
        use trust_wp_core::formula::internal::tuple_lowering::{
            TUPLE_FIELD_LOGIC_FN_PREFIX, TUPLE_LOGIC_FN_PREFIX,
        };

        // Bridge dotted projection variables (`self.0`, etc.) to the
        // `__trust_wp_tuple_get_N` accessor family BEFORE collecting
        // declared accessors. This ensures newly declared getters are
        // included in the accessor scan below and the native datatype
        // payload axioms fire automatically. (#1296)
        self.bridge_projection_variables_to_tuple_getters();
        self.assert_struct_field_placeholder_aliases();

        let smt_tuple_prefix = trust_wp_core::logic::logic_fn_smt_name(TUPLE_LOGIC_FN_PREFIX);
        let smt_field_prefix = trust_wp_core::logic::logic_fn_smt_name(TUPLE_FIELD_LOGIC_FN_PREFIX);

        // Collect declared tuple constructors by stripping the encoded prefix
        // and parsing the remaining digit(s) as arity. Digits pass through the
        // injective encoding unchanged, so this is reliable (#1435).
        let tuple_constructors: Vec<(usize, ay_dpll::api::FuncDecl)> = self
            .logic_funcs_iter()
            .filter_map(|(name, decl)| {
                let suffix = name.strip_prefix(&smt_tuple_prefix)?;
                let arity = Self::parse_leading_usize(suffix)?;
                (arity >= 1).then_some((arity, decl.clone()))
            })
            .collect();

        // Collect declared tuple field accessors by stripping the encoded prefix
        // and parsing the remaining digit(s) as field index.
        let field_accessors: Vec<(usize, ay_dpll::api::FuncDecl)> = self
            .logic_funcs_iter()
            .filter_map(|(name, decl)| {
                let suffix = name.strip_prefix(&smt_field_prefix)?;
                let index = Self::parse_leading_usize(suffix)?;
                Some((index, decl.clone()))
            })
            .collect();

        if field_accessors.is_empty() {
            return;
        }

        if !tuple_constructors.is_empty() {
            // For each constructor/accessor pair where index < arity, assert the axiom
            for &(arity, ref ctor_decl) in &tuple_constructors {
                // Create bound variables using the constructor's declared element sorts.
                // This is critical: if an element is Bool-sorted, the axiom's bound
                // variable must also be Bool, or ay's E-matching won't instantiate (#837).
                let element_sorts = ctor_decl.domain();

                // Skip constructors where domain length is inconsistent with parsed
                // arity — emitting axioms with wrong sorts is unsound (#1608).
                if element_sorts.len() < arity {
                    continue;
                }

                let mut bound_vars: Vec<ay_dpll::api::Term> = Vec::with_capacity(arity);
                for (i, sort) in element_sorts.iter().enumerate().take(arity) {
                    let var = self
                        .solver
                        .fresh_var(&format!("tuple_ax_{i}"), sort.clone());
                    bound_vars.push(var);
                }

                // Build the constructor application: __trust_wp_tupleN(x0, x1, ..., xN-1)
                let ctor_term = self.solver.apply(ctor_decl, &bound_vars);

                for &(index, ref accessor_decl) in &field_accessors {
                    if index >= arity {
                        continue; // This accessor doesn't apply to this constructor
                    }

                    // Guard: skip when accessor domain sort mismatches constructor
                    // return sort. Sort-aware placeholder declarations (#994) can
                    // create getters with Tuple/Datatype domains alongside legacy
                    // Int-domain constructors (or vice versa). Without this guard,
                    // the raw solver.apply below panics on the sort mismatch.
                    let accessor_domain = accessor_decl.domain();
                    let ctor_return = ctor_decl.range();
                    if let Some(acc_domain) = accessor_domain.first() {
                        if *acc_domain != *ctor_return {
                            continue;
                        }
                    }

                    // Safe: index < arity <= element_sorts.len()
                    let elem_sort = element_sorts[index].clone();

                    // Build: __trust_wp_tuple_get_I(__trust_wp_tupleN(x0, ..., xN-1))
                    let accessor_term = self.solver.apply(accessor_decl, &[ctor_term]);

                    // Unit-sorted elements: skip axiom. Unit has one inhabitant,
                    // so get_I(tupleN(..., unit, ...)) is trivially the unit value.
                    // Emitting the axiom would cause a sort mismatch because the
                    // accessor returns Int but the bound variable is Unit. (#2059)
                    if elem_sort == unit_sort() {
                        continue;
                    }
                    let accessor_range = accessor_decl.range().clone();
                    if (accessor_range != elem_sort
                        && !(elem_sort == Sort::Bool && accessor_range == Sort::Int)
                        && select_structural_sort_target(&accessor_range, &elem_sort).is_none())
                        || bool_accessor_over_non_bool_payload(&accessor_range, &elem_sort)
                    {
                        continue;
                    }

                    // A `MutRef`-carrier element with an inner-sorted getter
                    // must NOT get the defining axiom (#closure-capture-
                    // carriers): the carrier/inner pairing passes the
                    // structural-target check above, but `eq_term` below
                    // cannot equate the Int-ranged accessor with the
                    // carrier-sorted bound variable — it would coerce the
                    // bound variable into a FRESH CONSTANT, fabricating
                    // `forall v. get_I(tupleN(.., v, ..)) == c`, a premise
                    // that forces every carrier-tuple projection equal (and
                    // fails the dt-egraph model builder's structural
                    // self-check, degrading whole obligations to Unknown).
                    // Skipping keeps the getter uninterpreted over this
                    // family — strictly weaker, sound.
                    if accessor_range != elem_sort
                        && select_mutref_carrier_target(&accessor_range, &elem_sort).is_some()
                    {
                        continue;
                    }

                    // Int-lane projection of an Option-typed tuple element: the
                    // accessor returns the universal-fallback `Int` carrier while
                    // the element is a native `OptionInt` datatype, so the
                    // `eq_term` below would fabricate the
                    // `ite(is_some, Some(spec_unwrap(get_I(..))), None)`
                    // Int<->Option bridge INSIDE this quantifier body. Triggered on
                    // the tuple constructor, that bridge term re-enters tuple
                    // construction and seeds an unbounded
                    // `Some(spec_unwrap(get_I(tupleN(Some(spec_unwrap(...))))))`
                    // E-matching tower — or_pat's residual degrade-to-Unknown.
                    // Re-emit this projection as GROUND instances over the concrete
                    // `tupleN(..)` applications instead (see
                    // `assert_ground_option_tuple_projection_instances`) so the
                    // projection fact is retained but, carrying no trigger, no
                    // tower can form. (loop-free)
                    if self.tuple_projection_needs_option_bridge(&accessor_range, &elem_sort) {
                        continue;
                    }

                    // When the element sort differs from the accessor's return sort
                    // (e.g., Bool element but getter returns Int), coerce the bound
                    // variable to Int via ite(x, 1, 0) to keep the axiom well-sorted.
                    // The bound variable is Bool for E-matching, but the accessor
                    // returns Int, so we bridge the sorts. (#837)
                    let rhs = if elem_sort == Sort::Bool && accessor_range != Sort::Bool {
                        let one = self.solver.int_const(1);
                        let zero = self.solver.int_const(0);
                        self.solver.ite(bound_vars[index], one, zero)
                    } else {
                        bound_vars[index]
                    };

                    // Build: __trust_wp_tuple_get_I(__trust_wp_tupleN(x0, ..., xN-1)) = xI
                    let _eq_sort = accessor_decl.range().clone();
                    let eq = self.eq_term(accessor_term, rhs);

                    // Wrap in forall with trigger on the constructor application.
                    // Using ctor_term as trigger (not the nested accessor_term) because
                    // ay's E-matching more reliably matches single-level function
                    // applications. The constructor term appears directly in the E-graph
                    // when result = tupleN(...) is asserted.
                    let axiom = self
                        .solver
                        .forall_with_triggers(&bound_vars, eq, &[&[ctor_term]]);
                    self.solver.assert_term(axiom);
                }
            }

            // Ground tuple destructor instances (#724): eagerly assert
            // `get_I(tupleN(a0, ..., aN-1)) = aI` for each ground constructor
            // application in the pool. This gives the LIA solver direct equalities
            // without requiring E-matching → congruence closure → theory combination,
            // which ay-dpll fails to chain for multi-field struct invariants.
            self.assert_ground_tuple_destructor_instances(
                &tuple_constructors,
                &field_accessors,
                &smt_tuple_prefix,
            );

            // Loop-free replacement for the Int-lane Option projection axioms
            // skipped above: emit `get_I(tupleN(..)) = arg_I` as GROUND instances
            // over the concrete tuple applications present in the query, so the
            // Int<->Option bridge is fabricated only over fixed ground terms (no
            // trigger, no tower). (loop-free)
            self.assert_ground_option_tuple_projection_instances(
                &tuple_constructors,
                &field_accessors,
            );
        }

        // Registered datatypes can still route payload reads through the
        // legacy tuple-get UF family even when no raw tuple constructor was
        // declared in the same query. Keep these bridges independent from the
        // tuple-constructor axiom gate so getter-only driver shapes still get
        // native payload semantics. (#1296)
        self.assert_native_datatype_payload_axioms(&field_accessors);
        self.assert_ground_native_datatype_payload_instances(&field_accessors);
        self.assert_native_datatype_payload_reconstruction_axioms(&field_accessors);
    }

    /// Assert tuple-get payload axioms for native datatype constructors.
    ///
    /// Driver-lowered enum and struct field reads still flow through the legacy
    /// `__trust_wp_tuple_get_N` UF family. When the receiver is a native datatype
    /// constructor, bridge that UF back to the constructor payload:
    ///
    /// ```text
    /// forall v. __trust_wp_tuple_get_0(OwnResult::Ok(v)) = v
    /// forall e. __trust_wp_tuple_get_0(OwnResult::Err(e)) = e
    /// ```
    ///
    /// Without this bridge, driver-shaped bodies can choose the right branch
    /// with `discriminant(self)` while still reading an unconstrained `self.0`
    /// payload, producing semantic counterexamples in compat cases like
    /// `result/own.rs`. (#1296)
    fn assert_native_datatype_payload_axioms(&mut self, field_accessors: &[(usize, FuncDecl)]) {
        let datatypes: Vec<DatatypeSort> = self.datatypes_iter().cloned().collect();

        for datatype in datatypes {
            let datatype_sort = Sort::Datatype(datatype.clone());

            for constructor in &datatype.constructors {
                if constructor.fields.is_empty() {
                    continue;
                }

                let bound_vars = constructor
                    .fields
                    .iter()
                    .enumerate()
                    .map(|(field_index, field)| {
                        self.solver.fresh_var(
                            &format!(
                                "native_payload_ax_{}_{}_{}",
                                datatype.name, constructor.name, field_index
                            ),
                            field.sort.clone(),
                        )
                    })
                    .collect::<Vec<_>>();
                let Some(ctor_term) = self.axiom_datatype_constructor(
                    "native payload accessor axiom",
                    &datatype,
                    &constructor.name,
                    &bound_vars,
                ) else {
                    continue;
                };

                for &(index, ref accessor_decl) in field_accessors {
                    let Some(field) = constructor.fields.get(index) else {
                        continue;
                    };

                    let accessor_domain = accessor_decl.domain();
                    if accessor_domain.first() != Some(&datatype_sort) {
                        continue;
                    }

                    let field_sort = field.sort.clone();
                    let accessor_range = accessor_decl.range().clone();
                    if field_sort == unit_sort() {
                        continue;
                    }
                    if accessor_range != field_sort
                        && !(field_sort == Sort::Bool && accessor_range == Sort::Int)
                    {
                        continue;
                    }

                    let accessor_term = self.solver.apply(accessor_decl, &[ctor_term]);
                    let rhs = if field_sort == Sort::Bool && accessor_range != Sort::Bool {
                        let one = self.solver.int_const(1);
                        let zero = self.solver.int_const(0);
                        self.solver.ite(bound_vars[index], one, zero)
                    } else {
                        bound_vars[index]
                    };
                    let eq = self.eq_term(accessor_term, rhs);
                    let axiom = self
                        .solver
                        .forall_with_triggers(&bound_vars, eq, &[&[ctor_term]]);
                    self.solver.assert_term(axiom);
                }
            }
        }
    }

    /// Assert ground tuple-get payload instances for observed native datatype
    /// constructor applications.
    ///
    /// ay-dpll can leave the quantified bridge
    /// `tuple_get_I(C(args)) = args[I]` incomplete when the payload flows through
    /// FMap local-update lookup aliases. The exact ground instance keeps the
    /// legacy tuple-get payload path connected to the native constructor payload
    /// without requiring another ay bump.
    fn assert_ground_native_datatype_payload_instances(
        &mut self,
        field_accessors: &[(usize, FuncDecl)],
    ) {
        let datatypes: Vec<DatatypeSort> = self.datatypes_iter().cloned().collect();

        for datatype in datatypes {
            let datatype_sort = Sort::Datatype(datatype.clone());
            let datatype_term_sort = datatype_sort.as_term_sort();

            for constructor in &datatype.constructors {
                if constructor.fields.is_empty() {
                    continue;
                }

                let symbol =
                    Self::native_constructor_ground_symbol(&datatype.name, &constructor.name);
                let Some(entries) = self.ground_pool.entries_for(&symbol) else {
                    continue;
                };
                let ground_entries: Vec<(ay_dpll::api::Term, Vec<ay_dpll::api::Term>)> = entries
                    .iter()
                    .filter(|entry| entry.arg_terms.len() == constructor.fields.len())
                    .map(|entry| (entry.application, entry.arg_terms.clone()))
                    .collect();

                for (constructor_term, arg_terms) in &ground_entries {
                    for &(index, ref accessor_decl) in field_accessors {
                        let Some(field) = constructor.fields.get(index) else {
                            continue;
                        };

                        let accessor_domain = accessor_decl.domain();
                        if accessor_domain.first() != Some(&datatype_sort)
                            && accessor_domain.first() != Some(&datatype_term_sort)
                        {
                            continue;
                        }

                        let field_sort = field.sort.clone();
                        let accessor_range = accessor_decl.range().clone();
                        if field_sort == unit_sort() {
                            continue;
                        }
                        if accessor_range != field_sort
                            && !(field_sort == Sort::Bool && accessor_range == Sort::Int)
                        {
                            continue;
                        }

                        let accessor_term = self.solver.apply(accessor_decl, &[*constructor_term]);
                        let rhs = if field_sort == Sort::Bool && accessor_range != Sort::Bool {
                            let one = self.solver.int_const(1);
                            let zero = self.solver.int_const(0);
                            self.solver.ite(arg_terms[index], one, zero)
                        } else {
                            arg_terms[index]
                        };
                        self.assert_ground_equality_with_seq_propagation(
                            "native_datatype_payload/ground_tuple_get",
                            accessor_term,
                            rhs,
                        );
                    }
                }
            }
        }
    }

    /// Assert native datatype reconstruction axioms through legacy tuple accessors.
    ///
    /// The tuple payload bridge above proves `get_I(C(v)) = v`, but driver-lowered
    /// postconditions such as `OwnResult::Ok(result) == self` need the converse
    /// direction once the body binds `result = self.0` / `result = tuple_get_0(self)`:
    ///
    /// ```text
    /// is_Ok(x) ==> OwnResult::Ok(__trust_wp_tuple_get_0(x)) = x
    /// is_Err(x) ==> OwnResult::Err(__trust_wp_tuple_get_0(x)) = x
    /// ```
    ///
    /// Restricting the axiom with the native datatype tester keeps it scoped to
    /// the active constructor, avoiding the cross-family UF collapse that makes
    /// the qualified-constructor reconstruction axioms unsafe in the generic
    /// `logic_*` path. (#1296)
    fn assert_native_datatype_payload_reconstruction_axioms(
        &mut self,
        field_accessors: &[(usize, FuncDecl)],
    ) {
        let datatypes: Vec<DatatypeSort> = self.datatypes_iter().cloned().collect();

        for datatype in datatypes {
            let datatype_sort = Sort::Datatype(datatype.clone());

            for constructor in &datatype.constructors {
                if constructor.fields.is_empty() {
                    continue;
                }

                let x = self.solver.fresh_var(
                    &format!(
                        "native_payload_reconstruct_{}_{}",
                        datatype.name, constructor.name
                    ),
                    datatype_sort.clone(),
                );
                let Ok(is_ctor) = self.solver.try_datatype_tester(&constructor.name, x) else {
                    continue;
                };

                let mut ctor_args = Vec::with_capacity(constructor.fields.len());
                let mut supported = true;
                for (index, field) in constructor.fields.iter().enumerate() {
                    if field.sort == unit_sort() {
                        supported = false;
                        break;
                    }

                    let Some(accessor_decl) =
                        field_accessors.iter().find_map(|(field_index, decl)| {
                            (*field_index == index && decl.domain().first() == Some(&datatype_sort))
                                .then_some(decl)
                        })
                    else {
                        supported = false;
                        break;
                    };

                    let accessor_term = self.solver.apply(accessor_decl, &[x]);
                    let accessor_range = accessor_decl.range().clone();
                    if accessor_range == field.sort {
                        ctor_args.push(accessor_term);
                    } else if field.sort == Sort::Bool && accessor_range == Sort::Int {
                        let one = self.solver.int_const(1);
                        ctor_args.push(self.eq_term(accessor_term, one));
                    } else {
                        supported = false;
                        break;
                    }
                }

                if !supported {
                    continue;
                }

                let Some(reconstructed) = self.axiom_datatype_constructor(
                    "native payload reconstruction axiom",
                    &datatype,
                    &constructor.name,
                    &ctor_args,
                ) else {
                    continue;
                };
                let eq = self.eq_term(reconstructed, x);
                let implication = self.solver.implies(is_ctor, eq);
                let axiom = self
                    .solver
                    .forall_with_triggers(&[x], implication, &[&[is_ctor]]);
                self.solver.assert_term(axiom);
            }
        }
    }

    /// Assert ground destructor instances for tuple constructor applications (#724).
    ///
    /// For each ground `tupleN(a0, ..., aN-1)` in the ground pool, asserts:
    /// ```text
    /// get_I(tupleN(a0, ..., aN-1)) = aI   (for each accessor I < N)
    /// ```
    ///
    /// This compensates for ay-dpll's inability to combine E-matched equalities
    /// from quantified tuple axioms with LIA arithmetic. The ground instances
    /// make the field-value equalities directly available to the arithmetic solver.
    fn assert_ground_tuple_destructor_instances(
        &mut self,
        tuple_constructors: &[(usize, ay_dpll::api::FuncDecl)],
        field_accessors: &[(usize, ay_dpll::api::FuncDecl)],
        smt_tuple_prefix: &str,
    ) {
        for &(arity, ref ctor_decl) in tuple_constructors {
            let element_sorts = ctor_decl.domain();
            if element_sorts.len() < arity {
                continue;
            }

            // Compute the SMT name for this constructor to look up ground entries
            let ctor_smt_name = format!("{smt_tuple_prefix}{arity}");

            // Collect ground entries for this constructor from the pool
            let ground_entries: Vec<(ay_dpll::api::Term, Vec<ay_dpll::api::Term>)> =
                match self.ground_pool.entries_for(&ctor_smt_name) {
                    Some(entries) => entries
                        .iter()
                        .filter(|e| e.arg_terms.len() == arity)
                        .map(|e| (e.application, e.arg_terms.clone()))
                        .collect(),
                    None => continue,
                };

            for (ctor_app, arg_terms) in &ground_entries {
                for &(index, ref accessor_decl) in field_accessors {
                    if index >= arity {
                        continue;
                    }

                    // Same sort guards as the quantified axiom path
                    let accessor_domain = accessor_decl.domain();
                    let ctor_return = ctor_decl.range();
                    if let Some(acc_domain) = accessor_domain.first() {
                        if *acc_domain != *ctor_return {
                            continue;
                        }
                    }

                    let elem_sort = element_sorts[index].clone();
                    if elem_sort == unit_sort() {
                        continue;
                    }
                    let accessor_range = accessor_decl.range().clone();
                    if accessor_range != elem_sort
                        && !(elem_sort == Sort::Bool && accessor_range == Sort::Int)
                    {
                        continue;
                    }

                    // Build: get_I(tupleN(a0, ..., aN-1))
                    let accessor_app = self.solver.apply(accessor_decl, &[*ctor_app]);

                    // Coerce Bool element to Int if accessor returns Int (#837)
                    let rhs = if elem_sort == Sort::Bool && accessor_range != Sort::Bool {
                        let one = self.solver.int_const(1);
                        let zero = self.solver.int_const(0);
                        self.solver.ite(arg_terms[index], one, zero)
                    } else {
                        arg_terms[index]
                    };

                    // Assert ground instance: get_I(tupleN(a0, ..., aN-1)) = aI
                    let _eq_sort = accessor_decl.range().clone();
                    // Native Seq carrier equality does not by itself connect
                    // the finite component proxies used by collection
                    // reasoning. Materialize the same semantic equality shape
                    // as ordinary encoded `==` so a Seq-valued tuple payload
                    // retains its observable length/array identity.
                    let ground_eq = self.seq_aware_equality_term(accessor_app, rhs);
                    self.solver.assert_term(ground_eq);
                }
            }
        }
    }

    /// True when a tuple-`get_I` accessor returns the universal-fallback `Int`
    /// carrier while the corresponding tuple element is a native `OptionInt`
    /// datatype. In that case `eq_term(accessor, element)` fabricates the
    /// `ite(is_some, Some(spec_unwrap(accessor)), None)` Int<->Option bridge, so
    /// the caller must keep that fabrication OUT of any quantifier body (it seeds
    /// the residual or_pat E-matching tower) and emit it as ground instances.
    fn tuple_projection_needs_option_bridge(
        &self,
        accessor_range: &Sort,
        elem_sort: &Sort,
    ) -> bool {
        *accessor_range == Sort::Int && self.option_bridge_datatype(elem_sort).is_some()
    }

    /// Emit GROUND Int-lane Option projection instances, replacing the quantified
    /// `get_I(tupleN(x..)) = xI` axioms skipped in `assert_tuple_axioms` for
    /// Option-typed tuple elements (see `tuple_projection_needs_option_bridge`).
    ///
    /// For an Option-typed element the Int-lane getter (`...__ret_i`) and the
    /// element disagree on sort, so `eq_term` fabricates the
    /// `ite(is_some, Some(spec_unwrap(get_I(..))), None)` Int<->Option bridge.
    /// Emitted inside the quantified projection axiom (triggered on `tupleN(x..)`)
    /// that bridge term re-enters tuple construction and seeds an unbounded
    /// `Some(spec_unwrap(get_I(tupleN(Some(spec_unwrap(...))))))` E-matching tower
    /// (or_pat's residual ~145s degrade-to-Unknown). Re-emitting the SAME
    /// projection fact as a single ground instance per (accessor, concrete tuple
    /// application) retains the fact while carrying no trigger, so no tower forms.
    ///
    /// The concrete tuple applications are collected by walking the asserted
    /// query (NOT the ground pool, which is keyed by the base `__trust_wp_tupleN`
    /// symbol and so misses the sort-specialised placeholder constructors these
    /// Option-tuples actually use). Quantifier bodies are skipped: their
    /// constructor applications are over BOUND variables, so a ground instance
    /// there would be ill-formed.
    ///
    /// SOUNDNESS: each clause is exactly one instance of the (sound) quantified
    /// projection axiom with the bound variables set to the concrete tuple's
    /// arguments. It only ADDS a true consequence and so can never admit a model
    /// the quantified form rejected (zero false-accept risk).
    fn assert_ground_option_tuple_projection_instances(
        &mut self,
        tuple_constructors: &[(usize, FuncDecl)],
        field_accessors: &[(usize, FuncDecl)],
    ) {
        const MAX_TUPLE_PROJ_TERMS: usize = 256;

        // Index tuple constructors by their SMT symbol so an App found in the
        // asserted query can be matched to its declared element sorts/arity.
        let ctor_by_name: std::collections::HashMap<String, (usize, FuncDecl)> = tuple_constructors
            .iter()
            .map(|(arity, decl)| (decl.name().to_string(), (*arity, decl.clone())))
            .collect();

        // Walk the asserted query collecting ground tuple constructor
        // applications. Skip quantifier bodies (bound-variable applications) and
        // dedup the shared DAG via `seen`.
        let mut seen: HashSet<Term> = HashSet::new();
        let mut ground_apps: Vec<(Term, usize, FuncDecl, Vec<Term>)> = Vec::new();
        let mut stack: Vec<Term> = self.solver.assertions();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            match self.solver.term_kind(term) {
                TermKind::Forall | TermKind::Exists => continue,
                TermKind::App { name, num_args } => {
                    let children = self.solver.term_children(term);
                    if let Some((arity, decl)) = ctor_by_name.get(&name) {
                        if *arity == num_args
                            && children.len() == *arity
                            && ground_apps.len() < MAX_TUPLE_PROJ_TERMS
                        {
                            ground_apps.push((term, *arity, decl.clone(), children.clone()));
                        }
                    }
                    for child in children {
                        stack.push(child);
                    }
                }
                _ => {
                    for child in self.solver.term_children(term) {
                        stack.push(child);
                    }
                }
            }
        }

        // For each ground tuple application, emit the Int-lane Option projection
        // for every applicable accessor, deduping by the emitted accessor term.
        let mut emitted: HashSet<Term> = HashSet::new();
        for (ctor_app, arity, ctor_decl, arg_terms) in ground_apps {
            let element_sorts = ctor_decl.domain();
            if element_sorts.len() < arity {
                continue;
            }
            let ctor_return = ctor_decl.range().clone();
            for &(index, ref accessor_decl) in field_accessors {
                if index >= arity {
                    continue;
                }
                // Apply only accessors declared over this tuple's sort.
                if accessor_decl.domain().first() != Some(&ctor_return) {
                    continue;
                }
                let elem_sort = element_sorts[index].clone();
                let accessor_range = accessor_decl.range().clone();
                if !self.tuple_projection_needs_option_bridge(&accessor_range, &elem_sort) {
                    continue;
                }
                let accessor_app = self.solver.apply(accessor_decl, &[ctor_app]);
                if !emitted.insert(accessor_app) {
                    continue;
                }
                // get_I(tupleN(a0, .., aN-1)) = aI — `eq_term` fabricates the
                // Int<->Option bridge over these GROUND terms only.
                let ground_eq = self.eq_term(accessor_app, arg_terms[index]);
                self.solver.assert_term(ground_eq);
            }
        }
    }

    /// Assert unit singleton axioms: for each variable known to be unit-sorted,
    /// assert `var = __trust_wp_unit` (the canonical Unit constant).
    ///
    /// The unit type `()` has exactly one value, encoded as a declared constant
    /// `__trust_wp_unit` of `Sort::Uninterpreted("Unit")` (see `unit_sort()` in
    /// `sort_inference.rs`). Variables annotated with `ExprSort::Unit` from MIR
    /// type information are tracked in the encoder's unit-sorted set. This method
    /// constrains them to the canonical unit value via `declare_const` + `eq_or_iff`.
    ///
    /// Without this constraint, unit-typed variables introduced by quantifier
    /// elimination (e.g., `forall<_x: ()> P` → free variable `_x`) remain
    /// unconstrained, making equalities like `_x == ()` unprovable.
    ///
    /// Reference: Issue #1271.
    pub(crate) fn assert_unit_singleton_axioms(&mut self) {
        if !self.has_unit_sorted_vars() {
            return;
        }

        // Unit has exactly one inhabitant: declare a canonical constant of
        // Unit sort and assert all unit-sorted variables equal to it.
        // Must match the constant used in encode_logic_fn_call_impl for
        // __trust_wp_tuple0(). (#2059 Phase 2)
        let unit = unit_sort();
        let unit_value = self.solver.declare_const("__trust_wp_unit", unit.clone());
        let unit_sorted_vars = self.unit_sorted_var_names();

        for var_name in unit_sorted_vars {
            if let Some(var_term) = self.var_term(&var_name) {
                let eq = self.eq_term(var_term, unit_value);
                self.solver.assert_term(eq);
            }
        }
    }

    /// Bridge dotted projection variables (`self.0`, `x.1`, etc.) to the
    /// `__trust_wp_tuple_get_N` accessor calls.
    ///
    /// Some driver paths lower enum payload reads to dotted projection
    /// variables instead of explicit `__trust_wp_tuple_get_0(self)` calls.
    /// Without this bridge, the projection variable is an unconnected
    /// constant that the solver cannot relate to the datatype constructors.
    ///
    /// For each variable named `<parent>.<index>` where `<parent>` is a
    /// Datatype-sorted variable, asserts:
    /// ```text
    /// self.0 == __trust_wp_tuple_get_0(self)
    /// ```
    ///
    /// This is a ground equality (no quantifiers), so it is directly
    /// available to the arithmetic solver. The existing native datatype
    /// payload axioms then connect `tuple_get_0(Ok(v)) = v` and the
    /// reconstruction axioms connect `is_Ok(x) ==> Ok(tuple_get_0(x)) = x`,
    /// making the full chain provable. (#1296)
    fn bridge_projection_variables_to_tuple_getters(&mut self) {
        use trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name;

        let var_names = self.var_names();

        for name in &var_names {
            let Some((parent_name, digit_str)) = name.rsplit_once('.') else {
                continue;
            };
            let Ok(index) = digit_str.parse::<usize>() else {
                continue;
            };

            let Some(parent_term) = self.var_term(parent_name) else {
                continue;
            };
            let Some(parent_sort) = self.var_sort(parent_name).cloned() else {
                continue;
            };

            // Only bridge Datatype-sorted parents — plain Int projections
            // don't have meaningful accessor semantics.
            if !matches!(parent_sort, Sort::Datatype(_)) {
                continue;
            }

            let Some(proj_term) = self.var_term(name) else {
                continue;
            };
            let proj_sort = self
                .var_sort(name)
                .cloned()
                .unwrap_or_else(|| self.solver.get_sort(proj_term));

            let getter_smt_name =
                trust_wp_core::logic::logic_fn_smt_name(&tuple_field_logic_fn_name(index));

            // If the accessor already exists with an incompatible domain or
            // incompatible return sort, skip the bridge to avoid sort
            // mismatches. Bool payloads still accept the legacy Int-returning
            // getter family because eq_term preserves Bool<->Int semantics via
            // ite(b, 1, 0). (#1296)
            let accessor_decl =
                if let Some(existing) = self.logic_func_decl_cloned(&getter_smt_name) {
                    let range_compatible = existing.range() == &proj_sort
                        || (proj_sort == Sort::Bool && *existing.range() == Sort::Int);
                    if existing.domain().first() != Some(&parent_sort) || !range_compatible {
                        continue;
                    }
                    existing
                } else {
                    let getter_range = if proj_sort == Sort::Bool {
                        Sort::Int
                    } else {
                        proj_sort.clone()
                    };
                    self.get_or_declare_logic_func(&getter_smt_name, &[parent_sort], getter_range)
                };

            let accessor_app = self.solver.apply(&accessor_decl, &[parent_term]);
            let eq = self.eq_term(proj_term, accessor_app);
            self.solver.assert_term(eq);
        }
    }
}
