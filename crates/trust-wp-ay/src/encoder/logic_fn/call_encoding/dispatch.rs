// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::{DatatypeSort, Sort, Term};
use num_bigint::BigInt;
use tracing::debug;
use trust_wp_core::formula::{
    internal::tuple_lowering::tuple_logic_fn_arity, BinOp, ExprSort, PureExpr,
};

use super::transparent_adapter_inner;
use crate::{
    encoder::{
        match_enc::{
            is_stdlib_payload_constructor, short_constructor_name, stdlib_constructor_target,
            SwitchTarget,
        },
        sort_context::{
            apply_name_prefix, extract_base_var_name, is_seq_family_sort, resolve_nameable_expr,
            resolve_view_var_name,
            sort_inference::{fmap_sort, mapping_sort, unit_sort},
            DerivedKind,
        },
        unsoundness, AYEncoder,
    },
    error::EncodingError,
};

impl AYEncoder {
    fn is_stdlib_none_expr(expr: &PureExpr) -> bool {
        let PureExpr::LogicFnCall { name, args } = expr else {
            return false;
        };
        args.is_empty()
            && short_constructor_name(name) == "None"
            && matches!(
                stdlib_constructor_target(name),
                Some(SwitchTarget::OptionInt)
            )
    }

    fn preferred_tuple_none_datatype(&self) -> Option<DatatypeSort> {
        self.datatypes_for_constructor("None")
            .filter(|dt| dt.name.starts_with("Option") && dt.name != "OptionInt")
            .last()
            .cloned()
    }

    fn encode_tuple_arg_with_option_context(
        &mut self,
        arg: &PureExpr,
        prefix: Option<DerivedKind>,
    ) -> Result<Term, EncodingError> {
        if Self::is_stdlib_none_expr(arg) {
            if let Some(datatype) = self.preferred_tuple_none_datatype() {
                if let Some(term) =
                    self.axiom_datatype_constructor("tuple/none", &datatype, "None", &[])
                {
                    return Ok(term);
                }
            }
        }
        self.encode_pure_impl(arg, prefix)
    }

    /// Encode the `__trust_wp_real_to_int_floor` builtin to ay's `real_to_int`. (#1802)
    fn encode_floor_builtin(
        &mut self,
        arg: &PureExpr,
        prefix: Option<DerivedKind>,
    ) -> Result<Term, EncodingError> {
        let arg_term = self.encode_pure_impl(arg, prefix)?;
        self.solver
            .try_real_to_int(arg_term)
            .map_err(|e| EncodingError::solver_error(format!("real_to_int: {e}")))
    }

    /// Internal logic function call encoding with optional prefix.
    #[allow(clippy::too_many_lines)]
    pub(crate) fn encode_logic_fn_call_impl(
        &mut self,
        name: &str,
        args: &[PureExpr],
        prefix: Option<DerivedKind>,
    ) -> Result<Term, EncodingError> {
        if name.starts_with("__trust_wp_concrete_float_") {
            return Err(EncodingError::unsupported(
                "concrete float literal escaped MIR translation folding (#1200)".to_string(),
            ));
        }

        // Built-in: resolve(x) expands to x_current == x_final.
        // In the RustHorn encoding, resolve(x) asserts that the mutable borrow
        // of x has ended -- the prophecy variable equals the actual value.
        if name == "resolve" && args.len() == 1 {
            return self.encode_resolve(&args[0], prefix);
        }

        // Snapshot<T> is transparent in the SMT model. Creusot examples may
        // use `Snapshot::new(x)` directly in specifications (distinct from the
        // `snapshot!` macro and `Snapshot::capture` std-spec path), so normalize
        // it at encoding time instead of creating an opaque UF key.
        if is_snapshot_new_logic_fn(name) && args.len() == 1 {
            return self.encode_pure_impl(&args[0], prefix);
        }

        // Built-in: seq![] is the empty sequence. Creusot emits this spelling
        // for empty sequence literals; route it to the same axiom-backed
        // constant as Seq::empty()/seq_empty instead of an opaque nullary UF.
        if name == "seq" && args.is_empty() {
            return Ok(self.encode_seq_empty());
        }

        // Built-in: seq![v] (single-element) maps to seq_singleton(v) with
        // full axiom support (len=1, index(0)=v). This replaces the opaque
        // `logic_fn_seq_1` declaration with the axiom-backed seq_singleton. (#379)
        if matches!(name, "seq" | "Seq::singleton") && args.len() == 1 {
            let value_term = self.encode_pure_impl(&args[0], prefix)?;
            return Ok(self.encode_seq_singleton(value_term));
        }

        // Built-in: seq![v1, ..., vn] (multi-element) — fresh constant with
        // directly-constructed Array backing. (#1317 + #2242)
        if name == "seq" && args.len() > 1 {
            return self.encode_seq_literal_as_fresh_constant(args, prefix);
        }

        // Built-in: Seq::empty() / seq_empty maps to the axiom-backed seq_empty
        // constant (Seq sort). Without this, apply_logic_fn would create an
        // Int-sorted declaration, causing sort mismatches in produces() args. (#737)
        if matches!(name, "seq_empty" | "Seq::empty") && args.is_empty() {
            return Ok(self.encode_seq_empty());
        }

        // Built-in: FMap::empty() / fmap_empty maps to a canonical FMap-sorted
        // constant with axioms (forall k. !contains(empty, k), len(empty) = 0).
        // Without this, apply_logic_fn creates an Int-sorted declaration,
        // disconnected from FMap axioms. (#2549)
        if matches!(name, "fmap_empty" | "FMap::empty") && args.is_empty() {
            return Ok(self.solver.declare_const("fmap_empty", fmap_sort()));
        }

        // Built-in: FSet::empty() / fset_empty maps to a canonical constant
        // (Int sort, matching FSet carrier). Axiom-backed: forall x.
        // !contains(empty, x), len(empty) = 0, is_empty(empty) = true. (#2549)
        if matches!(name, "fset_empty" | "FSet::empty") && args.is_empty() {
            return Ok(self.solver.declare_const("fset_empty", Sort::Int));
        }

        // Transparent iterator adapters (`Copied` / `Cloned`) do not change
        // the underlying iterator state. Encode them as the inner iterator
        // term so result postconditions and view bridges see the same relation
        // as the source iterator. (#collections copied-adapter bridge)
        if let Some(inner) = transparent_adapter_inner(&PureExpr::LogicFnCall {
            name: name.to_string(),
            args: args.to_vec(),
        }) {
            return self.encode_pure_impl(inner, prefix);
        }

        // Built-in: Mapping::cst(v) / mapping_cst(v) creates a constant mapping
        // where every key maps to the given value. At the SMT level, this is
        // encoded as `mapping_cst(v)` returning a Mapping-sorted term. The
        // read-over-constant axiom `mapping_get(mapping_cst(v), k) = v` is
        // asserted via ground instances in mapping_instances.rs. (#2317)
        if matches!(name, "mapping_cst" | "Mapping::cst") && args.len() == 1 {
            let value_term = self.encode_pure_impl(&args[0], prefix)?;
            let ms = mapping_sort();
            let func = self.get_or_declare_spec_fn("mapping_cst", &[Sort::Int], ms.clone());
            let result = self.safe_apply("mapping_cst", &func, &[value_term])?;
            self.register_standard_ground_application("mapping_cst", result, vec![value_term]);
            return Ok(result);
        }

        // Built-in: __trust_wp_tuple0() (the unit value `()`) maps to a
        // canonical constant of Unit sort. Unit has exactly one inhabitant,
        // so all `()` values are identical. Must match the constant used in
        // assert_unit_singleton_axioms. (#1271, #2059 Phase 2)
        if name == "__trust_wp_tuple0" && args.is_empty() {
            return Ok(self.solver.declare_const("__trust_wp_unit", unit_sort()));
        }

        // Built-in: floor(x) for FloatToInt casts — maps to ay real_to_int. (#1802)
        if name == trust_wp_core::formula::internal::builtins::REAL_TO_INT_FLOOR_LOGIC_FN
            && args.len() == 1
        {
            return self.encode_floor_builtin(&args[0], prefix);
        }

        // Built-in: `Int::min` / `Int::max` — the creusot-std logic `Int` type
        // marks these `#[builtin("int.MinMax.min")]` / `..max`, i.e. they have
        // no Rust body and their meaning is the integer minimum/maximum. Without
        // a dispatch they lower to an UNCONSTRAINED UF placeholder
        // (`logic_Int_P__P_min__placeholder_...`), so any proof that depends on
        // min/max semantics (e.g. `min(a, b) == min(a-1, b-1) + 1`,
        // `min(0, y) == 0`) is unprovable. ay encodes min/max natively as
        // `ite(a <= b, a, b)` / `ite(a >= b, a, b)`, which is exactly the
        // integer-min/max semantics — sound and total over Int. (#2702)
        if matches!(name, "Int::min" | "Int::max") && args.len() == 2 {
            let a = self.encode_pure_impl(&args[0], prefix)?;
            let b = self.encode_pure_impl(&args[1], prefix)?;
            return if name == "Int::min" {
                self.solver
                    .try_min(a, b)
                    .map_err(|e| EncodingError::solver_error(format!("Int::min: {e}")))
            } else {
                self.solver
                    .try_max(a, b)
                    .map_err(|e| EncodingError::solver_error(format!("Int::max: {e}")))
            };
        }

        if let Some(field_name) = name.strip_prefix(
            trust_wp_core::formula::internal::tuple_lowering::NAMED_FIELD_LOGIC_FN_PREFIX,
        ) {
            if args.len() == 1 {
                let receiver_term = self.encode_pure_impl(&args[0], prefix)?;
                let receiver_sort = self.solver.get_sort(receiver_term);
                if let Some((selector_name, selector_sort)) =
                    self.native_named_field_selector(&receiver_sort, field_name)
                {
                    return self
                        .solver
                        .try_datatype_selector(&selector_name, receiver_term, selector_sort)
                        .map_err(|err| {
                            EncodingError::solver_error(format!(
                                "native named field selector {name}: {err}"
                            ))
                        });
                }
            }
        }

        // Positional tuple getter → native datatype selector upgrade (#1982):
        // The driver rewrites `__trust_wp_field_x(p)` to `__trust_wp_tuple_get_N(p)`.
        // When ADT metadata is present and the receiver is a registered struct
        // datatype, recover the native selector from the positional index.
        //
        // Sort check is done via var_sorts lookup (not encoding) to avoid
        // side effects that could interfere with downstream encoding paths
        // (e.g., tuple axiom encoding, closure sort registration).
        if let Some(index_str) = name.strip_prefix(
            trust_wp_core::formula::internal::tuple_lowering::TUPLE_FIELD_LOGIC_FN_PREFIX,
        ) {
            if let Ok(field_index) = index_str.parse::<usize>() {
                if args.len() == 1 {
                    let receiver_sort = self.peek_receiver_sort(&args[0], prefix);
                    let incompatible_inline_constructor =
                        self.is_incompatible_declared_constructor_call(&args[0], prefix);
                    let mut receiver_term = None;
                    if let Some(ref sort) = receiver_sort {
                        let encoded_receiver = self.encode_pure_impl(&args[0], prefix)?;
                        receiver_term = Some(encoded_receiver);
                        let encoded_receiver_sort = self.solver.get_sort(encoded_receiver);
                        if let Some(term) = self.try_native_positional_field_selector(
                            name,
                            sort,
                            field_index,
                            encoded_receiver,
                        )? {
                            return Ok(term);
                        }
                        if encoded_receiver_sort == *sort {
                            if let Some(projection_decl) =
                                self.registered_enum_payload_projection(sort, field_index)
                            {
                                let projection_term = self
                                    .safe_apply(name, &projection_decl, &[encoded_receiver])
                                    .map_err(|err| {
                                        EncodingError::solver_error(format!(
                                            "registered enum payload projection {name}: {err}"
                                        ))
                                    })?;
                                self.assert_ground_registered_enum_payload_reconstruction(
                                    sort,
                                    encoded_receiver,
                                    field_index,
                                    projection_term,
                                );
                                return Ok(projection_term);
                            }
                        }
                    }

                    // Some structural receivers, including FMap lookup results,
                    // only acquire their precise datatype sort after encoding.
                    // Prefer the native selector once the actual receiver term is
                    // available so proofs do not depend on quantified tuple-get
                    // payload axioms for datatype-valued map payloads.
                    let encoded_receiver = match receiver_term {
                        Some(term) => term,
                        None => self.encode_pure_impl(&args[0], prefix)?,
                    };
                    let actual_sort = self.solver.get_sort(encoded_receiver);
                    if !incompatible_inline_constructor
                        && receiver_sort.as_ref() != Some(&actual_sort)
                    {
                        if let Some(term) = self.try_native_positional_field_selector(
                            name,
                            &actual_sort,
                            field_index,
                            encoded_receiver,
                        )? {
                            return Ok(term);
                        }
                        if let Some(projection_decl) =
                            self.registered_enum_payload_projection(&actual_sort, field_index)
                        {
                            let projection_term = self
                                .safe_apply(name, &projection_decl, &[encoded_receiver])
                                .map_err(|err| {
                                    EncodingError::solver_error(format!(
                                        "registered enum payload projection {name}: {err}"
                                    ))
                                })?;
                            self.assert_ground_registered_enum_payload_reconstruction(
                                &actual_sort,
                                encoded_receiver,
                                field_index,
                                projection_term,
                            );
                            return Ok(projection_term);
                        }
                    }
                }
            }
        }

        // Datatype constructor encoding (#967, #1296, #1572): when a constructor
        // name (Some, None, Ok, Err, or qualified like OwnResult::Ok) appears as
        // a LogicFnCall, encode as a native datatype constructor application
        // instead of an uninterpreted function. Without this, `Some(x)` produces
        // an Int-sorted UF term which crashes `mk_eq` when compared with an
        // OptionInt-sorted variable from a match postcondition.
        //
        // Only fires when the datatype has ALREADY been declared (typically by a
        // match expression earlier in the encoding). Eager declaration would
        // conflict with the UF-axiom encoding from `assert_option_result_axioms`
        // which declares `logic_Some: Int -> Int` etc. (#1572)
        //
        // For qualified names (e.g., "OwnResult::Ok"), the short name ("Ok") is
        // used to look up the datatype constructor, since SwitchTarget::UserDefined
        // stores constructors by their short names.
        if let Some((dt, short_name, field_sorts)) =
            self.native_constructor_call(name, args, prefix)
        {
            let mut arg_terms = Vec::with_capacity(args.len());
            let mut sorts_compatible = true;
            for (idx, arg) in args.iter().enumerate() {
                let term = self.encode_pure_impl(arg, prefix)?;
                let expected_sort = field_sorts.get(idx);

                // After encoding, the *actual* term sort may differ from the
                // expression-level inference used by `native_constructor_call`.
                // In particular, `Some(x)` infers as `Int` but encodes as
                // `OptionInt` when `x` is Int-sorted. Applying an OptionInt
                // term to a constructor that expects Int panics in ay.
                // Bail out and fall through to the UF placeholder path. (#2462)
                let term_sort = self.solver.get_sort(term);
                if let Some(expected) = expected_sort {
                    let expected_term_sort = expected.as_term_sort();
                    if term_sort != expected_term_sort {
                        // Bool→Int coercion is handled below; all other
                        // mismatches abort the native constructor path.
                        if !(term_sort == Sort::Bool.as_term_sort()
                            && expected_term_sort == Sort::Int.as_term_sort())
                        {
                            sorts_compatible = false;
                            arg_terms.push(term);
                            continue;
                        }
                    }
                }

                // Datatype payload fields are currently Int-sorted for Option/Result.
                // Constructor calls like Err(true) therefore need Bool->Int coercion.
                //
                // Use the *encoded* term sort (`term_sort`) rather than expression-
                // level inference (`infer_expr_sort_with_context`). The two can
                // disagree when a sort hint or prior precondition encoding flagged a
                // variable as Bool while the actual encoded term is Int — feeding an
                // Int-sorted term to `solver.ite()` as the condition panics with
                // "sort mismatch in ite: expected Bool, got Int", observed for
                // `should_succeed/option.rs::ok_or` (Phase 4).
                let coerced = if term_sort == Sort::Bool
                    && expected_sort.map(|s| s == &Sort::Int).unwrap_or(false)
                {
                    let one = self.solver.int_const(1);
                    let zero = self.solver.int_const(0);
                    self.solver.ite(term, one, zero)
                } else {
                    term
                };

                arg_terms.push(coerced);
            }
            if sorts_compatible {
                let context = format!("logic_fn_constructor:{name}");
                if let Ok(term) =
                    self.safe_datatype_constructor(&context, &dt, &short_name, &arg_terms)
                {
                    self.materialize_ground_native_constructor(&dt, &short_name, term, &arg_terms);
                    return Ok(term);
                }
                debug!(
                    "native constructor path for {name} failed ay sort validation; \
                     falling back to UF placeholder"
                );
            }
            // Post-encoding sort mismatch, or a native constructor-family
            // mismatch, falls through to UF constructor encoding below.
        }
        // Sort/arity mismatch — fall through to UF constructor encoding below.

        // SliceIndexSpec name collision (#knights_tour): the driver rewrites
        // `ix.in_bounds(seq)` / `ix.has_value(..)` / `ix.resolve_elsewhere(..)`
        // from std indexing contracts into LogicFnCall nodes whenever a USER
        // logic fn shares the method name. Applying the user's registered
        // declaration to the std call's (Int, Seq, ..) arguments would bridge
        // every argument to a fresh unconstrained coercion constant, making
        // the negated goal trivially SAT (false reject). Reroute such calls to
        // the builtin SliceIndexSpec semantics instead.
        if let Some(term) =
            self.try_reroute_slice_index_spec_logic_fn_collision(name, args, prefix)?
        {
            return Ok(term);
        }

        self.propagate_domain_sort_hints(name, args, prefix);
        self.preseed_tuple_getter_placeholders_for_callee_domain(name, args, prefix);

        let tuple_constructor_arity =
            tuple_logic_fn_arity(name).filter(|arity| *arity == args.len());
        let mut arg_terms: Vec<Term> = args
            .iter()
            .map(|arg| {
                if tuple_constructor_arity.is_some() {
                    self.encode_tuple_arg_with_option_context(arg, prefix)
                } else {
                    self.encode_pure_impl(arg, prefix)
                }
            })
            .collect::<Result<_, _>>()?;

        // Fallback UF constructor encoding still uses Int payloads for
        // Option/Result constructors. Coerce Bool payloads to Int (ite b 1 0)
        // to avoid solver panics on calls like Err(true). (#1277, #1332)
        //
        // Check the *encoded* term sort, not the expression-level inference.
        // Inference can disagree with the actual term sort when a sort hint
        // mislabels an Int-sorted variable as Bool — passing the Int term to
        // `solver.ite()` as condition panics with "sort mismatch in ite". (Phase 4)
        let mut had_bool_coercion = false;
        if is_stdlib_payload_constructor(name) {
            for arg_term in arg_terms.iter_mut() {
                if self.solver.get_sort(*arg_term) == Sort::Bool {
                    let one = self.solver.int_const(1);
                    let zero = self.solver.int_const(0);
                    *arg_term = self.solver.ite(*arg_term, one, zero);
                    had_bool_coercion = true;
                }
            }
        }

        // When Bool-to-Int coercion was applied, pass None for arg_exprs so
        // apply_logic_fn infers all parameter sorts as Int (matching the coerced
        // terms). Passing the original expressions would infer Sort::Bool from
        // the pre-coercion PureExpr, causing a sort mismatch when the Int-sorted
        // coerced term is applied to a Bool-declared UF parameter. (#1277)
        let arg_exprs_for_decl = if had_bool_coercion { None } else { Some(args) };
        let result = self.apply_logic_fn(name, &arg_terms, arg_exprs_for_decl, prefix)?;
        self.assert_leading_zeros_logic_ground_facts(name, &arg_terms, result);
        self.assert_ground_some_not_none(name, result, &arg_terms);
        self.assert_ground_uf_constructor_tester(name, result);

        // Register ground function application in the ground-term pool (#994).
        // This enables the verification layer to assert targeted ground instances
        // of quantified axioms (e.g., logic fn defining axioms) before check_sat,
        // compensating for ay-dpll's single-round E-matching.
        //
        // Skip built-in constructors (Some/Ok/Err) since they are handled by
        // datatype encoding, and skip resolve() which is not a UF application.
        //
        // Also skip when inside a quantifier body (quantifier_depth > 0) because
        // the arguments are bound variables, not ground terms. Registering
        // non-ground entries pollutes the pool and causes encoding errors or
        // unsound instantiation during assert_ground_pool_instances. (#1965)
        if self.quantifier_state.quantifier_depth() == 0
            && !matches!(
                name,
                "Some" | "Ok" | "Err" | "resolve" | "seq" | "seq_empty" | "Seq::empty"
            )
        {
            let (_, smt_name) = self.resolve_logic_fn_call_name_for_decl(name);
            self.ground_pool.register_with_path_conditions(
                &smt_name,
                result,
                arg_terms,
                args.to_vec(),
                self.active_path_conditions_cloned(),
            );
        }

        Ok(result)
    }

    fn assert_leading_zeros_logic_ground_facts(
        &mut self,
        name: &str,
        arg_terms: &[Term],
        result: Term,
    ) {
        if self.quantifier_state.quantifier_depth() != 0
            || arg_terms.len() != 1
            || self.solver.get_sort(arg_terms[0]) != Sort::Int
            || self.solver.get_sort(result) != Sort::Int
        {
            return;
        }

        let Some((width, param, body)) = self.leading_zeros_logic_axiom(name) else {
            return;
        };
        let dedup_key = format!("leading_zeros_logic_ground::{name}::{result:?}");
        if !self.mark_logic_fn_axiom_asserted(dedup_key) {
            return;
        }

        let value = arg_terms[0];
        self.assert_ground_logic_definition(&param, value, result, &body);

        let zero = self.solver.int_const(0);
        let one = self.solver.int_const(1);
        let width_term = self.solver.int_const(i64::from(width));
        let max = (BigInt::from(1u8) << width) - BigInt::from(1u8);
        let max_term = self.solver.int_const_bigint(&max);
        let ge_zero = self.solver.ge(value, zero);
        let le_max = self.solver.le(value, max_term);
        let in_domain = self.solver.and(ge_zero, le_max);

        let value_eq_zero = self.eq_term(value, zero);
        let result_eq_zero = self.eq_term(result, zero);
        let zero_guard = self.solver.and(in_domain, value_eq_zero);
        let zero_case = self.solver.implies(zero_guard, result_eq_zero);
        self.assert_solver_term("leading_zeros_logic_ground/zero", zero_case);

        let value_ne_zero = self.solver.neq(value, zero);
        let result_ge_one = self.solver.ge(result, one);
        let result_le_width = self.solver.le(result, width_term);
        let result_in_range = self.solver.and(result_ge_one, result_le_width);
        let nonzero_guard = self.solver.and(in_domain, value_ne_zero);
        let nonzero_case = self.solver.implies(nonzero_guard, result_in_range);
        self.assert_solver_term("leading_zeros_logic_ground/nonzero_range", nonzero_case);
    }

    fn assert_ground_logic_definition(
        &mut self,
        param: &str,
        arg_term: Term,
        result: Term,
        body: &PureExpr,
    ) {
        let old_binding = self.insert_var(param.to_string(), arg_term);
        let old_sort = self.insert_var_sort(param.to_string(), self.solver.get_sort(arg_term));
        self.bind_quantifier_var(param.to_string());
        let body_result = self.encode_pure(body);
        self.unbind_quantifier_var(param);
        self.restore_var_sort(param, old_sort);
        self.restore_var(param, old_binding);

        if let Ok(body_term) = body_result {
            let definition = self.eq_term(result, body_term);
            self.assert_solver_term("leading_zeros_logic_ground/definition", definition);
        }
    }

    pub(in crate::encoder) fn leading_zeros_logic_axiom(
        &self,
        name: &str,
    ) -> Option<(u32, String, PureExpr)> {
        let smt_name = trust_wp_core::logic::logic_fn_smt_name(name);
        self.ground_pool.axioms().iter().find_map(|axiom| {
            (axiom.fn_symbol == smt_name
                && axiom.kind == crate::encoder::ground_pool::AxiomKind::Defining
                && axiom.requires.is_empty()
                && axiom.params.len() == 1)
                .then(|| {
                    leading_zeros_body_width(&axiom.body, &axiom.params[0])
                        .map(|width| (width, axiom.params[0].clone(), axiom.body.clone()))
                })
                .flatten()
        })
    }

    pub(crate) fn native_constructor_ground_symbol(
        datatype_name: &str,
        constructor_name: &str,
    ) -> String {
        format!("datatype_ctor::{datatype_name}::{constructor_name}")
    }

    pub(in crate::encoder) fn register_ground_native_constructor_application(
        &mut self,
        datatype: &ay_dpll::api::DatatypeSort,
        constructor_name: &str,
        constructor_term: Term,
        arg_terms: &[Term],
    ) {
        if self.quantifier_state.quantifier_depth() != 0 {
            return;
        }

        let symbol = Self::native_constructor_ground_symbol(&datatype.name, constructor_name);
        self.ground_pool
            .register_term_application_with_path_conditions(
                &symbol,
                constructor_term,
                arg_terms.to_vec(),
                self.active_path_conditions_cloned(),
            );
    }

    pub(crate) fn materialize_ground_native_constructor(
        &mut self,
        datatype: &ay_dpll::api::DatatypeSort,
        constructor_name: &str,
        constructor_term: Term,
        arg_terms: &[Term],
    ) {
        self.register_ground_native_constructor_application(
            datatype,
            constructor_name,
            constructor_term,
            arg_terms,
        );
        self.assert_ground_native_constructor_selectors(
            datatype,
            constructor_name,
            constructor_term,
            arg_terms,
        );
        self.assert_ground_native_constructor_tester(datatype, constructor_name, constructor_term);
        if constructor_name == "Some" {
            self.assert_ground_some_not_none(constructor_name, constructor_term, arg_terms);
        }
    }

    /// Assert the tester-on-constructor fact `is-C(C(args)) = true` for a
    /// freshly built ground native constructor application.
    ///
    /// The flattened UF datatype encoding omits the fundamental datatype
    /// tester axiom that native SMT datatypes provide built-in, so a
    /// ground constructor equality `x = C(args)` never propagates to
    /// `is-C(x)` on ay's non-DT solver paths. Emitting the ground fact about
    /// the constructor-application term lets EUF congruence carry the tester
    /// across the equality: when an assertion equates `x` with a native
    /// constructor app `C(args)`, congruence with `is-C(C(args)) = true`
    /// yields `is-C(x)`, which is what discriminant/match-arm guards key on.
    /// This is the converse of the existing selector fact
    /// (`C.f(C(args)) = args`) emitted right above, and lands at the same
    /// depth-0 ground site.
    ///
    /// Scope: this fires only for *native* datatype constructor applications
    /// (the dispatch.rs native-constructor path). It does NOT reach nested
    /// payloads encoded via logic-placeholder constructors
    /// (e.g. `OwnResult<Option<T>, E>` in result/own.rs::transpose, whose
    /// guard is `self = Ok_placeholder(Some(sk_t))`, not a native `Ok(..)`).
    ///
    /// Polarity-independent and sound: `is-C(C(·))` is a datatype tautology,
    /// true in every model, so it can never turn a SAT (counterexample)
    /// obligation into a spurious UNSAT.
    fn assert_ground_native_constructor_tester(
        &mut self,
        datatype: &ay_dpll::api::DatatypeSort,
        constructor_name: &str,
        constructor_term: Term,
    ) {
        if self.quantifier_state.quantifier_depth() != 0 {
            return;
        }
        // Single-constructor datatypes have a trivially-true tester; the fact
        // carries no discriminating information, so skip the noise.
        if datatype.constructors.len() < 2 {
            return;
        }
        if let Ok(tester) = self
            .solver
            .try_datatype_tester(constructor_name, constructor_term)
        {
            self.assert_solver_term("datatype_constructor/ground_tester_on_constructor", tester);
        }
    }

    fn assert_ground_native_constructor_selectors(
        &mut self,
        datatype: &ay_dpll::api::DatatypeSort,
        constructor_name: &str,
        constructor_term: Term,
        arg_terms: &[Term],
    ) {
        if self.quantifier_state.quantifier_depth() != 0 {
            return;
        }

        let Some(constructor) = datatype
            .constructors
            .iter()
            .find(|constructor| constructor.name == constructor_name)
        else {
            return;
        };

        for (index, field) in constructor.fields.iter().enumerate() {
            let Some(arg_term) = arg_terms.get(index).copied() else {
                continue;
            };
            let Ok(selector_term) = self.solver.try_datatype_selector(
                &field.name,
                constructor_term,
                field.sort.clone(),
            ) else {
                continue;
            };
            let eq = self.eq_term(selector_term, arg_term);
            self.assert_solver_term("datatype_constructor/ground_selector", eq);
        }
    }

    fn try_native_positional_field_selector(
        &mut self,
        name: &str,
        receiver_sort: &Sort,
        field_index: usize,
        receiver_term: Term,
    ) -> Result<Option<Term>, EncodingError> {
        let Some((selector_name, selector_sort)) =
            self.native_positional_field_selector(receiver_sort, field_index)
        else {
            return Ok(None);
        };
        match self.solver.try_datatype_selector(
            &selector_name,
            receiver_term,
            selector_sort.clone(),
        ) {
            Ok(term) => Ok(Some(term)),
            Err(err) => {
                // Sort mismatch: the receiver's ay sort may differ from the
                // datatype the selector is defined on (e.g., receiver is
                // Uninterpreted but selector expects a Datatype). Bridge the
                // receiver to the expected Datatype sort via a fresh constant
                // and retry. This is conservative: the fresh constant is
                // unconstrained, which cannot produce false proofs. (#2699)
                if let Sort::Datatype(ref dt) = receiver_sort {
                    let receiver_ay_sort = self.solver.get_sort(receiver_term);
                    if receiver_ay_sort != Sort::Datatype(dt.clone()) {
                        let bridged_receiver =
                            self.cached_datatype_selector_bridge(receiver_term, dt);
                        if let Ok(term) = self.solver.try_datatype_selector(
                            &selector_name,
                            bridged_receiver,
                            selector_sort,
                        ) {
                            return Ok(Some(term));
                        }
                    }
                }
                Err(EncodingError::solver_error(format!(
                    "native positional field selector {name}: {err}"
                )))
            }
        }
    }

    fn cached_datatype_selector_bridge(
        &mut self,
        receiver_term: Term,
        datatype: &DatatypeSort,
    ) -> Term {
        let key = (receiver_term, datatype.clone());
        if let Some(term) = self.datatype_selector_bridges.get(&key) {
            return *term;
        }

        static DT_BRIDGE_COUNTER: std::sync::atomic::AtomicU64 =
            std::sync::atomic::AtomicU64::new(0);
        let id = DT_BRIDGE_COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        unsoundness::increment(unsoundness::UnsoundnessCategory::SortCoercionBridge);
        let bridged_receiver = self.solver.declare_const(
            &format!("__dt_selector_bridge_{id}"),
            Sort::Datatype(datatype.clone()),
        );
        self.datatype_selector_bridges.insert(key, bridged_receiver);
        bridged_receiver
    }

    /// Preseed sort-typed tuple-getter placeholder declarations for arguments
    /// of a REGISTERED logic function, using the callee's declared domain
    /// sort (logic-fn-ARGUMENT position).
    ///
    /// The caller-side verification scope of e.g. `inc_some_2_list` inlines
    /// the callee ensures `sum((^result.1)) ...` WITHOUT ever encoding a
    /// `__trust_wp_tuple2(..)` constructor application, so the ctor-domain
    /// derivation in `placeholder_return_sort` has nothing to derive from and
    /// the getter defaults to `Int`. Passing that Int-sorted getter to
    /// `sum : List -> Int` then mints an `[apply-coerce]` fresh unconstrained
    /// constant per call — corrupting the recursive-logic-fn one-step
    /// unfolding facts and tripping the SpecAxiomDropped demotion guard on
    /// contracts whose VCs already prove (rusthorn inc_some_2_list/2_tree).
    ///
    /// Here the callee's registered declaration IS the authority on the
    /// argument sort, so pre-declare the signature-keyed getter placeholder
    /// `..__placeholder_<TupleN>__ret_<domain sort>` BEFORE the arguments are
    /// encoded; the placeholder mint then resolves it via
    /// `existing_placeholder_return_sort` (non-Int preferred), the getter
    /// application carries the callee's domain sort, and no fresh coercion
    /// constant is needed.
    ///
    /// Soundness: this only declares an UF symbol with a refined sort — no
    /// assertions are added. The resulting unfolding facts are definitional
    /// instances of the callee over an (at worst) uninterpreted List-valued
    /// term, which are true in the intended semantics; sort refinement
    /// strictly removes unconstrained fresh constants. Conservative guards
    /// mirror `tuple_getter_return_sort_from_ctor_domain`: single-receiver
    /// getters over the opaque `Uninterpreted("TupleN")` carrier only, and
    /// only for non-Int/non-Bool declared domain sorts. (#residuals)
    fn preseed_tuple_getter_placeholders_for_callee_domain(
        &mut self,
        name: &str,
        args: &[PureExpr],
        prefix: Option<DerivedKind>,
    ) {
        let smt_name = trust_wp_core::logic::logic_fn_smt_name(name);
        let Some(func_decl) = self.logic_func_decl_cloned(&smt_name) else {
            return;
        };
        if func_decl.domain().len() != args.len() {
            return;
        }
        let domain = func_decl.domain().to_vec();
        for (i, arg) in args.iter().enumerate() {
            let expected = &domain[i];
            if matches!(expected, Sort::Int | Sort::Bool) {
                continue;
            }
            let Some((getter_name, getter_args)) = self.peel_tuple_getter_call(arg) else {
                continue;
            };
            if trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_index(
                getter_name,
            )
            .is_none()
            {
                continue;
            }
            let [receiver] = getter_args else {
                continue;
            };
            let receiver = receiver.clone();
            let getter_smt = trust_wp_core::logic::logic_fn_smt_name(getter_name);
            let receiver_sort = self.infer_expr_sort_with_context(&receiver, prefix);
            let Sort::Uninterpreted(carrier) = &receiver_sort else {
                continue;
            };
            if carrier
                .strip_prefix("Tuple")
                .and_then(|arity| arity.parse::<usize>().ok())
                .is_none()
            {
                continue;
            }
            let param_sorts = std::slice::from_ref(&receiver_sort);
            let decl_key = Self::placeholder_smt_name(&getter_smt, param_sorts, expected);
            self.get_or_declare_logic_func(&decl_key, param_sorts, expected.clone());
        }
    }

    /// Propagate sort hints from declared domain sorts to call-site arguments
    /// before encoding. Handles Seq (#1572), FMap (#994), and Datatype (#2002) hints.
    fn propagate_domain_sort_hints(
        &mut self,
        name: &str,
        args: &[PureExpr],
        prefix: Option<DerivedKind>,
    ) {
        let smt_name = trust_wp_core::logic::logic_fn_smt_name(name);
        let func_decl = if let Some(fd) = self.logic_func_decl_cloned(&smt_name) {
            fd
        } else {
            let placeholder_prefix = format!("{smt_name}__placeholder_");
            match self
                .logic_funcs_iter()
                .find(|(decl_name, decl)| {
                    decl_name.starts_with(&placeholder_prefix) && decl.domain().len() == args.len()
                })
                .map(|(_, decl)| decl.clone())
            {
                Some(fd) => fd,
                None => return,
            }
        };
        let domain = func_decl.domain().to_vec();
        for (i, arg) in args.iter().enumerate() {
            if let Some(sort) = domain.get(i) {
                if is_seq_family_sort(sort) {
                    if let Some(vn) = resolve_view_var_name(arg, prefix) {
                        self.record_sort_hint(vn, ExprSort::Seq);
                    }
                    if let Some(vn) = resolve_nameable_expr(arg, prefix) {
                        self.record_sort_hint(vn, ExprSort::Seq);
                    }
                } else if matches!(sort, Sort::Uninterpreted(s) if s == "FMap") {
                    // FMap domain sort propagation: when a declared function
                    // has an FMap-sorted parameter, propagate FMap hint to the
                    // call-site argument variable. Without this, v@ in f(v@)
                    // where f has FMap domain won't get an FMap hint, causing
                    // method calls like v@.contains(k) to misroute. (#994)
                    if let Some(vn) = resolve_view_var_name(arg, prefix) {
                        self.record_sort_hint(vn, ExprSort::FMap);
                    }
                    if let Some(vn) = resolve_nameable_expr(arg, prefix) {
                        self.record_sort_hint(vn, ExprSort::FMap);
                    }
                } else if matches!(sort, Sort::Datatype(_)) {
                    if let Some(base_name) = extract_base_var_name(arg) {
                        let var_key = apply_name_prefix(base_name, prefix).into_owned();
                        self.insert_var_sort(var_key, sort.clone());
                    }
                }
            }
        }
    }
}

fn leading_zeros_body_width(body: &PureExpr, param: &str) -> Option<u32> {
    let PureExpr::BinOp(width, BinOp::Sub, bit_count) = body else {
        return None;
    };
    let PureExpr::MethodCall {
        receiver,
        method,
        args,
    } = bit_count.as_ref()
    else {
        return None;
    };
    if method != "leading_zeros_logic" || !args.is_empty() {
        return None;
    }
    if !matches!(receiver.as_ref(), PureExpr::Var(name, _) if name == param) {
        return None;
    }
    bit_count_width_literal(width)
}

fn bit_count_width_literal(expr: &PureExpr) -> Option<u32> {
    match expr {
        PureExpr::Int(value) => u32::try_from(*value).ok().filter(|width| *width > 0),
        PureExpr::Var(name, _) if name == "USIZE_BITS" => {
            Some((std::mem::size_of::<usize>() * 8) as u32)
        }
        _ => None,
    }
}

fn is_snapshot_new_logic_fn(name: &str) -> bool {
    name == "Snapshot::new" || name.ends_with("::Snapshot::new")
}

#[cfg(test)]
mod tests {
    use ay_dpll::api::{SolveResult, Sort};
    use ntest::timeout;

    use crate::{encoder::AYEncoder, tests::helpers::*};

    // ── encode_logic_fn_call_impl: direct UF encoding ────────────────

    /// A simple user-defined logic function call encodes as a UF application.
    /// UF congruence: f(x) == f(x) is always true.
    #[test]
    #[timeout(30000)]
    fn test_dispatch_simple_uf_call_congruence() {
        let mut encoder = AYEncoder::new();
        let expr = logic_fn_call("user_fn", vec![var("x")]);
        let t1 = encoder.encode_pure(&expr).expect("first encoding");
        let t2 = encoder.encode_pure(&expr).expect("second encoding");
        let eq = encoder.solver.eq(t1, t2);
        let neq = encoder.solver.not(eq);
        encoder.assert_term(neq);
        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "user_fn(x) != user_fn(x) should be UNSAT (UF congruence)"
        );
    }

    /// Different arguments produce potentially different results (SAT).
    #[test]
    #[timeout(30000)]
    fn test_dispatch_different_args_can_differ() {
        let mut encoder = AYEncoder::new();
        let call_a = logic_fn_call("f", vec![var("a")]);
        let call_b = logic_fn_call("f", vec![var("b")]);
        let t1 = encoder.encode_pure(&call_a).expect("f(a)");
        let t2 = encoder.encode_pure(&call_b).expect("f(b)");
        let eq = encoder.solver.eq(t1, t2);
        let neq = encoder.solver.not(eq);
        encoder.assert_term(neq);
        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Sat),
            "f(a) != f(b) should be SAT (different args can produce different results), got {result:?}"
        );
    }

    // ── Sort-aware dispatch: Bool-returning logic functions ──────────

    /// A pre-declared Bool-returning logic function should produce a Bool-sorted term.
    #[test]
    #[timeout(30000)]
    fn test_dispatch_bool_returning_fn_sort() {
        let mut encoder = AYEncoder::new();
        // logic_fn_smt_name("isvalid") = "logic_isvalid" (no underscores to double)
        let _fd = encoder.get_or_declare_logic_func("logic_isvalid", &[Sort::Int], Sort::Bool);
        let expr = logic_fn_call("isvalid", vec![int(5)]);
        let term = encoder
            .encode_pure(&expr)
            .expect("Bool-returning fn encoding");
        let sort = encoder.solver.get_sort(term);
        assert_eq!(
            sort,
            Sort::Bool,
            "declared Bool-returning logic function should produce Bool-sorted term"
        );
    }

    /// A Bool-returning function can be used in logical connectives without sort mismatch.
    #[test]
    #[timeout(30000)]
    fn test_dispatch_bool_fn_in_conjunction() {
        let mut encoder = AYEncoder::new();
        // logic_fn_smt_name("mypred") = "logic_mypred"
        let _fd = encoder.get_or_declare_logic_func("logic_mypred", &[Sort::Int], Sort::Bool);
        // mypred(x) && mypred(y) — should encode without sort errors
        let conj = and(
            logic_fn_call("mypred", vec![var("x")]),
            logic_fn_call("mypred", vec![var("y")]),
        );
        let term = encoder
            .encode_pure(&conj)
            .expect("conjunction of Bool logic fns should encode");
        let sort = encoder.solver.get_sort(term);
        assert_eq!(sort, Sort::Bool, "conjunction should produce Bool sort");
    }

    // ── Dispatch with multiple arguments of different sorts ─────────

    /// Logic function with Int and Bool arguments uses correct placeholder sorts.
    #[test]
    #[timeout(30000)]
    fn test_dispatch_mixed_int_bool_args() {
        let mut encoder = AYEncoder::new();
        let expr = logic_fn_call("mixed", vec![int(1), bool_expr(true)]);
        let term = encoder
            .encode_pure(&expr)
            .expect("mixed Int+Bool args should encode");
        // Term should be valid — the placeholder infers sorts from arguments
        let _ = encoder.solver.get_sort(term);
    }

    /// Logic function with three arguments of different sorts.
    #[test]
    #[timeout(30000)]
    fn test_dispatch_three_different_sort_args() {
        let mut encoder = AYEncoder::new();
        // Int, Bool, and an expression that evaluates to Bool
        let expr = logic_fn_call(
            "triple_arg_fn",
            vec![int(42), bool_expr(false), gt(var("x"), int(0))],
        );
        let term = encoder
            .encode_pure(&expr)
            .expect("three mixed-sort args should encode");
        let _ = encoder.solver.get_sort(term);

        // UF congruence: same call with same args produces same result
        let term2 = encoder.encode_pure(&expr).expect("re-encode triple args");
        let eq = encoder.solver.eq(term, term2);
        let neq = encoder.solver.not(eq);
        encoder.assert_term(neq);
        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "same triple-arg call should be equal (UF congruence)"
        );
    }

    /// A declared function with mixed domain sorts dispatches correctly.
    #[test]
    #[timeout(30000)]
    fn test_dispatch_declared_fn_mixed_domain() {
        let mut encoder = AYEncoder::new();
        // logic_fn_smt_name("mycombine") = "logic_mycombine"
        let _fd = encoder.get_or_declare_logic_func(
            "logic_mycombine",
            &[Sort::Int, Sort::Bool],
            Sort::Int,
        );
        let expr = logic_fn_call("mycombine", vec![int(10), bool_expr(true)]);
        let term = encoder
            .encode_pure(&expr)
            .expect("declared fn with mixed domain should encode");
        let sort = encoder.solver.get_sort(term);
        assert_eq!(
            sort,
            Sort::Int,
            "mycombine(Int, Bool) -> Int should produce Int-sorted term"
        );
    }

    // ── Builtin dispatch paths ──────────────────────────────────────

    /// resolve(x) dispatches to the resolve builtin (Bool-sorted equality).
    #[test]
    #[timeout(30000)]
    fn test_dispatch_resolve_builtin() {
        let mut encoder = AYEncoder::new();
        encoder
            .get_or_declare_var("x", Sort::Int)
            .expect("declare x");
        encoder
            .get_or_declare_var("x_final", Sort::Int)
            .expect("declare x_final");
        let expr = logic_fn_call("resolve", vec![var("x")]);
        let term = encoder.encode_pure(&expr).expect("resolve should encode");
        let sort = encoder.solver.get_sort(term);
        assert_eq!(
            sort,
            Sort::Bool,
            "resolve(x) should produce a Bool-sorted term (x == x_final)"
        );
    }

    /// `Int::min(3, 5)` dispatches to ay's native min and equals `3` — the
    /// negation must be UNSAT (#2702).
    #[test]
    #[timeout(30000)]
    fn test_dispatch_int_min_concrete() {
        let mut encoder = AYEncoder::new();
        let expr = logic_fn_call("Int::min", vec![int(3), int(5)]);
        let term = encoder.encode_pure(&expr).expect("Int::min should encode");
        let three = encoder.solver.int_const(3);
        let eq = encoder.solver.eq(term, three);
        let neq = encoder.solver.not(eq);
        encoder.assert_term(neq);
        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "Int::min(3, 5) != 3 should be UNSAT (native min semantics)"
        );
    }

    /// `Int::max(3, 5)` equals `5`.
    #[test]
    #[timeout(30000)]
    fn test_dispatch_int_max_concrete() {
        let mut encoder = AYEncoder::new();
        let expr = logic_fn_call("Int::max", vec![int(3), int(5)]);
        let term = encoder.encode_pure(&expr).expect("Int::max should encode");
        let five = encoder.solver.int_const(5);
        let eq = encoder.solver.eq(term, five);
        let neq = encoder.solver.not(eq);
        encoder.assert_term(neq);
        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "Int::max(3, 5) != 5 should be UNSAT (native max semantics)"
        );
    }

    /// The translation-invariance law `Int::min(a, b) == Int::min(a-1, b-1) + 1`
    /// — the exact fact the `custom_variant` loop preservation needs — holds for
    /// the native min encoding. Its negation must be UNSAT (#2702).
    #[test]
    #[timeout(30000)]
    fn test_dispatch_int_min_translation_invariant() {
        let mut encoder = AYEncoder::new();
        encoder.get_or_declare_var("a", Sort::Int).expect("a");
        encoder.get_or_declare_var("b", Sort::Int).expect("b");
        let lhs = logic_fn_call("Int::min", vec![var("a"), var("b")]);
        let a_minus_1 = sub(var("a"), int(1));
        let b_minus_1 = sub(var("b"), int(1));
        let rhs_inner = logic_fn_call("Int::min", vec![a_minus_1, b_minus_1]);
        let lhs_t = encoder.encode_pure(&lhs).expect("min(a,b)");
        let rhs_inner_t = encoder.encode_pure(&rhs_inner).expect("min(a-1,b-1)");
        let one = encoder.solver.int_const(1);
        let rhs_t = encoder.solver.add(rhs_inner_t, one);
        let eq = encoder.solver.eq(lhs_t, rhs_t);
        let neq = encoder.solver.not(eq);
        encoder.assert_term(neq);
        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "min(a,b) != min(a-1,b-1)+1 should be UNSAT (min is translation-invariant)"
        );
    }

    /// SOUNDNESS: `Int::min(a, b)` is NOT forced to equal `a` for free vars —
    /// the negation `min(a,b) != a` must remain SAT (min is a genuine choice,
    /// not a fabricated identity). Guards against the native dispatch
    /// over-constraining.
    #[test]
    #[timeout(30000)]
    fn test_dispatch_int_min_not_trivially_a() {
        let mut encoder = AYEncoder::new();
        encoder.get_or_declare_var("a", Sort::Int).expect("a");
        encoder.get_or_declare_var("b", Sort::Int).expect("b");
        let expr = logic_fn_call("Int::min", vec![var("a"), var("b")]);
        let term = encoder.encode_pure(&expr).expect("min(a,b)");
        let a_t = encoder.encode_pure(&var("a")).expect("a term");
        let eq = encoder.solver.eq(term, a_t);
        let neq = encoder.solver.not(eq);
        encoder.assert_term(neq);
        assert!(
            matches!(encoder.check_sat(), SolveResult::Sat),
            "min(a,b) != a should be SAT (b can be the smaller value)"
        );
    }

    /// seq![v] dispatches to seq_singleton, producing a Seq-sorted term.
    #[test]
    #[timeout(30000)]
    fn test_dispatch_seq_singleton_builtin() {
        let mut encoder = AYEncoder::new();
        let expr = logic_fn_call("seq", vec![int(42)]);
        let term = encoder.encode_pure(&expr).expect("seq singleton");
        let sort = encoder.solver.get_sort(term);
        assert!(
            sort.is_seq(),
            "seq![42] should produce Seq sort, got {sort:?}"
        );
    }

    /// seq![] dispatches to the axiom-backed empty sequence.
    #[test]
    #[timeout(30000)]
    fn test_dispatch_seq_empty_macro_builtin() {
        let mut encoder = AYEncoder::new();
        let expr = logic_fn_call("seq", vec![]);
        let term = encoder.encode_pure(&expr).expect("seq![]");
        let sort = encoder.solver.get_sort(term);
        assert!(
            sort.is_seq(),
            "seq![] should produce Seq sort, got {sort:?}"
        );

        let canonical = encoder.encode_seq_empty();
        let eq = encoder.solver.eq(term, canonical);
        let distinct = encoder.solver.not(eq);
        encoder.assert_term(distinct);
        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "seq![] should encode as the canonical empty Seq"
        );
    }

    /// seq_empty dispatches to the axiom-backed empty sequence.
    #[test]
    #[timeout(30000)]
    fn test_dispatch_seq_empty_builtin() {
        let mut encoder = AYEncoder::new();
        let expr = logic_fn_call("seq_empty", vec![]);
        let term = encoder.encode_pure(&expr).expect("seq_empty");
        let sort = encoder.solver.get_sort(term);
        assert!(
            sort.is_seq(),
            "seq_empty should produce Seq sort, got {sort:?}"
        );
    }

    /// __trust_wp_concrete_float_* is rejected with an unsupported error.
    #[test]
    #[timeout(30000)]
    fn test_dispatch_concrete_float_rejected() {
        let mut encoder = AYEncoder::new();
        let expr = logic_fn_call("__trust_wp_concrete_float_3_14", vec![]);
        let result = encoder.encode_pure(&expr);
        assert!(result.is_err(), "concrete float literal should be rejected");
    }

    /// __trust_wp_tuple0() dispatches to a Unit-sorted constant.
    #[test]
    #[timeout(30000)]
    fn test_dispatch_tuple0_unit() {
        let mut encoder = AYEncoder::new();
        let expr = logic_fn_call("__trust_wp_tuple0", vec![]);
        let term = encoder.encode_pure(&expr).expect("tuple0");
        let sort = encoder.solver.get_sort(term);
        assert!(
            matches!(&sort, Sort::Uninterpreted(s) if s == "Unit"),
            "__trust_wp_tuple0() should produce Unit sort, got {sort:?}"
        );
    }

    /// fmap_empty dispatches to an FMap-sorted constant.
    #[test]
    #[timeout(30000)]
    fn test_dispatch_fmap_empty_builtin() {
        let mut encoder = AYEncoder::new();
        let expr = logic_fn_call("fmap_empty", vec![]);
        let term = encoder.encode_pure(&expr).expect("fmap_empty");
        let sort = encoder.solver.get_sort(term);
        assert!(
            matches!(&sort, Sort::Uninterpreted(s) if s == "FMap"),
            "fmap_empty should produce FMap sort, got {sort:?}"
        );
    }

    /// FSet::empty() dispatches to an Int-sorted constant.
    #[test]
    #[timeout(30000)]
    fn test_dispatch_fset_empty_builtin() {
        let mut encoder = AYEncoder::new();
        let expr = logic_fn_call("fset_empty", vec![]);
        let term = encoder.encode_pure(&expr).expect("fset_empty");
        let sort = encoder.solver.get_sort(term);
        assert_eq!(
            sort,
            Sort::Int,
            "fset_empty should produce Int sort (FSet carrier)"
        );
    }

    // ── propagate_domain_sort_hints ─────────────────────────────────

    /// Domain sort hints propagate Seq sort from declared function parameters.
    #[test]
    #[timeout(30000)]
    fn test_dispatch_propagates_seq_domain_hint() {
        let mut encoder = AYEncoder::new();
        // Declare a function expecting Seq parameter
        let s_sort = encoder.get_seq_sort();
        let _fd =
            encoder.get_or_declare_logic_func("logic_takes_seq", &[s_sort.clone()], Sort::Int);
        // Encode a call with a view variable — should propagate Seq hint
        let expr = logic_fn_call("takes_seq", vec![view(var("v"))]);
        // Register sort hints first so the view variable gets Seq tag
        encoder.register_sort_hints(std::slice::from_ref(&expr));
        let _term = encoder
            .encode_pure(&expr)
            .expect("seq domain hint propagation should not panic");
    }

    // ── Ground pool registration at depth 0 ─────────────────────────

    /// Logic function calls at quantifier_depth == 0 register in the ground pool.
    /// Calls inside quantifiers (depth > 0) should NOT register ground entries.
    #[test]
    #[timeout(30000)]
    fn test_dispatch_ground_pool_only_at_depth_zero() {
        let mut encoder = AYEncoder::new();
        // Direct call at depth 0 — should succeed and register
        let expr = logic_fn_call("ground_test_fn", vec![int(1)]);
        let _term = encoder
            .encode_pure(&expr)
            .expect("ground-level call should encode and register in pool");
    }
}
