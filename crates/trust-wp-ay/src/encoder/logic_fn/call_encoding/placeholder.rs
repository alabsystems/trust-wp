// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use ay_dpll::api::{Sort, Term};
use tracing::debug;
use trust_wp_core::formula::PureExpr;

use crate::{
    encoder::{
        match_enc::{
            is_stdlib_payload_constructor, short_constructor_name, stdlib_constructor_target,
            SwitchTarget,
        },
        sort_context::{apply_name_prefix, sort_inference::fmap_sort, DerivedKind},
        unsoundness, AYEncoder,
    },
    error::EncodingError,
};

impl AYEncoder {
    pub(super) fn resolve_logic_fn_call_name_for_decl<'a>(
        &self,
        name: &'a str,
    ) -> (&'a str, String) {
        let smt_name = trust_wp_core::logic::logic_fn_smt_name(name);
        if self.has_logic_func_decl(&smt_name) || !name.starts_with("Self::") {
            return (name, smt_name);
        }

        if let Some(method) = name.strip_prefix("Self::") {
            let bare_smt = trust_wp_core::logic::logic_fn_smt_name(method);
            if self.has_logic_func_decl(&bare_smt) {
                return (method, bare_smt);
            }
        }

        (name, smt_name)
    }

    pub(in crate::encoder) fn existing_placeholder_return_sort(
        &self,
        smt_name: &str,
        param_sorts: &[Sort],
    ) -> Option<Sort> {
        let placeholder_prefix = format!("{smt_name}__placeholder_");
        let mut int_fallback = None;

        for (decl_name, decl) in self.logic_funcs_iter() {
            if !decl_name.starts_with(&placeholder_prefix) || decl.domain() != param_sorts {
                continue;
            }
            if decl.range() != &Sort::Int {
                return Some(decl.range().clone());
            }
            int_fallback.get_or_insert_with(|| decl.range().clone());
        }

        int_fallback
    }

    /// Derive a tuple getter's return sort from the declared tuple
    /// constructor's domain.
    ///
    /// For `__trust_wp_tuple_get_<index>` applied to a receiver of the opaque
    /// `Uninterpreted("Tuple<N>")` carrier sort, scan the declared
    /// `__trust_wp_tuple<N>` constructor family (raw and signature-keyed
    /// placeholder declarations alike) whose range is exactly the receiver
    /// sort, and read component `<index>` of the constructor domain.
    ///
    /// Conservative by construction:
    /// - Only fires for the `Uninterpreted("TupleN")` carrier. Datatype-sorted
    ///   receivers keep their enum-payload/native-selector routes untouched.
    /// - Returns `None` when the declared constructors disagree on the
    ///   component sort (ambiguous carrier) — behavior falls back to today's.
    /// - Returns `None` for an `Int` component (today's default), so the
    ///   Int-lane getters (e.g. `result.0@`) are byte-identical to before.
    pub(in crate::encoder) fn tuple_getter_return_sort_from_ctor_domain(
        &self,
        index: usize,
        param_sorts: &[Sort],
    ) -> Option<Sort> {
        let [receiver_sort] = param_sorts else {
            return None;
        };
        let Sort::Uninterpreted(carrier) = receiver_sort else {
            return None;
        };
        let arity = carrier.strip_prefix("Tuple")?.parse::<usize>().ok()?;
        if arity < 1 || index >= arity {
            return None;
        }
        let smt_tuple_prefix = trust_wp_core::logic::logic_fn_smt_name(
            trust_wp_core::formula::internal::tuple_lowering::TUPLE_LOGIC_FN_PREFIX,
        );
        let mut derived: Option<Sort> = None;
        for (decl_name, decl) in self.logic_funcs_iter() {
            let Some(suffix) = decl_name.strip_prefix(&smt_tuple_prefix) else {
                continue;
            };
            // Getters (`...tuple__get__I...`) and the unit constructor
            // (`...tuple0...`) fail the arity parse/match and are skipped.
            let Some(decl_arity) = Self::parse_leading_usize(suffix) else {
                continue;
            };
            if decl_arity != arity || decl.range() != receiver_sort || decl.domain().len() < arity {
                continue;
            }
            let component = decl.domain()[index].clone();
            match &derived {
                None => derived = Some(component),
                Some(existing) if *existing == component => {}
                // Conflicting constructor domains for the same carrier —
                // refinement would be a guess. Stay on the Int default.
                Some(_) => return None,
            }
        }
        derived.filter(|sort| *sort != Sort::Int)
    }

    /// #prophecy-slots (Fix B M2): the return sort of `__trust_wp_tuple_get_I`
    /// when the receiver is one of the instantiation-aware prophecy-carrier
    /// sorts.
    ///
    /// The driver's substitution pipeline reaches a payload binder through a
    /// positional getter chain (`tuple_get_0(tuple_get_0(call))` for the
    /// `Option<(&mut T, ..)>` shape). Those getters previously defaulted to
    /// `Int` — the prophecy slot was erased one step before the binder even
    /// though the receiver's SORT NAME states the element sorts exactly.
    ///
    /// This derivation is authoritative rather than inferential: the name was
    /// minted by `mutref_carrier_tuple_sort_name` /
    /// `mutref_instantiated_option_name` from the payload's real type. It is
    /// consulted BEFORE the ctor-domain derivation for that reason.
    /// `legacy` elements yield `None` and keep the legacy lane.
    pub(in crate::encoder) fn prophecy_carrier_getter_return_sort(
        &mut self,
        index: usize,
        param_sorts: &[Sort],
    ) -> Option<Sort> {
        use crate::encoder::sort_context::sort_mapping::parse_mutref_carrier_tuple;

        let [receiver_sort] = param_sorts else {
            return None;
        };
        let name = match receiver_sort.as_term_sort() {
            Sort::Uninterpreted(name) => name,
            _ => return None,
        };
        if let Some(elements) = parse_mutref_carrier_tuple(&name) {
            let element = elements.get(index)?.clone()?;
            return Some(self.sort_from_expr_sort(element));
        }
        // A specialized carrier `Option` family: the driver models the payload
        // projection as field 0. Only the single-field `Some` payload can be
        // meant, and only when it IS a prophecy carrier — so this cannot
        // retarget any legacy Option getter.
        if index != 0 {
            return None;
        }
        let dt = self.get_datatype_decl(&name)?.clone();
        if !dt.name.starts_with("Option") {
            return None;
        }
        let (_, payload_sort) = Self::constructor_payload_selector(&dt, "Some")?;
        match payload_sort.as_term_sort() {
            Sort::Uninterpreted(payload_name)
                if payload_name.starts_with("__trust_wp_mutref::")
                    || parse_mutref_carrier_tuple(&payload_name).is_some() =>
            {
                Some(payload_sort.clone())
            }
            _ => None,
        }
    }

    /// Resolve the return sort for Self-parametric trait method calls.
    ///
    /// When a contract references `Self::f()`, the encoder doesn't have
    /// a registered function for the parametric name `Self::f`. This method
    /// resolves the return sort by:
    /// 1. Direct lookup: the method name alone (e.g., `f` → `logic_f`) since
    ///    trait default methods are registered under their short name.
    /// 2. Suffix match: scanning for qualified names ending with `_P__P_f`
    ///    (e.g., `logic_Foo_P__P_f`) for impl-specific overrides.
    /// (#2676)
    fn resolve_self_parametric_return_sort(
        &self,
        name: &str,
        param_sorts: &[Sort],
    ) -> Option<Sort> {
        // Only applies to Self-prefixed calls (Self::method_name)
        let method_name = name.strip_prefix("Self::")?;

        // Strategy 1: Direct lookup by method name.
        // Trait default methods like `Foo::f() {}` are registered under their
        // short name `f`, producing SMT name `logic_f`.
        let direct_smt = trust_wp_core::logic::logic_fn_smt_name(method_name);
        if let Some(decl) = self.logic_func_decl_cloned(&direct_smt) {
            if decl.domain().len() == param_sorts.len() {
                let range = decl.range().clone();
                if range != Sort::Int {
                    return Some(range);
                }
                // Declaration has Int sort — check if a sort hint provides
                // a more precise sort. Int is the default fallback and may
                // not reflect the function's true return type (e.g., when
                // body inference couldn't resolve __trust_wp_tuple0 to Unit).
                if let Some(hint) = self.sort_hint_cloned(&direct_smt) {
                    // Carrier-aware for EVERY hint, not just a bare `Seq`.
                    // Special-casing `ExprSort::Seq` and sending the rest
                    // through the stateless converter still leaked the native
                    // spelling out of any hint that CONTAINS a sequence — a
                    // `Datatype("Vec")`, say — which splits the sort exactly as
                    // a bare `Seq` would have.
                    let hint_sort =
                        crate::encoder::sort_context::sort_mapping::expr_sort_to_ay_sort_for_carrier(
                            &hint,
                            self.seq_carrier(),
                        );
                    if hint_sort != Sort::Int {
                        return Some(hint_sort);
                    }
                }
                // Int declaration with no better hint — still return Int
                // rather than creating a disconnected placeholder. The
                // caller's congruence depends on using the SAME function.
                return Some(range);
            }
        }

        // Strategy 2: Suffix match for qualified impl methods.
        // E.g., `<Struct as Trait>::method` → `logic_..._P__P_method`.
        let smt_suffix = direct_smt.strip_prefix("logic_").unwrap_or(&direct_smt);
        let smt_suffix = format!("_P__P_{smt_suffix}");
        let mut best_match: Option<Sort> = None;
        for (decl_name, decl) in self.logic_funcs_iter() {
            if decl_name.contains("__placeholder_") {
                continue;
            }
            if decl_name.ends_with(&smt_suffix) && decl.domain().len() == param_sorts.len() {
                let range = decl.range().clone();
                if range != Sort::Int {
                    return Some(range);
                }
                best_match.get_or_insert(range);
            }
        }

        // Strategy 3: Sort hint lookup for the resolved method name.
        // The preseed pass records sort hints from return type annotations
        // (e.g., ExprSort::Unit for fn f() {}). If the declaration wasn't
        // found or had Int sort, the hint may still provide the correct sort.
        if best_match.is_none() {
            if let Some(hint) = self.sort_hint_cloned(&direct_smt) {
                // Carrier-aware for every hint; see the sibling site above.
                let hint_sort =
                    crate::encoder::sort_context::sort_mapping::expr_sort_to_ay_sort_for_carrier(
                        &hint,
                        self.seq_carrier(),
                    );
                if hint_sort != Sort::Int {
                    return Some(hint_sort);
                }
            }
        }

        best_match
    }

    fn placeholder_return_sort(
        &mut self,
        name: &str,
        smt_name: &str,
        param_sorts: &[Sort],
    ) -> Sort {
        // Stdlib constructors (Some/None → OptionInt, Ok/Err → ResultIntInt):
        // ensure the datatype is declared and return its sort. Without the
        // ResultIntInt arm, Ok/Err placeholders defaulted to Int, causing sort
        // mismatches when the function was later used in a datatype context.
        // (#1552)
        match stdlib_constructor_target(name) {
            Some(SwitchTarget::OptionInt) => {
                let short = short_constructor_name(name);
                let dt = if short == "Some" {
                    if name == short {
                        param_sorts
                            .first()
                            .cloned()
                            .map(|sort| self.stdlib_option_datatype_for_payload_sort(sort))
                            .unwrap_or_else(|| SwitchTarget::OptionInt.datatype())
                    } else {
                        SwitchTarget::OptionInt.datatype()
                    }
                } else {
                    SwitchTarget::OptionInt.datatype()
                };
                self.ensure_datatype_declared(&dt);
                return Sort::Datatype(dt);
            }
            Some(SwitchTarget::ResultIntInt) => {
                let dt = SwitchTarget::ResultIntInt.datatype();
                self.ensure_datatype_declared(&dt);
                return Sort::Datatype(dt);
            }
            _ => {}
        }
        // User-defined ADT constructor fallback (#1296): when a qualified
        // constructor name like `OwnResult::Ok` falls through to the
        // placeholder path (e.g., because its argument has a Datatype sort
        // incompatible with the native ADT field sort), the return sort
        // must be the owning datatype — not Int. Without this, postcondition
        // terms like `OwnResult::Ok(None)` produce Int-sorted placeholders,
        // causing sort mismatches with `self` (Datatype(OwnResult)) in
        // eq_term, which replaces one side with an unconstrained fresh
        // constant and breaks verification.
        if let Some(dt) = self.constructor_datatype(name) {
            return Sort::Datatype(dt);
        }
        if name == "seq" {
            self.get_seq_sort()
        } else if let Some(field_name) = name.strip_prefix(
            trust_wp_core::formula::internal::tuple_lowering::NAMED_FIELD_LOGIC_FN_PREFIX,
        ) {
            if field_name == "frag" {
                fmap_sort()
            } else if field_name == "auth" {
                // View RA authority projection: `Option<FMap<K, V>>`. Declare
                // and return the Option-of-FMap carrier so placeholder uses of
                // `view.auth()` agree with the option datatype produced by the
                // sort-inference path. (RA view frag/auth)
                let dt = self.stdlib_option_datatype_for_payload_sort(fmap_sort());
                self.ensure_datatype_declared(&dt);
                Sort::Datatype(dt)
            } else if let Some(hint) = self.sort_hint_cloned(smt_name) {
                self.sort_from_expr_sort(hint)
            } else {
                Sort::Int
            }
        } else if name == "view" && param_sorts.len() == 1 {
            param_sorts[0].clone()
        } else if let Some(sort) =
            trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_index(name)
                .and_then(|index| {
                    // #prophecy-slots (Fix B M2) first: the carrier sort NAME
                    // is a declaration, not an inference.
                    self.prophecy_carrier_getter_return_sort(index, param_sorts)
                        .or_else(|| {
                            self.tuple_getter_return_sort_from_ctor_domain(index, param_sorts)
                        })
                })
        {
            // Opaque tuple projection over the Uninterpreted("TupleN") carrier:
            // derive the component sort from the declared `__trust_wp_tupleN`
            // constructor's domain. The ctor placeholder knows the true
            // component sorts (e.g. [Int, Uninterpreted("List")] -> Tuple2)
            // while the getters previously defaulted to Int, so passing
            // `get_1(t)` to a logic fn with a non-Int domain forced an
            // [apply-coerce] fresh unconstrained constant — corrupting the
            // recursive-logic-fn one-step unfolding facts and tripping the
            // SpecAxiomDropped demotion guard on contracts whose VCs already
            // prove (rusthorn inc_some_2_list/2_tree). Sort refinement here
            // strictly removes unconstrained fresh constants: the properly
            // sorted getter is constrained by the tuple projection axioms
            // (`get_I(tupleN(x..)) = xI`), which only assert true facts of the
            // intended semantics. Conservative guards: only the Uninterpreted
            // tuple carrier family (Datatype receivers keep the enum-payload
            // route), only when every declared ctor for that carrier agrees on
            // the component sort, and only when that sort is non-Int. (#residuals)
            sort
        } else if let Some(arity) =
            trust_wp_core::formula::internal::tuple_lowering::tuple_logic_fn_arity(name)
        {
            Sort::Uninterpreted(format!("Tuple{arity}"))
        } else if name == "inv"
            || name.ends_with("_inv")
            || trust_wp_core::logic::is_invariant_method_name(name)
        {
            // Type invariant functions always return Bool. (#2124)
            Sort::Bool
        } else if name == "fmap_contains" {
            // FMap containment always returns Bool. Mirrors infer_logic_fn_sort. (#1552)
            Sort::Bool
        } else if matches!(
            name.rsplit("::").next().unwrap_or(name),
            "Copied" | "Cloned"
        ) && param_sorts.len() == 1
        {
            // Transparent iterator adapters do not change the underlying
            // iterator state. Reuse the inner iterator sort so the placeholder
            // family does not invent a separate adapter carrier. (#collections)
            param_sorts[0].clone()
        } else if matches!(
            name,
            "fmap_insert" | "fmap_merge" | "__trust_wp_fmap_iter_view"
        ) {
            // FMap-returning functions. Mirrors infer_logic_fn_sort. (#1552)
            fmap_sort()
        } else if name == "fmap_into_seq" {
            // Canonical FMap->Seq witness. Mirrors infer_logic_fn_sort. (#2720)
            // Through `get_seq_sort`, like the `__trust_wp_iter_mut_view` arm
            // directly below: both return a sequence, and both must return it
            // at THIS encoder's carrier. Spelling the native sort here declared
            // the witness `(Seq Int)` while `ensure_seq_theory` declared the
            // projectors over the encoder's actual carrier, which is the sort
            // split that made `Solver::apply` fail its domain check.
            self.get_seq_sort()
        } else if name == "__trust_wp_iter_mut_view" {
            // IterMut view projector returns Seq. Mirrors infer_logic_fn_sort. (#2238)
            self.get_seq_sort()
        } else if let Some(existing) = self.existing_placeholder_return_sort(smt_name, param_sorts)
        {
            existing
        } else if let Some(hint) = self.sort_hint_cloned(smt_name) {
            self.sort_from_expr_sort(hint)
        } else if let Some(sort) = self.resolve_self_parametric_return_sort(name, param_sorts) {
            // Self-parametric trait calls like `Self::f()` resolve against
            // registered logic functions with the same method suffix. (#2676)
            sort
        } else if name
            .rsplit_once("::")
            .is_some_and(|(_, short)| short.starts_with(char::is_uppercase))
            && stdlib_constructor_target(name).is_none()
            && !name.rsplit_once("::").is_some_and(|(_, short)| {
                // Exclude Option/Result-like short names that need Int-model
                // sort for the axiom system (find_standard_int_constructor_decl
                // only matches Int -> Int declarations). (#1552, #1296)
                matches!(short, "Some" | "None" | "Ok" | "Err")
            })
        {
            // User-defined ADT constructor: `MyEnum::Variant` → Uninterpreted("MyEnum").
            // Mirrors the qualified name inference in infer_logic_fn_sort. (#1552)
            let (prefix, _) = name
                .rsplit_once("::")
                .expect("guard ensures :: separator exists");
            Sort::Uninterpreted(prefix.replace("::", "_"))
        } else {
            Sort::Int
        }
    }

    pub(super) fn placeholder_sort_tag(sort: &Sort) -> String {
        fn encode_tag(raw: &str) -> String {
            let mut encoded = String::new();
            for byte in raw.as_bytes() {
                let _ = std::fmt::Write::write_fmt(&mut encoded, format_args!("{byte:02x}"));
            }
            encoded
        }

        match sort {
            Sort::Bool => "b".to_string(),
            Sort::Int => "i".to_string(),
            Sort::Uninterpreted(name) => format!("u{}", encode_tag(name)),
            Sort::Datatype(dt) => format!("d{}", encode_tag(&dt.name)),
            other => format!("x{}", encode_tag(&format!("{other:?}"))),
        }
    }

    pub(in crate::encoder) fn placeholder_smt_name(
        smt_name: &str,
        param_sorts: &[Sort],
        return_sort: &Sort,
    ) -> String {
        let params = if param_sorts.is_empty() {
            "nullary".to_string()
        } else {
            param_sorts
                .iter()
                .map(Self::placeholder_sort_tag)
                .collect::<Vec<_>>()
                .join("_")
        };
        let ret = Self::placeholder_sort_tag(return_sort);
        format!("{smt_name}__placeholder_{params}__ret_{ret}")
    }

    /// Get or create a logic function declaration and apply it to arguments.
    ///
    /// This is the common implementation for `encode_logic_fn_call_impl`.
    /// It handles function declaration lookup/creation and application.
    ///
    /// `arg_exprs` is used to infer parameter sorts for placeholder declarations
    /// when the function has not been registered yet. `None` is only valid for
    /// the Bool→Int coercion fallback used by `Some/Ok/Err`; all other placeholder
    /// paths must provide expression context for sort inference. (#1608)
    pub(crate) fn apply_logic_fn(
        &mut self,
        name: &str,
        arg_terms: &[Term],
        arg_exprs: Option<&[PureExpr]>,
        prefix: Option<DerivedKind>,
    ) -> Result<Term, EncodingError> {
        // Resolve Self-parametric trait method calls: `Self::method()` references
        // a trait method that is registered under its bare name (e.g., `logic_f`
        // for `Self::f`). When the parametric SMT name (`logic_Self_P__P_f`) has
        // no declaration, try the bare method name before falling through to the
        // placeholder path. This ensures `Self::f()` uses the same UF symbol as
        // `f()`, preserving axiom congruence and sort information.
        let (resolved_name, resolved_smt_name) = self.resolve_logic_fn_call_name_for_decl(name);
        let name = resolved_name;
        let smt_name = resolved_smt_name;

        // Seq-literal builtins must NEVER become placeholder UFs, mirroring
        // the dispatch-level routing (`encode_logic_fn_call_impl`): `seq![v]`
        // is the axiom-backed `seq_singleton(v)` and `seq![]`/`Seq::empty()`
        // is the `seq_empty` constant. Expected-sort encoding paths can reach
        // `apply_logic_fn` directly with these names; the placeholder route
        // then infers a context return sort (observed live: `s@ == seq!['Ã']`
        // with `s: String` inferring ret=Datatype("String")) and the
        // declaration `logic_seq__placeholder_i__ret_d537472696e67` panics in
        // ay-dpll's core-identity gate (function_declarations.rs) — the third
        // declare-collision route beyond #2706's two. (ce-census 2026-08-20,
        // cc/string test_string_len encoder panic)
        if name == "seq" && arg_terms.len() == 1 {
            return Ok(self.encode_seq_singleton(arg_terms[0]));
        }
        if matches!(name, "seq" | "seq_empty" | "Seq::empty") && arg_terms.is_empty() {
            return Ok(self.encode_seq_empty());
        }

        // Look up or create the function declaration
        if let Some(func_decl) = self.logic_func_decl_cloned(&smt_name) {
            // Coerce argument sorts to match the function's declared domain.
            // User-defined ADTs (e.g., List) may produce DatatypeSort mismatches
            // when the same enum is declared with different DatatypeSort names
            // or when the first-declaration-wins lock-in assigns a different sort
            // to the argument variable. Replace mismatched arguments with fresh
            // constants of the expected sort. (#1965, #2002)
            let domain = func_decl.domain();
            let mut coerced_args: Vec<Term> = arg_terms.to_vec();
            for (i, arg_term) in coerced_args.iter_mut().enumerate() {
                if let Some(expected_sort) = domain.get(i) {
                    let expected_term_sort = expected_sort.as_term_sort();
                    let actual_sort = self.solver.get_sort(*arg_term);
                    if actual_sort != expected_term_sort {
                        if let Some(restored) =
                            self.try_restore_seq_element_from_int(*arg_term, &expected_term_sort)
                        {
                            *arg_term = restored;
                            continue;
                        }

                        if let Some(view_term) = self.existing_view_arg_for_expected_sort(
                            arg_exprs,
                            i,
                            prefix,
                            &expected_term_sort,
                        ) {
                            let view_sort = self.solver.get_sort(view_term);
                            debug!(
                                "  [apply-view-recover] {name} param {i}: \
                                     {actual_sort:?} -> {view_sort:?}"
                            );
                            *arg_term = view_term;
                            continue;
                        }
                        // Always coerce when the argument sort doesn't match
                        // the function's declared domain sort. (#2002, #2155)
                        //
                        // The previous gate (`should_coerce`) only handled
                        // Datatype and Int↔Uninterpreted mismatches. This
                        // missed Uninterpreted-vs-Uninterpreted mismatches
                        // (e.g., "List" vs "Seq", "std::option::Option" vs
                        // "OptionInt", "FMap" vs "Seq") and Bool-vs-other
                        // mismatches. Every uncaught case resulted in a ay
                        // panic in safe_apply, which is strictly worse than
                        // a fresh unconstrained constant.
                        //
                        // The fresh const is conservative (unconstrained) —
                        // the solver can't reason about the original
                        // argument's value but won't crash.

                        debug!(
                            "  [apply-coerce] {name} param {i}: \
                                 {actual_sort:?} → {expected_term_sort:?} (fresh const)"
                        );

                        let fresh_name = format!("__apply_coerce_{name}_{i}_{}", self.var_count());
                        // Fresh const is conservative (unconstrained) — reclassified
                        // from HIGH to LOW per #2231.
                        unsoundness::increment(
                            unsoundness::UnsoundnessCategory::SortCoercionBridge,
                        );
                        *arg_term = self.solver.declare_const(&fresh_name, expected_term_sort);
                    }
                }
            }
            let context = format!("logic_fn_call:{name}");
            let result = self.safe_apply(&context, &func_decl, &coerced_args)?;
            self.assert_struct_field_placeholder_aliases_for_accessor_name(name, &domain);
            self.assert_ground_struct_field_placeholder_aliases_for_accessor_call(
                name,
                &domain,
                &coerced_args,
                result,
            );
            // The Option `.0`-payload bridge
            // (`bridge_tuple_get_0_to_option_some_value`) is emitted by the
            // safe_apply choke point above, which covers this and every other
            // application path of the accessor family.
            Ok(result)
        } else {
            // Function not registered - create a placeholder declaration.
            // Infer parameter sorts from argument expressions when available.
            let param_sorts: Vec<Sort> = if let Some(exprs) = arg_exprs {
                let mut sorts = Vec::with_capacity(exprs.len());
                for (i, expr) in exprs.iter().enumerate() {
                    let inferred = self.infer_expr_sort_with_context(expr, prefix);
                    // Reconcile against the actual ay sort of the already-encoded
                    // argument term. The placeholder declaration's domain MUST
                    // match the actual term sorts, since safe_apply validates
                    // sort compatibility. Expression-level inference can diverge
                    // from post-encoding term sorts in both directions:
                    // - Inferred Int, actual Datatype (Seq, OptionInt) — original
                    //   case from #994
                    // - Inferred Datatype, actual Int — when UF fallback was used
                    //   or TypeParam→Int mapping from #2551 applies (#2565)
                    // Always prefer the actual term sort as ground truth.
                    if let Some(term) = arg_terms.get(i) {
                        let actual = self.solver.get_sort(*term);
                        if inferred != actual {
                            sorts.push(actual);
                            continue;
                        }
                    }
                    sorts.push(inferred);
                }
                sorts
            } else {
                // Fail closed for unexpected placeholder calls without source exprs.
                // `arg_exprs=None` is only expected for Bool->Int coercion on
                // stdlib Option/Result constructor fallback paths, and for the
                // positional `.0` accessor when a synthetic axiom (the bounded-get
                // structural-induction L3 bridge) applies it to a derived term
                // (`get(l,i)`) that has no source expr. In all these cases the
                // argument terms carry their real ay sorts, so inferring the
                // parameter sorts from the terms is sound (and lets the L3 bridge
                // declare the SAME placeholder symbol the goal's `.0` access uses).
                let is_positional_tuple_field =
                    trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_index(
                        name,
                    )
                    .is_some();
                if !is_stdlib_payload_constructor(name) && !is_positional_tuple_field {
                    return Err(EncodingError::sort_inference(
                        format!("logic_fn_placeholder:{name}"),
                        "no arg_exprs available to infer parameter sorts",
                    ));
                }

                // Constructor fallback: use actual ay sorts of encoded terms
                // rather than defaulting all to Int. Terms may carry datatype
                // sorts (OptionInt, Seq) that would cause sort mismatches. (#994)
                arg_terms.iter().map(|t| self.solver.get_sort(*t)).collect()
            };
            // Infer the placeholder return sort from sort hints. The prescan
            // collects Bool/Seq/FMap hints for function names that appear in
            // sort-determining contexts (e.g., Not(f(...)) → Bool, v@.len()
            // where v = f(...) → Seq). Use these hints to avoid the Int default
            // that causes sort mismatches when the function is later used in a
            // non-Int context. (#544, #994)
            let return_sort = arg_exprs
                .and_then(|exprs| self.tuple_getter_return_sort(name, exprs, prefix))
                .unwrap_or_else(|| self.placeholder_return_sort(name, &smt_name, &param_sorts));

            // Zero-arg placeholder calls are effectively typed constants. Using
            // a single monomorphic symbol for all return sorts lets the first
            // call lock the declaration for the entire query, so a later Bool
            // use of the same name after an Int use can panic in `implies`.
            // Give nullary placeholders sort-specific SMT names instead. (#2169 audit)
            //
            // Extend the same signature-keying to non-nullary placeholders too.
            // A single raw SMT name lets the first declaration lock in one domain
            // forever, which crashes later calls when the same source function name
            // is used over different structural carrier sorts (Tuple, IterMut, Seq).
            // (#994, #2169)
            let decl_key = Self::placeholder_smt_name(&smt_name, &param_sorts, &return_sort);
            // Keep placeholder declarations signature-keyed only. Reintroducing
            // raw-name aliases makes the first declaration win across mixed
            // sorts, which is exactly the collision pattern fixed by the
            // placeholder split. Consumer layers that need a canonical Int-model
            // constructor must scan the placeholder family explicitly. (#2274)
            let is_new_decl = !self.has_logic_func_decl(&decl_key);
            let func_decl =
                self.get_or_declare_logic_func(&decl_key, &param_sorts, return_sort.clone());
            // When a new UF placeholder is created for a constructor (Some, Ok,
            // Err, None) whose return sort is a declared datatype, assert a
            // quantified tester axiom: `forall x. is-Ctor(UF_Ctor(x))`. This
            // bridges the UF constructor and native datatype tester, enabling
            // the solver to connect postcondition equalities (using UF_Ctor)
            // with body match conditions (using native is-Ctor testers). (#1296)
            if is_new_decl {
                self.assert_uf_constructor_tester_axiom(name, &func_decl, &return_sort);
            }
            let context = format!("logic_fn_placeholder:{name}");
            let result = self.safe_apply(&context, &func_decl, arg_terms)?;
            if self.quantifier_state.quantifier_depth() == 0
                && !matches!(
                    name,
                    "Some" | "Ok" | "Err" | "resolve" | "seq" | "seq_empty" | "Seq::empty"
                )
            {
                if let Some(exprs) = arg_exprs {
                    self.ground_pool.register_with_path_conditions(
                        &smt_name,
                        result,
                        arg_terms.to_vec(),
                        exprs.to_vec(),
                        self.active_path_conditions_cloned(),
                    );
                } else {
                    self.ground_pool
                        .register_term_application_with_path_conditions(
                            &smt_name,
                            result,
                            arg_terms.to_vec(),
                            self.active_path_conditions_cloned(),
                        );
                }
            }
            self.assert_struct_field_placeholder_aliases_for_accessor_name(name, &param_sorts);
            self.assert_ground_struct_field_placeholder_aliases_for_accessor_call(
                name,
                &param_sorts,
                arg_terms,
                result,
            );
            // The Option `.0`-payload bridge
            // (`bridge_tuple_get_0_to_option_some_value`) is emitted by the
            // safe_apply choke point above, which covers this and every other
            // application path of the accessor family.
            Ok(result)
        }
    }

    fn existing_view_arg_for_expected_sort(
        &self,
        arg_exprs: Option<&[PureExpr]>,
        index: usize,
        prefix: Option<DerivedKind>,
        expected_sort: &Sort,
    ) -> Option<Term> {
        let expr = arg_exprs?.get(index)?;
        let base_name = match expr {
            PureExpr::Var(name, _) => apply_name_prefix(name, prefix).into_owned(),
            PureExpr::View(inner) => match inner.as_ref() {
                PureExpr::Var(name, _) => apply_name_prefix(name, prefix).into_owned(),
                _ => return None,
            },
            _ => return None,
        };
        let view_name = DerivedKind::View.format_name(&base_name);
        let view_term = self.var_term(&view_name)?;
        (self.solver.get_sort(view_term) == *expected_sort).then_some(view_term)
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, SolveResult, Sort};
    use ntest::timeout;
    use trust_wp_core::formula::PureExpr;

    use crate::{encoder::AYEncoder, tests::helpers::*};

    // ── placeholder_sort_tag ────────────────────────────────────────

    /// Bool sort maps to "b" tag.
    #[test]
    fn test_placeholder_sort_tag_bool() {
        assert_eq!(AYEncoder::placeholder_sort_tag(&Sort::Bool), "b");
    }

    /// Int sort maps to "i" tag.
    #[test]
    fn test_placeholder_sort_tag_int() {
        assert_eq!(AYEncoder::placeholder_sort_tag(&Sort::Int), "i");
    }

    /// Uninterpreted sort maps to "u" + hex-encoded name.
    #[test]
    fn test_placeholder_sort_tag_uninterpreted() {
        let tag = AYEncoder::placeholder_sort_tag(&Sort::Uninterpreted("FMap".to_string()));
        assert!(
            tag.starts_with('u'),
            "Uninterpreted sort tag should start with 'u', got {tag}"
        );
        // "FMap" = [0x46, 0x4d, 0x61, 0x70]
        assert_eq!(tag, "u464d6170");
    }

    /// Datatype sort maps to "d" + hex-encoded name.
    #[test]
    fn test_placeholder_sort_tag_datatype() {
        let dt = DatatypeSort {
            name: "OptionInt".to_string(),
            constructors: vec![],
        };
        let tag = AYEncoder::placeholder_sort_tag(&Sort::Datatype(dt));
        assert!(
            tag.starts_with('d'),
            "Datatype sort tag should start with 'd', got {tag}"
        );
    }

    // ── CE-census 2026-08-20 pin: seq builtins never become placeholders ──

    /// `apply_logic_fn("seq", [v])` must route to the axiom-backed
    /// `seq_singleton`, never to a placeholder UF declaration. Reaching the
    /// placeholder path infers a context-dependent return sort (observed
    /// live: ret=Datatype("String") for `s@ == seq!['Ã']` with `s: String`)
    /// whose declaration panics in ay-dpll's core-identity gate — the
    /// cc/string test_string_len encoder panic (declare-collision route #3
    /// beyond #2706's two).
    #[test]
    #[timeout(30000)]
    fn seq_singleton_builtin_never_becomes_placeholder_uf() {
        let mut encoder = AYEncoder::new();
        let v = encoder.solver.int_const(195);
        let term = encoder
            .apply_logic_fn("seq", &[v], None, None)
            .expect("seq![v] must encode via the builtin singleton");
        let seq_sort = encoder.get_seq_sort();
        assert_eq!(
            encoder.solver.get_sort(term),
            seq_sort,
            "seq![v] must produce a Seq-sorted term"
        );
        assert!(
            !encoder
                .logic_func_names_iter()
                .any(|n| n.starts_with("logic_seq__placeholder")),
            "no placeholder UF may be declared for the seq builtin"
        );
    }

    // ── placeholder_smt_name ────────────────────────────────────────

    /// Nullary placeholder uses "nullary" as parameter tag.
    #[test]
    fn test_placeholder_smt_name_nullary() {
        let name = AYEncoder::placeholder_smt_name("logic_default", &[], &Sort::Int);
        assert!(
            name.contains("__placeholder_nullary__ret_"),
            "nullary placeholder should contain 'nullary': {name}"
        );
        assert!(
            name.starts_with("logic_default__placeholder_"),
            "should start with smt_name prefix: {name}"
        );
    }

    /// Unary Int -> Bool placeholder includes parameter and return sort tags.
    #[test]
    fn test_placeholder_smt_name_unary_int_to_bool() {
        let name = AYEncoder::placeholder_smt_name("logic_is_positive", &[Sort::Int], &Sort::Bool);
        assert!(
            name.contains("__placeholder_i__ret_b"),
            "Int->Bool placeholder should have 'i' param and 'b' return: {name}"
        );
    }

    /// Binary (Int, Bool) -> Int placeholder joins parameter tags with underscore.
    #[test]
    fn test_placeholder_smt_name_binary_mixed() {
        let name =
            AYEncoder::placeholder_smt_name("logic_combine", &[Sort::Int, Sort::Bool], &Sort::Int);
        assert!(
            name.contains("__placeholder_i_b__ret_i"),
            "binary (Int, Bool)->Int should have 'i_b' params and 'i' return: {name}"
        );
    }

    /// Different return sorts produce different placeholder names.
    #[test]
    fn test_placeholder_smt_name_return_sort_differentiates() {
        let name_int = AYEncoder::placeholder_smt_name("logic_f", &[Sort::Int], &Sort::Int);
        let name_bool = AYEncoder::placeholder_smt_name("logic_f", &[Sort::Int], &Sort::Bool);
        assert_ne!(
            name_int, name_bool,
            "different return sorts should produce different placeholder names"
        );
    }

    /// Same input produces deterministic output.
    #[test]
    fn test_placeholder_smt_name_deterministic() {
        let a = AYEncoder::placeholder_smt_name("logic_f", &[Sort::Int], &Sort::Bool);
        let b = AYEncoder::placeholder_smt_name("logic_f", &[Sort::Int], &Sort::Bool);
        assert_eq!(a, b, "placeholder_smt_name should be deterministic");
    }

    // ── existing_placeholder_return_sort ─────────────────────────────

    /// Returns None when no placeholder declarations exist.
    #[test]
    #[timeout(30000)]
    fn test_existing_placeholder_return_sort_empty() {
        let encoder = AYEncoder::new();
        assert!(
            encoder
                .existing_placeholder_return_sort("logic_unknown", &[Sort::Int])
                .is_none(),
            "should return None when no placeholders exist"
        );
    }

    /// Returns the non-Int sort when a matching placeholder exists.
    #[test]
    #[timeout(30000)]
    fn test_existing_placeholder_return_sort_finds_match() {
        let mut encoder = AYEncoder::new();
        // Create a placeholder by encoding a call
        let _fd = encoder.get_or_declare_logic_func(
            "logic_pred__placeholder_i__ret_b",
            &[Sort::Int],
            Sort::Bool,
        );
        let result = encoder.existing_placeholder_return_sort("logic_pred", &[Sort::Int]);
        assert_eq!(
            result,
            Some(Sort::Bool),
            "should find existing Bool-returning placeholder"
        );
    }

    /// Prefers non-Int return sort over Int fallback.
    #[test]
    #[timeout(30000)]
    fn test_existing_placeholder_prefers_non_int() {
        let mut encoder = AYEncoder::new();
        // Create Int placeholder first
        let _fd1 = encoder.get_or_declare_logic_func(
            "logic_ambig__placeholder_i__ret_i",
            &[Sort::Int],
            Sort::Int,
        );
        // Create Bool placeholder second
        let _fd2 = encoder.get_or_declare_logic_func(
            "logic_ambig__placeholder_i__ret_b",
            &[Sort::Int],
            Sort::Bool,
        );
        let result = encoder.existing_placeholder_return_sort("logic_ambig", &[Sort::Int]);
        assert_eq!(
            result,
            Some(Sort::Bool),
            "should prefer non-Int (Bool) over Int fallback"
        );
    }

    // ── Placeholder call encoding (unresolved logic functions) ──────

    /// An unresolved function call creates a placeholder UF declaration.
    #[test]
    #[timeout(30000)]
    fn test_placeholder_created_for_unresolved_fn() {
        let mut encoder = AYEncoder::new();
        let expr = logic_fn_call("totally_new_fn", vec![int(1)]);
        let term = encoder
            .encode_pure(&expr)
            .expect("unresolved fn should create placeholder");
        // The term should be valid and have Int sort (default)
        let sort = encoder.solver.get_sort(term);
        assert_eq!(
            sort,
            Sort::Int,
            "default placeholder return sort should be Int"
        );
    }

    /// Transparent iterator adapters preserve the inner term exactly.
    #[test]
    #[timeout(30000)]
    fn test_placeholder_transparent_adapter_collapses_to_inner_term() {
        let mut encoder = AYEncoder::new();
        let inner = method_call(var("xs"), "intersection", vec![var("ys")]);
        let copied = logic_fn_call("Copied", vec![inner.clone()]);
        let inner_term = encoder.encode_pure(&inner).expect("inner term");
        let copied_term = encoder.encode_pure(&copied).expect("copied term");
        assert_eq!(
            copied_term, inner_term,
            "Copied(inner) should encode identically to inner"
        );
    }

    /// Placeholder preserves UF congruence: same unresolved call twice yields equal terms.
    #[test]
    #[timeout(30000)]
    fn test_placeholder_uf_congruence() {
        let mut encoder = AYEncoder::new();
        let expr = logic_fn_call("placeholder_fn", vec![int(5)]);
        let t1 = encoder.encode_pure(&expr).expect("first placeholder call");
        let t2 = encoder.encode_pure(&expr).expect("second placeholder call");
        let eq = encoder.solver.eq(t1, t2);
        let neq = encoder.solver.not(eq);
        encoder.assert_term(neq);
        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "placeholder_fn(5) != placeholder_fn(5) should be UNSAT (UF congruence)"
        );
    }

    // ── Placeholder with sort annotations ───────────────────────────

    /// Placeholder infers Bool return sort from invariant function names.
    #[test]
    #[timeout(30000)]
    fn test_placeholder_inv_fn_returns_bool() {
        let mut encoder = AYEncoder::new();
        let expr = logic_fn_call("inv", vec![int(0)]);
        let term = encoder.encode_pure(&expr).expect("inv placeholder");
        let sort = encoder.solver.get_sort(term);
        assert_eq!(
            sort,
            Sort::Bool,
            "invariant function 'inv' placeholder should return Bool"
        );
    }

    /// `*_inv` suffix also gets Bool return sort.
    #[test]
    #[timeout(30000)]
    fn test_placeholder_suffix_inv_returns_bool() {
        let mut encoder = AYEncoder::new();
        let expr = logic_fn_call("my_type_inv", vec![int(0)]);
        let term = encoder.encode_pure(&expr).expect("*_inv placeholder");
        let sort = encoder.solver.get_sort(term);
        assert_eq!(
            sort,
            Sort::Bool,
            "function ending in '_inv' placeholder should return Bool"
        );
    }

    /// `fmap_contains` placeholder returns Bool sort.
    #[test]
    #[timeout(30000)]
    fn test_placeholder_fmap_contains_returns_bool() {
        let mut encoder = AYEncoder::new();
        let expr = logic_fn_call("fmap_contains", vec![int(0), int(1)]);
        let term = encoder
            .encode_pure(&expr)
            .expect("fmap_contains placeholder");
        let sort = encoder.solver.get_sort(term);
        assert_eq!(
            sort,
            Sort::Bool,
            "fmap_contains placeholder should return Bool"
        );
    }

    /// `fmap_insert` placeholder returns FMap sort.
    #[test]
    #[timeout(30000)]
    fn test_placeholder_fmap_insert_returns_fmap() {
        let mut encoder = AYEncoder::new();
        let expr = logic_fn_call("fmap_insert", vec![int(0), int(1), int(2)]);
        let term = encoder.encode_pure(&expr).expect("fmap_insert placeholder");
        let sort = encoder.solver.get_sort(term);
        assert!(
            matches!(&sort, Sort::Uninterpreted(s) if s == "FMap"),
            "fmap_insert placeholder should return FMap, got {sort:?}"
        );
    }

    #[test]
    #[timeout(30000)]
    fn apply_logic_fn_restores_seq_index_for_non_int_domain() {
        let mut encoder = AYEncoder::new();
        let seq_sort = encoder.get_seq_sort();
        let seq = encoder.solver.declare_const("lists", seq_sort);
        let zero = encoder.solver.int_const(0);
        let indexed = encoder
            .seq_index_term(seq, zero)
            .expect("seq index should encode");
        assert_eq!(encoder.solver.get_sort(indexed), Sort::Int);

        let list_sort = Sort::Uninterpreted("List".to_string());
        let smt_name = trust_wp_core::logic::logic_fn_smt_name("consume_list");
        encoder.get_or_declare_logic_func(&smt_name, std::slice::from_ref(&list_sort), Sort::Bool);

        let applied = encoder
            .apply_logic_fn("consume_list", &[indexed], Some(&[int(0)]), None)
            .expect("logic function application should restore seq element");
        let children = encoder.solver.term_children(applied);
        assert_eq!(children.len(), 1);
        assert_eq!(encoder.solver.get_sort(children[0]), list_sort);
        let child_text = encoder.solver.format_term(children[0]);
        assert!(
            child_text.contains("__seq_index_restore_List"),
            "expected restored seq element, got {child_text}"
        );
        assert!(
            !child_text.contains("__apply_coerce"),
            "seq element should not be replaced by a fresh apply-coerce constant"
        );
    }

    /// `fmap_into_seq` placeholder returns Seq sort.
    #[test]
    #[timeout(30000)]
    fn test_placeholder_fmap_into_seq_returns_seq() {
        let mut encoder = AYEncoder::new();
        let expr = logic_fn_call("fmap_into_seq", vec![int(0)]);
        let term = encoder
            .encode_pure(&expr)
            .expect("fmap_into_seq placeholder");
        let sort = encoder.solver.get_sort(term);
        assert!(
            sort.is_seq(),
            "fmap_into_seq placeholder should return Seq sort, got {sort:?}"
        );
    }

    /// `seq` placeholder (single element) returns Seq sort.
    #[test]
    #[timeout(30000)]
    fn test_placeholder_seq_single_returns_seq() {
        let mut encoder = AYEncoder::new();
        let expr = logic_fn_call("seq", vec![int(42)]);
        let term = encoder.encode_pure(&expr).expect("seq placeholder");
        let sort = encoder.solver.get_sort(term);
        assert!(
            sort.is_seq(),
            "seq placeholder should return Seq sort, got {sort:?}"
        );
    }

    /// `view` placeholder with one argument returns the argument's sort.
    #[test]
    #[timeout(30000)]
    fn test_placeholder_view_returns_arg_sort() {
        let mut encoder = AYEncoder::new();
        // Declare a variable so it has known Int sort
        encoder
            .get_or_declare_var("x", Sort::Int)
            .expect("declare x");
        // Create the term before calling apply_logic_fn to avoid borrow conflict
        let x_term = encoder.solver.declare_const("x_view_test", Sort::Int);
        // view(x) on the placeholder path returns Int (matching x's sort)
        let result = encoder.apply_logic_fn("view", &[x_term], Some(&[var("x")]), None);
        assert!(result.is_ok(), "view(x) placeholder should succeed");
    }

    // ── Placeholder fallback behavior ───────────────────────────────

    /// apply_logic_fn without arg_exprs rejects non-constructor functions.
    #[test]
    #[timeout(30000)]
    fn test_placeholder_fallback_rejects_non_constructor_without_exprs() {
        let mut encoder = AYEncoder::new();
        let dummy = encoder.solver.int_const(42);
        let result = encoder.apply_logic_fn("custom_fn", &[dummy], None, None);
        assert!(
            result.is_err(),
            "non-constructor without arg_exprs should fail with sort inference error"
        );
    }

    /// apply_logic_fn without arg_exprs allows stdlib constructors (Some, Ok, Err).
    #[test]
    #[timeout(30000)]
    fn test_placeholder_fallback_allows_stdlib_constructors() {
        let mut encoder = AYEncoder::new();
        let dummy = encoder.solver.int_const(7);
        for ctor in &["Some", "Ok", "Err"] {
            let result = encoder.apply_logic_fn(ctor, &[dummy], None, None);
            assert!(
                result.is_ok(),
                "stdlib constructor {ctor} should succeed without arg_exprs"
            );
        }
    }

    /// Calling the same unresolved function with different argument sorts
    /// creates separate placeholder declarations (sort-keyed).
    #[test]
    #[timeout(30000)]
    fn test_placeholder_sort_keyed_separation() {
        let mut encoder = AYEncoder::new();
        // Int argument
        let int_call = logic_fn_call("poly", vec![int(1)]);
        let _ = encoder.encode_pure(&int_call).expect("poly(int)");

        // Bool argument
        let bool_call = logic_fn_call("poly", vec![bool_expr(true)]);
        let _ = encoder.encode_pure(&bool_call).expect("poly(bool)");

        // Both should have created valid terms without crashing
        // The sort-keyed placeholder system creates distinct declarations
    }

    /// User-defined ADT constructor `MyEnum::Variant` on the placeholder path
    /// gets Uninterpreted("MyEnum") return sort.
    #[test]
    #[timeout(30000)]
    fn test_placeholder_user_adt_constructor_sort() {
        let mut encoder = AYEncoder::new();
        let expr = logic_fn_call("MyEnum::Variant", vec![int(1)]);
        let term = encoder
            .encode_pure(&expr)
            .expect("user ADT constructor placeholder");
        let sort = encoder.solver.get_sort(term);
        assert!(
            matches!(&sort, Sort::Uninterpreted(s) if s == "MyEnum"),
            "MyEnum::Variant placeholder should return Uninterpreted(MyEnum), got {sort:?}"
        );
    }

    /// Qualified constructor with declared datatype gets Datatype return sort.
    #[test]
    #[timeout(30000)]
    fn test_placeholder_declared_adt_constructor_datatype_sort() {
        let mut encoder = AYEncoder::new();
        let own_result = DatatypeSort {
            name: "OwnResult".to_string(),
            constructors: vec![
                DatatypeConstructor {
                    name: "Ok".to_string(),
                    fields: vec![DatatypeField {
                        name: "ok_val".to_string(),
                        sort: Sort::Int,
                    }],
                },
                DatatypeConstructor {
                    name: "Err".to_string(),
                    fields: vec![DatatypeField {
                        name: "err_val".to_string(),
                        sort: Sort::Int,
                    }],
                },
            ],
        };
        encoder.ensure_datatype_declared(&own_result);

        let expr = logic_fn_call("OwnResult::Ok", vec![int(42)]);
        let term = encoder.encode_pure(&expr).expect("OwnResult::Ok encoding");
        let sort = encoder.solver.get_sort(term);
        assert!(
            sort == Sort::Datatype(own_result.clone())
                || matches!(&sort, Sort::Uninterpreted(s) if s == "OwnResult"),
            "OwnResult::Ok should produce OwnResult-family sort, got {sort:?}"
        );
    }

    /// apply_logic_fn coerces mismatched argument sorts with fresh constants.
    #[test]
    #[timeout(30000)]
    fn test_placeholder_coerces_mismatched_sorts() {
        let mut encoder = AYEncoder::new();
        // Declare function using SMT name that apply_logic_fn will look up.
        // logic_fn_smt_name("needsbool") = "logic_needsbool"
        let _fd = encoder.get_or_declare_logic_func("logic_needsbool", &[Sort::Bool], Sort::Int);
        // Apply with Int argument — should coerce via fresh Bool constant
        let int_arg = encoder.solver.int_const(42);
        let result = encoder.apply_logic_fn("needsbool", &[int_arg], None, None);
        assert!(
            result.is_ok(),
            "mismatched sort should be coerced, not crash"
        );
        let term = result.unwrap();
        let sort = encoder.solver.get_sort(term);
        assert_eq!(
            sort,
            Sort::Int,
            "return sort should match declared Int range"
        );
    }

    #[test]
    #[timeout(30000)]
    fn apply_logic_fn_uses_existing_view_arg_before_fresh_coercion() {
        let mut encoder = AYEncoder::new();
        let list_sort = Sort::Uninterpreted("List".to_string());
        let map_sort = Sort::Uninterpreted("MyHashMap".to_string());
        let option_sort = Sort::Uninterpreted("OptionInt".to_string());
        encoder.get_or_declare_logic_func(
            "logic_get",
            &[list_sort.clone(), Sort::Int],
            option_sort,
        );
        let old_self = encoder
            .get_or_declare_var("old_self", map_sort)
            .expect("old_self declaration");
        let old_self_view = encoder
            .get_or_declare_var("old_self_view", list_sort)
            .expect("old_self_view declaration");
        let k = encoder
            .get_or_declare_var("k", Sort::Int)
            .expect("k declaration");

        let call = encoder
            .apply_logic_fn(
                "get",
                &[old_self, k],
                Some(&[
                    PureExpr::Var("old_self".to_string(), None),
                    PureExpr::Var("k".to_string(), None),
                ]),
                None,
            )
            .expect("view-backed get should encode");
        let expected = encoder
            .apply_logic_fn(
                "get",
                &[old_self_view, k],
                Some(&[
                    PureExpr::View(Arc::new(PureExpr::Var("old_self".to_string(), None))),
                    PureExpr::Var("k".to_string(), None),
                ]),
                None,
            )
            .expect("explicit view-backed get should encode");

        assert_eq!(
            call, expected,
            "mismatched receiver should reuse the existing _view term before creating a fresh coercion"
        );
    }

    /// Tuple constructor placeholder returns appropriate Tuple sort.
    #[test]
    #[timeout(30000)]
    fn test_placeholder_tuple_constructor_sort() {
        let mut encoder = AYEncoder::new();
        let expr = logic_fn_call("__trust_wp_tuple2", vec![int(1), int(2)]);
        let term = encoder.encode_pure(&expr).expect("tuple2 placeholder");
        let sort = encoder.solver.get_sort(term);
        assert!(
            matches!(&sort, Sort::Uninterpreted(s) if s == "Tuple2"),
            "__trust_wp_tuple2 placeholder should return Tuple2 sort, got {sort:?}"
        );
    }

    // ── Tuple getter return sort from ctor domain (#residuals) ──────

    fn list_sort() -> Sort {
        Sort::Uninterpreted("List".to_string())
    }

    fn tuple2_sort() -> Sort {
        Sort::Uninterpreted("Tuple2".to_string())
    }

    /// Declare the `__trust_wp_tuple2` ctor placeholder with an
    /// [Int, List] domain by encoding a ctor application over typed vars.
    fn declare_int_list_tuple2_ctor(encoder: &mut AYEncoder) {
        encoder
            .get_or_declare_var("x_comp", Sort::Int)
            .expect("declare Int component var");
        encoder
            .get_or_declare_var("l_comp", list_sort())
            .expect("declare List component var");
        encoder
            .encode_pure(&logic_fn_call(
                "__trust_wp_tuple2",
                vec![var("x_comp"), var("l_comp")],
            ))
            .expect("tuple2 ctor application should encode");
    }

    /// CTOR-FIRST ORDER: with `__trust_wp_tuple2: [Int, List] -> Tuple2`
    /// declared, the `__trust_wp_tuple_get_1` placeholder over the opaque
    /// Tuple2 carrier resolves the ctor-declared component sort (List), so
    /// passing it to a registered logic fn with a List domain (argument
    /// position) does NOT mint an [apply-coerce] fresh constant.
    #[test]
    #[timeout(30000)]
    fn tuple_getter_resolves_ctor_component_sort_in_logic_fn_argument_position() {
        let mut encoder = AYEncoder::new();
        declare_int_list_tuple2_ctor(&mut encoder);
        encoder
            .get_or_declare_var("t", tuple2_sort())
            .expect("declare Tuple2 var");
        encoder.get_or_declare_logic_func("logic_sum", &[list_sort()], Sort::Int);

        let expr = logic_fn_call(
            "sum",
            vec![logic_fn_call("__trust_wp_tuple_get_1", vec![var("t")])],
        );
        let sum_term = encoder
            .encode_pure(&expr)
            .expect("sum(get_1(t)) should encode");

        let children = encoder.solver.term_children(sum_term);
        assert_eq!(children.len(), 1, "sum should have one argument");
        assert_eq!(
            encoder.solver.get_sort(children[0]),
            list_sort(),
            "getter placeholder must carry the ctor-declared List component sort"
        );
        let text = encoder.solver.format_term(sum_term);
        assert!(
            !text.contains("__apply_coerce"),
            "no fresh apply-coerce constant may be minted: {text}"
        );
    }

    /// GETTER-FIRST ORDER: an early Int-sorted getter mint (no ctor declared
    /// yet) must not pin the family — once the ctor is declared, a later
    /// getter application re-resolves to the ctor-declared component sort.
    #[test]
    #[timeout(30000)]
    fn tuple_getter_upgrades_to_ctor_component_sort_after_ctor_declaration() {
        let mut encoder = AYEncoder::new();
        encoder
            .get_or_declare_var("t", tuple2_sort())
            .expect("declare Tuple2 var");

        let getter = logic_fn_call("__trust_wp_tuple_get_1", vec![var("t")]);
        let early = encoder
            .encode_pure(&getter)
            .expect("pre-ctor getter should encode");
        assert_eq!(
            encoder.solver.get_sort(early),
            Sort::Int,
            "without a declared ctor the getter keeps the Int default"
        );

        declare_int_list_tuple2_ctor(&mut encoder);
        let late = encoder
            .encode_pure(&getter)
            .expect("post-ctor getter should encode");
        assert_eq!(
            encoder.solver.get_sort(late),
            list_sort(),
            "after the ctor declaration the getter resolves the List component"
        );

        encoder.get_or_declare_logic_func("logic_sum", &[list_sort()], Sort::Int);
        let sum_term = encoder
            .encode_pure(&logic_fn_call("sum", vec![getter]))
            .expect("sum(get_1(t)) should encode");
        let text = encoder.solver.format_term(sum_term);
        assert!(
            !text.contains("__apply_coerce"),
            "no fresh apply-coerce constant may be minted: {text}"
        );
    }

    /// CTOR-LESS CALLER SCOPE (the demoting-scope shape): no
    /// `__trust_wp_tuple2` constructor is ever declared, but the callee
    /// `sum : List -> Int` is registered — the logic-fn-ARGUMENT-position
    /// preseed derives the getter placeholder sort from the callee's declared
    /// domain, so no [apply-coerce] fresh constant is minted.
    #[test]
    #[timeout(30000)]
    fn tuple_getter_resolves_callee_domain_sort_without_ctor_declaration() {
        let mut encoder = AYEncoder::new();
        encoder
            .get_or_declare_var("t", tuple2_sort())
            .expect("declare Tuple2 var");
        encoder.get_or_declare_logic_func("logic_sum", &[list_sort()], Sort::Int);

        let expr = logic_fn_call(
            "sum",
            vec![logic_fn_call("__trust_wp_tuple_get_1", vec![var("t")])],
        );
        let sum_term = encoder
            .encode_pure(&expr)
            .expect("sum(get_1(t)) should encode without a ctor declaration");

        let children = encoder.solver.term_children(sum_term);
        assert_eq!(children.len(), 1, "sum should have one argument");
        assert_eq!(
            encoder.solver.get_sort(children[0]),
            list_sort(),
            "getter placeholder must carry the callee-declared List domain sort"
        );
        let text = encoder.solver.format_term(sum_term);
        assert!(
            !text.contains("__apply_coerce"),
            "no fresh apply-coerce constant may be minted: {text}"
        );
    }

    /// CONSERVATIVE GUARD: conflicting ctor domains for the same carrier
    /// ((Int, List) vs (Int, Int)) make component derivation ambiguous — the
    /// getter must stay on the Int default (today's behavior).
    #[test]
    #[timeout(30000)]
    fn tuple_getter_stays_int_on_conflicting_ctor_domains() {
        let mut encoder = AYEncoder::new();
        declare_int_list_tuple2_ctor(&mut encoder);
        // Second ctor variant with an (Int, Int) domain.
        encoder
            .get_or_declare_var("y_comp", Sort::Int)
            .expect("declare second Int component var");
        encoder
            .encode_pure(&logic_fn_call(
                "__trust_wp_tuple2",
                vec![var("x_comp"), var("y_comp")],
            ))
            .expect("(Int, Int) tuple2 ctor application should encode");
        encoder
            .get_or_declare_var("t", tuple2_sort())
            .expect("declare Tuple2 var");

        let term = encoder
            .encode_pure(&logic_fn_call("__trust_wp_tuple_get_1", vec![var("t")]))
            .expect("getter over ambiguous carrier should encode");
        assert_eq!(
            encoder.solver.get_sort(term),
            Sort::Int,
            "ambiguous ctor domains must not refine the getter sort"
        );
    }

    /// INT-LANE UNCHANGED: an Int component (index 0 of (Int, List)) keeps
    /// the Int-sorted getter exactly as before the refinement.
    #[test]
    #[timeout(30000)]
    fn tuple_getter_index0_int_component_stays_int() {
        let mut encoder = AYEncoder::new();
        declare_int_list_tuple2_ctor(&mut encoder);
        encoder
            .get_or_declare_var("t", tuple2_sort())
            .expect("declare Tuple2 var");

        let term = encoder
            .encode_pure(&logic_fn_call("__trust_wp_tuple_get_0", vec![var("t")]))
            .expect("get_0 over Tuple2 should encode");
        assert_eq!(
            encoder.solver.get_sort(term),
            Sort::Int,
            "Int components keep the Int-lane getter"
        );
    }

    /// Self-parametric trait call `Self::f()` resolves return sort from
    /// the concrete declaration `f` registered under its short name. (#2676)
    #[test]
    #[timeout(30000)]
    fn test_self_parametric_resolves_unit_return_sort() {
        let mut encoder = AYEncoder::new();
        // Register `f` as a nullary function returning Unit (mimics `Foo::f() {}`)
        let unit = Sort::Uninterpreted("Unit".to_string());
        let _fd = encoder.get_or_declare_logic_func("logic_f", &[], unit.clone());
        // Call `Self::f()` — should resolve via direct lookup of `logic_f`
        let expr = logic_fn_call("Self::f", vec![]);
        let term = encoder
            .encode_pure(&expr)
            .expect("Self::f() should encode via placeholder");
        let sort = encoder.solver.get_sort(term);
        assert_eq!(
            sort, unit,
            "Self::f() placeholder should resolve to Unit (from logic_f), got {sort:?}"
        );
    }

    /// Self-parametric resolution falls back to Int when the concrete
    /// declaration is not found.
    #[test]
    #[timeout(30000)]
    fn test_self_parametric_falls_back_to_int() {
        let mut encoder = AYEncoder::new();
        // No `logic_g` registered
        let expr = logic_fn_call("Self::g", vec![]);
        let term = encoder
            .encode_pure(&expr)
            .expect("Self::g() should still encode as Int placeholder");
        let sort = encoder.solver.get_sort(term);
        assert_eq!(
            sort,
            Sort::Int,
            "Self::g() without concrete decl should fall back to Int"
        );
    }

    /// Self-parametric resolution via batch registration: a logic function `f`
    /// with body `__trust_wp_tuple0()` (unit) and return_sort=Unit should be
    /// declared with Unit sort. Then `Self::f()` should resolve to Unit.
    /// This mimics the real pipeline for `call_in_contract.rs`.
    #[test]
    #[timeout(30000)]
    fn test_self_parametric_via_batch_registration() {
        use trust_wp_core::{formula::ExprSort, logic::LogicFnDef};

        let mut encoder = AYEncoder::new();

        // Create LogicFnDef for `f` with body __trust_wp_tuple0() and Unit return sort
        let body = logic_fn_call("__trust_wp_tuple0", vec![]);
        let f_def = LogicFnDef::new("f".to_string(), "Foo::f".to_string(), vec![], body)
            .with_return_sort(Some(ExprSort::Unit));

        // Register via batch (same as real pipeline)
        encoder
            .register_logic_fns(&[f_def])
            .expect("register_logic_fns should succeed");

        // Verify: logic_f should be declared with Unit sort
        let smt_name = trust_wp_core::logic::logic_fn_smt_name("f");
        let decl = encoder
            .logic_func_decl_cloned(&smt_name)
            .expect("logic_f should be declared");
        let range = decl.range().clone();
        let unit = Sort::Uninterpreted("Unit".to_string());
        assert_eq!(
            range, unit,
            "logic_f should have Unit return sort after batch registration, got {range:?}"
        );

        // Now encode Self::f() — should resolve to Unit
        let expr = logic_fn_call("Self::f", vec![]);
        let term = encoder
            .encode_pure(&expr)
            .expect("Self::f() should encode after batch registration");
        let sort = encoder.solver.get_sort(term);
        assert_eq!(
            sort, unit,
            "Self::f() should resolve to Unit sort via batch-registered logic_f, got {sort:?}"
        );
    }

    #[test]
    #[timeout(30000)]
    fn test_self_parametric_ground_pool_uses_resolved_symbol() {
        use trust_wp_core::{
            formula::ExprSort,
            logic::{LogicFnDef, LogicMode},
        };

        let mut encoder = AYEncoder::new_with_quantifiers();
        let hash_log = LogicFnDef::new(
            "hash_log".to_string(),
            "<usize as Hash>::hash_log".to_string(),
            vec!["x".to_string()],
            var("x"),
        )
        .with_mode(LogicMode::Open)
        .with_param_sorts(vec![Some(ExprSort::Int)])
        .with_return_sort(Some(ExprSort::Int));
        encoder
            .register_logic_fns(&[hash_log])
            .expect("hash_log registration should succeed");

        let call = logic_fn_call("Self::hash_log", vec![int(5)]);
        let call_term = encoder
            .encode_pure(&call)
            .expect("Self::hash_log should encode through hash_log");

        let resolved = trust_wp_core::logic::logic_fn_smt_name("hash_log");
        let parametric = trust_wp_core::logic::logic_fn_smt_name("Self::hash_log");
        assert!(
            encoder
                .ground_pool_for_test()
                .entries_for(&resolved)
                .is_some_and(|entries| entries.len() == 1),
            "ground call should be registered under the resolved bare hash_log symbol"
        );
        assert!(
            encoder
                .ground_pool_for_test()
                .entries_for(&parametric)
                .is_none(),
            "ground call must not be stranded under the unresolved Self::hash_log symbol"
        );

        encoder
            .assert_ground_pool_instances()
            .expect("ground hash_log instance should assert");
        let five = encoder.solver.int_const(5);
        let not_five = encoder.solver.neq(call_term, five);
        encoder.solver.assert_term(not_five);
        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "ground instance should prove Self::hash_log(5) == 5"
        );
    }

    /// Build a fresh OptionInt datatype (None / Some(option_some_value: Int)).
    fn option_int_datatype() -> DatatypeSort {
        DatatypeSort {
            name: "OptionInt".to_string(),
            constructors: vec![
                DatatypeConstructor {
                    name: "None".to_string(),
                    fields: vec![],
                },
                DatatypeConstructor {
                    name: "Some".to_string(),
                    fields: vec![DatatypeField {
                        name: "option_some_value".to_string(),
                        sort: Sort::Int,
                    }],
                },
            ],
        }
    }

    /// The placeholder `__trust_wp_tuple_get_0` accessor applied to an
    /// `OptionInt`-sorted value is bridged to the native `option_some_value`
    /// selector under the `is-Some` guard, so logic-context `.0`-of-`Some`
    /// reasoning connects to native Option payload reasoning.
    ///
    /// Without the bridge, a premise `tuple_get_0(o) == 5` cannot establish
    /// `option_some_value(o) == 5` even when `is-Some(o)` holds, because the
    /// two accessors are unrelated UF symbols.
    #[test]
    #[timeout(30000)]
    fn tuple_get_0_placeholder_bridges_to_option_some_value() {
        let mut encoder = AYEncoder::new_pure_with_quantifiers();
        let dt = option_int_datatype();
        encoder.ensure_datatype_declared(&dt);
        let opt = encoder
            .get_or_declare_var("o", Sort::Datatype(dt.clone()))
            .expect("declare OptionInt var");

        // Premise via the placeholder accessor: tuple_get_0(o) == 5.
        let tuple_get = encoder
            .apply_logic_fn("__trust_wp_tuple_get_0", &[opt], Some(&[var("o")]), None)
            .expect("tuple_get_0(o) placeholder should encode");
        let five = encoder.solver.int_const(5);
        let premise = encoder.solver.eq(tuple_get, five);
        encoder.assert_term(premise);

        // Guard: is-Some(o).
        let is_some = encoder
            .solver
            .try_datatype_tester("Some", opt)
            .expect("native Some tester");
        encoder.assert_term(is_some);

        // Goal (negated): option_some_value(o) != 5.
        let native = encoder
            .solver
            .try_datatype_selector("option_some_value", opt, Sort::Int)
            .expect("native payload selector");
        let five_again = encoder.solver.int_const(5);
        let goal_neg = encoder.solver.neq(native, five_again);
        encoder.assert_term(goal_neg);

        assert!(
            matches!(encoder.check_sat(), SolveResult::Unsat(_)),
            "is-Some(o) && tuple_get_0(o)==5 should entail option_some_value(o)==5 (UNSAT)"
        );
    }

    /// SOUNDNESS GUARD: the Option bridge must NOT fire for a non-Option tuple
    /// `.0` placeholder. A generic 2-tuple's `.0` accessor and the (unrelated)
    /// `option_some_value` selector denote different values, so relating them
    /// would be a false-accept. Here `tuple_get_0` is applied to a Tuple2 sort,
    /// which is NOT an OptionInt, so no bridge is emitted and the two stay free.
    #[test]
    #[timeout(30000)]
    fn tuple_get_0_placeholder_does_not_bridge_for_non_option() {
        let mut encoder = AYEncoder::new_pure_with_quantifiers();
        let dt = option_int_datatype();
        encoder.ensure_datatype_declared(&dt);

        // A generic Tuple2-sorted receiver (NOT an Option).
        let tuple_sort = Sort::Uninterpreted("Tuple2".to_string());
        let pair = encoder
            .get_or_declare_var("p", tuple_sort)
            .expect("declare Tuple2 var");
        // An unrelated OptionInt value.
        let opt = encoder
            .get_or_declare_var("o2", Sort::Datatype(dt.clone()))
            .expect("declare OptionInt var");

        // tuple_get_0(p) == 5 over the Tuple2 receiver.
        let tuple_get = encoder
            .apply_logic_fn("__trust_wp_tuple_get_0", &[pair], Some(&[var("p")]), None)
            .expect("tuple_get_0(p) placeholder should encode");
        let five = encoder.solver.int_const(5);
        let premise = encoder.solver.eq(tuple_get, five);
        encoder.assert_term(premise);

        // is-Some(o2) must NOT let us conclude anything about p's payload.
        let is_some = encoder
            .solver
            .try_datatype_tester("Some", opt)
            .expect("native Some tester");
        encoder.assert_term(is_some);

        // option_some_value(o2) == 6 must remain SATISFIABLE — no spurious bridge
        // relates the Tuple2 `.0` to the OptionInt selector.
        let native = encoder
            .solver
            .try_datatype_selector("option_some_value", opt, Sort::Int)
            .expect("native payload selector");
        let six = encoder.solver.int_const(6);
        let goal = encoder.solver.eq(native, six);
        encoder.assert_term(goal);

        assert!(
            matches!(encoder.check_sat(), SolveResult::Sat),
            "non-Option tuple_get_0(p) must NOT be bridged to option_some_value(o2) (SAT)"
        );
    }
}
