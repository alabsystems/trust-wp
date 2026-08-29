// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Registered enum payload projection axioms.
//!
//! Handles total payload projection UFs for single-carrier enums, including
//! both quantified constructor equations and ground reconstruction implications.

use ay_dpll::api::{DatatypeSort, FuncDecl, Sort, Term, TermKind};
use trust_wp_core::logic::AdtKind;

use super::{datatype_constructor_matches, short_constructor_name, AYEncoder};

/// Decoded shape of a logic-placeholder constructor equality of the form
/// `receiver = OuterPh_<InnerTag>(InnerCtor(inner_args...))`, where
/// `OuterPh_<InnerTag>` is a `logic_..._P__P_<Outer>__placeholder_<tag>__ret_<tag>`
/// UF (NOT a native datatype constructor) and `InnerCtor(inner_args...)` is a
/// native constructor application. Drives the two sound bridge facts emitted by
/// `assert_placeholder_constructor_equality_consequence`. (#transpose)
struct PlaceholderGuard {
    /// Sort of `receiver` (a registered enum datatype).
    receiver_sort: Sort,
    /// The exact receiver term observed in the guard equality (e.g. `self`).
    receiver_term: Term,
    /// The outer datatype that the placeholder reconstructs (range of the UF,
    /// equal to the receiver's datatype).
    outer_datatype: DatatypeSort,
    /// Short constructor name decoded from the placeholder symbol (e.g. "Ok").
    outer_short_ctor: String,
    /// Datatype that owns the native inner constructor.
    inner_ctor_datatype: DatatypeSort,
    /// Native constructor name of the placeholder's argument (e.g. "Some").
    inner_ctor_name: String,
    /// Variant index of `inner_ctor_name` within `inner_ctor_datatype`.
    inner_ctor_variant_index: usize,
    /// Arguments of the native inner constructor application.
    inner_args: Vec<Term>,
}

impl AYEncoder {
    fn registered_enum_datatype_for_sort(&self, receiver_sort: &Sort) -> Option<DatatypeSort> {
        match receiver_sort {
            Sort::Datatype(datatype) => Some(datatype.clone()),
            Sort::Uninterpreted(name) => {
                let bare = name.rsplit("::").next().unwrap_or(name);
                self.get_datatype_decl(name)
                    .or_else(|| self.get_datatype_decl(bare))
                    .cloned()
            }
            _ => None,
        }
    }

    pub(crate) fn assert_registered_enum_payload_ground_consequences_from_assertions(&mut self) {
        if self.quantifier_state.quantifier_depth() != 0 {
            return;
        }

        let assertions = self.solver.assertions();
        let mut constructor_equalities = Vec::new();
        let mut tester_facts = Vec::new();
        let mut placeholder_guards = Vec::new();

        for assertion in &assertions {
            if let Some((lhs, rhs)) = self.asserted_enum_payload_equality(*assertion) {
                if let Some(consequence) = self.enum_receiver_constructor_equality(lhs, rhs) {
                    constructor_equalities.push(consequence);
                }
                if let Some(consequence) = self.enum_receiver_constructor_equality(rhs, lhs) {
                    constructor_equalities.push(consequence);
                }

                // Logic-placeholder constructor equalities (#transpose): the guard
                // `self = OkPh_<InnerTag>(InnerCtor(args))` is not a native
                // constructor equality (the LHS head is a placeholder UF, not a
                // datatype constructor), so the recognizer above skips it. Decode
                // it separately to emit the two sound bridge facts that connect the
                // guard's inner-ctor tag and body placeholder to native semantics.
                if let Some(guard) = self.placeholder_constructor_equality(lhs, rhs) {
                    placeholder_guards.push(guard);
                }
                if let Some(guard) = self.placeholder_constructor_equality(rhs, lhs) {
                    placeholder_guards.push(guard);
                }
            }

            if let Some(fact) = self.asserted_enum_tester_fact(*assertion) {
                tester_facts.push(fact);
            }
        }

        for (receiver_sort, receiver_term, constructor_name, args) in constructor_equalities {
            self.assert_registered_enum_payload_constructor_equality_consequence(
                &receiver_sort,
                receiver_term,
                &constructor_name,
                &args,
            );
        }

        for (receiver_sort, receiver_term, constructor_name) in tester_facts {
            self.assert_registered_enum_payload_tester_consequence(
                &receiver_sort,
                receiver_term,
                &constructor_name,
            );
        }

        for guard in placeholder_guards {
            self.assert_placeholder_constructor_equality_consequence(&assertions, guard);
        }
    }

    /// Emit placeholder-constructor bridge facts from the POSITIVE conjuncts of
    /// a freshly-encoded obligation term (e.g. a skolemized negated
    /// postcondition `(and guard... (not goal))`).
    ///
    /// The stack-scanning pass `assert_registered_enum_payload_ground_consequences_from_assertions`
    /// misses these guards because the skolemized postcondition is solved on a
    /// path whose check_sat does not re-run that pass, and the guard may be a
    /// conjunct inside one `(and ...)` assertion. Here we have the encoded term
    /// directly: walk its top-level conjunction (only descending through `and`,
    /// so we stay in positive/asserted-true polarity — never into `not`/`or`/
    /// `=>`), recognize `receiver = OuterPh(InnerCtor(args))` guards, and emit
    /// the same sound bridge facts. The body-placeholder scan uses the whole
    /// term (the goal sub-term carries `OkPh_body(receiver)`). (#transpose)
    pub(crate) fn emit_placeholder_bridge_facts_from_term(&mut self, term: Term) {
        if self.quantifier_state.quantifier_depth() != 0 {
            return;
        }
        // Collect positive-polarity equality conjuncts (descend only through `and`).
        let mut guards = Vec::new();
        let mut stack = vec![term];
        let mut seen = std::collections::HashSet::new();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            let TermKind::App { name, num_args } = self.solver.term_kind(t) else {
                continue;
            };
            match name.as_str() {
                "and" => {
                    // Positive context: every conjunct is asserted true.
                    stack.extend(self.solver.term_children(t));
                }
                "=" if num_args == 2 => {
                    let children = self.solver.term_children(t);
                    if let [lhs, rhs] = children.as_slice() {
                        if let Some(guard) = self.placeholder_constructor_equality(*lhs, *rhs) {
                            guards.push(guard);
                        }
                        if let Some(guard) = self.placeholder_constructor_equality(*rhs, *lhs) {
                            guards.push(guard);
                        }
                    }
                }
                // Any other connective (`not`, `or`, `=>`, `ite`, ...) breaks the
                // unconditional-truth chain; do not descend (would be unsound to
                // treat a guard under a negation/disjunction as asserted true).
                _ => {}
            }
        }
        // Scan the whole term for sibling body placeholders.
        let term_assertions = [term];
        for guard in guards {
            self.assert_placeholder_constructor_equality_consequence(&term_assertions, guard);
        }
    }

    fn asserted_enum_payload_equality(&self, assertion: Term) -> Option<(Term, Term)> {
        let TermKind::App { name, num_args: 2 } = self.solver.term_kind(assertion) else {
            return None;
        };
        if name != "=" {
            return None;
        }
        let children = self.solver.term_children(assertion);
        let [lhs, rhs] = children.as_slice() else {
            return None;
        };
        Some((*lhs, *rhs))
    }

    fn enum_receiver_constructor_equality(
        &self,
        receiver_term: Term,
        constructor_term: Term,
    ) -> Option<(Sort, Term, String, Vec<Term>)> {
        let receiver_sort = self.solver.get_sort(receiver_term);
        let datatype = self.registered_enum_datatype_for_sort(&receiver_sort)?;
        if self.solver.get_sort(constructor_term).as_term_sort() != receiver_sort.as_term_sort() {
            return None;
        }
        let decl = self.adt_decl_for_name(&datatype.name)?;
        if decl.kind != AdtKind::Enum {
            return None;
        }
        let TermKind::App {
            name: constructor_name,
            num_args,
        } = self.solver.term_kind(constructor_term)
        else {
            return None;
        };
        let constructor = datatype
            .constructors
            .iter()
            .find(|constructor| constructor.name == constructor_name)?;
        if constructor.fields.len() != num_args {
            return None;
        }
        let args = self.solver.term_children(constructor_term);
        if args.len() != constructor.fields.len() {
            return None;
        }
        Some((receiver_sort, receiver_term, constructor_name, args))
    }

    /// Decode the short outer constructor name from a logic-placeholder symbol.
    ///
    /// Placeholder symbols have the shape
    /// `logic_<Type>_P__P_<Ctor>__placeholder_<paramTag>__ret_<retTag>`. The
    /// outer constructor segment sits between `_P__P_` and `__placeholder_`. The
    /// segment may itself be path-qualified (`Mod::Ctor`), in which case the
    /// short name is taken. Returns `None` for non-placeholder symbols.
    fn placeholder_outer_short_ctor(name: &str) -> Option<String> {
        if !(name.starts_with("logic_")
            && name.contains("__placeholder_")
            && name.contains("__ret_"))
        {
            return None;
        }
        let after_marker = name.split("_P__P_").nth(1)?;
        let segment = after_marker.split("__placeholder_").next()?;
        if segment.is_empty() {
            return None;
        }
        Some(short_constructor_name(segment).to_string())
    }

    /// Recognize a logic-placeholder constructor equality
    /// `receiver = OuterPh_<InnerTag>(InnerCtor(inner_args...))`.
    ///
    /// Unlike `enum_receiver_constructor_equality` (which requires the RHS head to
    /// be a NATIVE datatype constructor of the receiver's datatype), this matches
    /// the guard shape produced when a quantified `self == Ok(Some(t))`
    /// skolemizes: the head is a placeholder UF and its single argument is a
    /// native inner constructor. Returns the decoded guard so the caller can emit
    /// the inner-discriminant and body-bridge facts. (#transpose)
    fn placeholder_constructor_equality(
        &self,
        receiver_term: Term,
        ph_term: Term,
    ) -> Option<PlaceholderGuard> {
        // Gate 1: ph_term is a single-argument placeholder application.
        let TermKind::App {
            name: ph_name,
            num_args: 1,
        } = self.solver.term_kind(ph_term)
        else {
            return None;
        };
        let outer_short_ctor = Self::placeholder_outer_short_ctor(&ph_name)?;

        // Gate 2: the receiver is a registered enum with >= 2 constructors and the
        // decoded outer short ctor names a real constructor of that enum.
        let receiver_sort = self.solver.get_sort(receiver_term);
        let outer_datatype = self.registered_enum_datatype_for_sort(&receiver_sort)?;
        let outer_decl = self.adt_decl_for_name(&outer_datatype.name)?;
        if outer_decl.kind != AdtKind::Enum {
            return None;
        }
        if outer_datatype.constructors.len() < 2 {
            return None;
        }
        if !outer_datatype.constructors.iter().any(|ctor| {
            datatype_constructor_matches(&outer_datatype, &ctor.name, &outer_short_ctor)
        }) {
            return None;
        }

        // Gate 3: the placeholder's single argument is a NATIVE constructor of
        // some registered datatype with >= 2 constructors. Resolve that datatype
        // and the variant index of the inner constructor.
        let inner = *self.solver.term_children(ph_term).first()?;
        let TermKind::App {
            name: inner_name,
            num_args: inner_num_args,
        } = self.solver.term_kind(inner)
        else {
            return None;
        };
        let inner_ctor_datatype = self
            .datatypes_for_constructor(&inner_name)
            .find(|dt| {
                dt.constructors.len() >= 2 && dt.constructors.iter().any(|c| c.name == inner_name)
            })
            .cloned()?;
        let inner_ctor_variant_index = inner_ctor_datatype
            .constructors
            .iter()
            .position(|c| c.name == inner_name)?;
        let inner_args = self.solver.term_children(inner);
        if inner_args.len() != inner_num_args {
            return None;
        }

        Some(PlaceholderGuard {
            receiver_sort,
            receiver_term,
            outer_datatype,
            outer_short_ctor,
            inner_ctor_datatype,
            inner_ctor_name: inner_name,
            inner_ctor_variant_index,
            inner_args,
        })
    }

    /// Emit the two sound bridge facts for a recognized placeholder guard.
    ///
    /// FACT1 (inner-discriminant tag): pins the flattened inner payload's
    /// discriminant to the exact tag of the guard's inner constructor, forcing the
    /// match's inner discriminant switch onto the correct arm.
    ///
    /// FACT2 (body-placeholder/native bridge): when the inner constructor is unary
    /// and a sibling body placeholder `B(receiver)` for the SAME outer constructor
    /// is applied to the SYNTACTICALLY IDENTICAL receiver, rewrites
    /// `B(receiver)` into the native `Outer(inner_args[0])`. Strictly gated to
    /// avoid false accepts. (#transpose)
    fn assert_placeholder_constructor_equality_consequence(
        &mut self,
        assertions: &[Term],
        guard: PlaceholderGuard,
    ) {
        // ---- FACT1: inner-discriminant tag (always emitted; the safer fact). ----
        if let Some(projection_decl) =
            self.registered_enum_payload_projection(&guard.receiver_sort, 0)
        {
            if let Ok(projection_term) = self.safe_apply(
                "datatype enum payload placeholder inner discriminant",
                &projection_decl,
                &[guard.receiver_term],
            ) {
                let disc_decl = self.get_or_declare_method_func(
                    "method_discriminant_1_i",
                    &[Sort::Int],
                    Sort::Int,
                );
                if let Ok(disc_term) = self.safe_apply(
                    "datatype enum payload placeholder inner discriminant apply",
                    &disc_decl,
                    &[projection_term],
                ) {
                    let tag_value = Self::datatype_discriminant_value(
                        self.adt_decl_for_name(&guard.inner_ctor_datatype.name),
                        &guard.inner_ctor_name,
                        guard.inner_ctor_variant_index,
                    );
                    let tag = self.solver.int_const_bigint(&tag_value);
                    let dedup_key = format!(
                        "datatype_enum_payload/placeholder_inner_discriminant::{:?}::{}",
                        guard.receiver_term, guard.inner_ctor_name
                    );
                    if self.mark_logic_fn_axiom_asserted(dedup_key) {
                        let eq = self.eq_term(disc_term, tag);
                        self.assert_solver_term(
                            "datatype_enum_payload/placeholder_inner_discriminant",
                            eq,
                        );
                    }
                }
            }
        }

        // ---- FACT2: body-placeholder/native bridge (dangerous; strictly gated). ----
        //
        // ONLY for a unary inner constructor: the native bridge target is
        // `Outer(inner_args[0])`, which is only well-typed/meaningful when the
        // inner ctor carries exactly one payload taken from THIS guard.
        if guard.inner_args.len() != 1 {
            return;
        }
        let payload = guard.inner_args[0];

        // Find sibling body placeholders B applied to the SAME receiver term.
        let mut body_placeholders: Vec<Term> = Vec::new();
        for assertion in assertions {
            for sub in self.collect_body_placeholder_terms(*assertion, &guard) {
                if !body_placeholders.contains(&sub) {
                    body_placeholders.push(sub);
                }
            }
        }

        for body_term in body_placeholders {
            let Some(native_ctor) = self.axiom_datatype_constructor(
                "datatype enum payload placeholder body native bridge",
                &guard.outer_datatype,
                &guard.outer_short_ctor,
                &[payload],
            ) else {
                continue;
            };
            let dedup_key = format!(
                "datatype_enum_payload/placeholder_body_native_bridge::{:?}::{:?}::{}",
                guard.receiver_term, body_term, guard.outer_short_ctor
            );
            if self.mark_logic_fn_axiom_asserted(dedup_key) {
                let eq = self.eq_term(body_term, native_ctor);
                self.assert_solver_term("datatype_enum_payload/placeholder_body_native_bridge", eq);
            }
        }
    }

    /// Collect sibling body-placeholder terms `B(receiver)` inside `assertion`
    /// that pair with the given guard. A body placeholder is a single-argument
    /// placeholder UF application whose:
    ///   * decoded outer short ctor equals the guard's outer short ctor,
    ///   * range datatype equals the guard's outer datatype, and
    ///   * single argument is the SYNTACTICALLY IDENTICAL receiver term.
    ///
    /// The body placeholder's domain ([outer DT]) differs from the guard
    /// placeholder's domain ([inner ctor DT]); this is what makes B the body
    /// (post-match) reconstruction rather than the guard itself. (#transpose)
    fn collect_body_placeholder_terms(
        &self,
        assertion: Term,
        guard: &PlaceholderGuard,
    ) -> Vec<Term> {
        let mut found = Vec::new();
        let mut stack = vec![assertion];
        let mut seen = std::collections::HashSet::new();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            if let TermKind::App {
                name: bname,
                num_args: 1,
            } = self.solver.term_kind(term)
            {
                if let Some(b_short) = Self::placeholder_outer_short_ctor(&bname) {
                    if b_short == guard.outer_short_ctor {
                        // Range must be the outer datatype (the placeholder
                        // reconstructs an `outer_datatype` value).
                        let b_range = self.solver.get_sort(term);
                        let outer_term_sort =
                            Sort::Datatype(guard.outer_datatype.clone()).as_term_sort();
                        if b_range.as_term_sort() == outer_term_sort {
                            let b_child = *self.solver.term_children(term).first().unwrap();
                            // SYNTACTIC identity with the guard's receiver term.
                            if b_child == guard.receiver_term {
                                found.push(term);
                            }
                        }
                    }
                }
            }
            stack.extend(self.solver.term_children(term));
        }
        found
    }

    fn asserted_enum_tester_fact(&self, assertion: Term) -> Option<(Sort, Term, String)> {
        let TermKind::App { name, num_args: 1 } = self.solver.term_kind(assertion) else {
            return None;
        };
        let constructor_name = name.strip_prefix("is-")?.to_string();
        let children = self.solver.term_children(assertion);
        let [receiver_term] = children.as_slice() else {
            return None;
        };
        let receiver_sort = self.solver.get_sort(*receiver_term);
        let datatype = self.registered_enum_datatype_for_sort(&receiver_sort)?;
        let decl = self.adt_decl_for_name(&datatype.name)?;
        if decl.kind != AdtKind::Enum {
            return None;
        }
        if !datatype
            .constructors
            .iter()
            .any(|constructor| constructor.name == constructor_name)
        {
            return None;
        }
        Some((receiver_sort, *receiver_term, constructor_name))
    }

    fn assert_registered_enum_payload_constructor_equality_consequence(
        &mut self,
        receiver_sort: &Sort,
        receiver_term: Term,
        constructor_name: &str,
        args: &[Term],
    ) {
        let Some(datatype) = self.registered_enum_datatype_for_sort(receiver_sort) else {
            return;
        };
        let Some(constructor) = datatype
            .constructors
            .iter()
            .find(|constructor| constructor.name == constructor_name)
            .cloned()
        else {
            return;
        };

        for (field_index, arg) in args.iter().copied().enumerate() {
            if constructor.fields.get(field_index).is_none() {
                continue;
            }
            let Some(projection_decl) =
                self.registered_enum_payload_projection(receiver_sort, field_index)
            else {
                continue;
            };
            let Ok(projection_term) = self.safe_apply(
                "datatype enum payload asserted constructor equality",
                &projection_decl,
                &[receiver_term],
            ) else {
                continue;
            };
            let dedup_key = format!(
                "datatype_enum_payload/asserted_constructor_eq::{receiver_term:?}::{constructor_name}::{field_index}::{arg:?}"
            );
            if self.mark_logic_fn_axiom_asserted(dedup_key) {
                let eq = self.eq_term(projection_term, arg);
                self.assert_solver_term("datatype_enum_payload/asserted_constructor_eq", eq);
            }
        }

        if constructor.fields.len() == 1 {
            let Some(projection_decl) = self.registered_enum_payload_projection(receiver_sort, 0)
            else {
                return;
            };
            let Ok(projection_term) = self.safe_apply(
                "datatype enum payload asserted constructor reconstruct",
                &projection_decl,
                &[receiver_term],
            ) else {
                return;
            };
            let Some(reconstructed) = self.axiom_datatype_constructor(
                "datatype enum payload asserted constructor reconstruct",
                &datatype,
                constructor_name,
                &[projection_term],
            ) else {
                return;
            };
            let dedup_key = format!(
                "datatype_enum_payload/asserted_constructor_reconstruct::{receiver_term:?}::{constructor_name}"
            );
            if self.mark_logic_fn_axiom_asserted(dedup_key) {
                let eq = self.eq_term(reconstructed, receiver_term);
                self.assert_solver_term(
                    "datatype_enum_payload/asserted_constructor_reconstruct",
                    eq,
                );
            }
        }
    }

    fn assert_registered_enum_payload_tester_consequence(
        &mut self,
        receiver_sort: &Sort,
        receiver_term: Term,
        constructor_name: &str,
    ) {
        let Some(datatype) = self.registered_enum_datatype_for_sort(receiver_sort) else {
            return;
        };
        let Some(constructor) = datatype
            .constructors
            .iter()
            .find(|constructor| constructor.name == constructor_name)
            .cloned()
        else {
            return;
        };
        if constructor.fields.len() != 1 {
            return;
        }

        let Some(projection_decl) = self.registered_enum_payload_projection(receiver_sort, 0)
        else {
            return;
        };
        let Ok(projection_term) = self.safe_apply(
            "datatype enum payload asserted tester reconstruct",
            &projection_decl,
            &[receiver_term],
        ) else {
            return;
        };
        let Some(reconstructed) = self.axiom_datatype_constructor(
            "datatype enum payload asserted tester reconstruct",
            &datatype,
            constructor_name,
            &[projection_term],
        ) else {
            return;
        };
        let dedup_key = format!(
            "datatype_enum_payload/asserted_tester_reconstruct::{receiver_term:?}::{constructor_name}"
        );
        if self.mark_logic_fn_axiom_asserted(dedup_key) {
            let eq = self.eq_term(reconstructed, receiver_term);
            self.assert_solver_term("datatype_enum_payload/asserted_tester_reconstruct", eq);
        }
    }

    /// Resolve a total payload projection for registered enums.
    ///
    /// MIR loses the active downcast variant when a projected enum payload is
    /// lowered to `__trust_wp_tuple_get_N(self)`. For single-carrier enums like
    /// `OwnResult<T, E>`, keep that payload read connected to constructor
    /// semantics by declaring a sort-specific total projection UF and asserting
    /// constructor equations:
    ///
    /// `forall args. enum_payload_get_N(Ctor(args)) = args[N]`
    ///
    /// This is only safe when every constructor that has field `N` encodes that
    /// field to the same SMT sort. Constructors without field `N` are left
    /// unconstrained, matching the total-UF fallback semantics on unmatched
    /// variants. (#1296)
    pub(crate) fn registered_enum_payload_projection(
        &mut self,
        receiver_sort: &Sort,
        field_index: usize,
    ) -> Option<FuncDecl> {
        let Some(datatype) = self.registered_enum_datatype_for_sort(receiver_sort) else {
            return None;
        };

        let constructors = {
            let Some(decl) = self.adt_decl_for_name(&datatype.name) else {
                return None;
            };
            if decl.kind != AdtKind::Enum {
                return None;
            }

            decl.constructors
                .iter()
                .filter_map(|ctor| {
                    let field_sort = ctor.fields.get(field_index)?.sort.clone();
                    Some((
                        ctor.smt_name.clone(),
                        ctor.fields
                            .iter()
                            .map(|field| field.sort.clone())
                            .collect::<Vec<_>>(),
                        field_sort,
                    ))
                })
                .collect::<Vec<_>>()
        };

        if constructors.is_empty() {
            return None;
        }

        let mut payload_sort: Option<Sort> = None;
        for (_, _, field_sort) in &constructors {
            let encoded_sort = self.sort_from_expr_sort(field_sort.clone());
            match payload_sort.as_ref() {
                Some(existing) if *existing != encoded_sort => return None,
                Some(_) => {}
                None => payload_sort = Some(encoded_sort),
            }
        }
        let payload_sort = payload_sort?;

        let smt_name = format!(
            "enum_payload_get_{field_index}_1_{}",
            Self::method_sort_tag(receiver_sort)
        );
        let projection_decl = self.get_or_declare_method_func(
            &smt_name,
            std::slice::from_ref(receiver_sort),
            payload_sort,
        );

        let dedup_key = format!(
            "datatype_enum_payload_axioms::{}::{field_index}",
            datatype.name
        );
        if !self.mark_logic_fn_axiom_asserted(dedup_key) {
            return Some(projection_decl);
        }

        for (ctor_name, field_sorts, _) in &constructors {
            let field_terms = field_sorts
                .iter()
                .enumerate()
                .map(|(idx, field_sort)| {
                    let encoded_sort = self.sort_from_expr_sort(field_sort.clone());
                    self.solver.fresh_var(
                        &format!("__enum_payload_{}_{}_field_{idx}", datatype.name, ctor_name),
                        encoded_sort,
                    )
                })
                .collect::<Vec<_>>();
            // Guard against declared/synthesized ADT alias skew. Recursive list-like
            // enums in the compat harness can register constructors whose internal
            // return sort no longer matches `datatype.name`, and bare
            // `datatype_constructor` panics in that case. Skipping the axiom is
            // sound: we only lose a proof step and return `Unknown` instead.
            let Some(ctor_term) = self.axiom_datatype_constructor(
                "datatype enum payload",
                &datatype,
                ctor_name,
                &field_terms,
            ) else {
                continue;
            };
            let projection_term = self.solver.apply(&projection_decl, &[ctor_term]);
            let eq = self.eq_term(projection_term, field_terms[field_index]);
            let axiom = self
                .solver
                .forall_with_triggers(&field_terms, eq, &[&[ctor_term]]);
            self.assert_solver_term("datatype_enum_payload/variant", axiom);
        }

        // When constructor-equality quantifiers collapse to tester facts
        // (`exists<t> x == Ok(t)` -> `is_ok(x)`), the forward payload axiom
        // alone is not enough to reassemble driver-lowered payload reads like
        // `self.0`. For single-field registered enums, add the converse bridge:
        // `is_Ctor(x) ==> Ctor(enum_payload_get_N(x)) = x`. (#1296)
        if constructors
            .iter()
            .all(|(_, field_sorts, _)| field_sorts.len() == 1)
        {
            for (ctor_name, _, _) in &constructors {
                let x = self.solver.fresh_var(
                    &format!("__enum_payload_reconstruct_{}_{}", datatype.name, ctor_name),
                    Sort::Datatype(datatype.clone()),
                );
                let Ok(is_ctor) = self.solver.try_datatype_tester(ctor_name, x) else {
                    continue;
                };
                let payload = self.solver.apply(&projection_decl, &[x]);
                let Some(reconstructed) = self.axiom_datatype_constructor(
                    "datatype enum payload reconstruct",
                    &datatype,
                    ctor_name,
                    &[payload],
                ) else {
                    continue;
                };
                let eq = self.eq_term(reconstructed, x);
                let implication = self.solver.implies(is_ctor, eq);
                let axiom = self
                    .solver
                    .forall_with_triggers(&[x], implication, &[&[is_ctor]]);
                self.assert_solver_term("datatype_enum_payload/reconstruct", axiom);
            }
        }

        // Native selector bridge (#1296): connect enum_payload_get_N to the
        // native datatype selector under the constructor tester guard.
        //
        // When constructor-equality elimination substitutes a quantified variable
        // with the native datatype selector (e.g., `Ok.0(self)`), the match body
        // uses `enum_payload_get_N(self)` for the same field. Without this axiom,
        // ay must derive their equality through a multi-step chain:
        //   1. Ok(Ok.0(self)) = self  (native reconstruction)
        //   2. Ok(enum_payload_get_N(self)) = self  (payload reconstruction)
        //   3. Ok is injective → Ok.0(self) = enum_payload_get_N(self)
        //
        // This bridge short-circuits the chain:
        //   `forall x. is_Ctor(x) ==> enum_payload_get_N(x) = native_selector(x)`
        //
        // Unlike the reconstruction axiom (which needs ALL field projections to
        // rebuild the constructor), this bridge is per-field and works for
        // multi-field constructors too — e.g., Tree::Node(val, left, right)
        // gets separate bridges for each of field_index 0, 1, 2.
        for (ctor_name, _field_sorts, _) in &constructors {
            let Some(ctor_def) = datatype.constructors.iter().find(|c| c.name == *ctor_name) else {
                continue;
            };
            let Some(field_def) = ctor_def.fields.get(field_index) else {
                continue;
            };
            let x = self.solver.fresh_var(
                &format!(
                    "__enum_payload_selector_bridge_{}_{ctor_name}",
                    datatype.name
                ),
                Sort::Datatype(datatype.clone()),
            );
            let Ok(is_ctor) = self.solver.try_datatype_tester(ctor_name, x) else {
                continue;
            };
            let Ok(native_sel) =
                self.solver
                    .try_datatype_selector(&field_def.name, x, field_def.sort.clone())
            else {
                continue;
            };
            let payload_proj = self.solver.apply(&projection_decl, &[x]);
            let eq = self.eq_term(payload_proj, native_sel);
            let implication = self.solver.implies(is_ctor, eq);
            let axiom = self
                .solver
                .forall_with_triggers(&[x], implication, &[&[is_ctor]]);
            self.assert_solver_term("datatype_enum_payload/selector_bridge", axiom);
        }

        Some(projection_decl)
    }

    /// Assert a ground reconstruction implication for a registered enum payload projection.
    ///
    /// This complements the quantified constructor equations above with the
    /// exact receiver term observed in a driver-shaped body:
    ///
    /// `is_Ok(self) ==> OwnResult::Ok(enum_payload_get_0(self)) = self`
    ///
    /// ay-dpll still leaves the quantified inverse stuck at
    /// `Unknown(Incomplete)` for the `result/own.rs::{unwrap,unwrap_err}` shape,
    /// while the equivalent ground implication closes immediately. (#1296)
    pub(crate) fn assert_ground_registered_enum_payload_reconstruction(
        &mut self,
        receiver_sort: &Sort,
        receiver_term: Term,
        field_index: usize,
        projection_term: Term,
    ) {
        if self.quantifier_state.quantifier_depth() != 0 {
            return;
        }

        let Some(datatype) = self.registered_enum_datatype_for_sort(receiver_sort) else {
            return;
        };
        let Some(decl) = self.adt_decl_for_name(&datatype.name) else {
            return;
        };
        if decl.kind != AdtKind::Enum {
            return;
        }

        // Receiver-specific constructor equality bridge:
        //
        //   receiver == C(v0, ...) ==> projection == vi
        //
        // The global forward axiom states the same fact for
        // `projection(C(v0, ...))`, but ay-dpll can miss the extra UF
        // congruence step from `receiver == C(...)` to
        // `projection(receiver) == projection(C(...))`. This scoped bridge
        // keeps the observed payload read connected to ground constructor
        // equalities without trusting a shortcut.
        for constructor in &datatype.constructors {
            let Some(field_def) = constructor.fields.get(field_index) else {
                continue;
            };
            let field_terms = constructor
                .fields
                .iter()
                .enumerate()
                .map(|(idx, field)| {
                    self.solver.fresh_var(
                        &format!(
                            "__enum_payload_ground_eq_{}_{}_field_{idx}",
                            datatype.name, constructor.name
                        ),
                        field.sort.clone(),
                    )
                })
                .collect::<Vec<_>>();
            let Some(ctor_term) = self.axiom_datatype_constructor(
                "datatype enum payload ground constructor equality",
                &datatype,
                &constructor.name,
                &field_terms,
            ) else {
                continue;
            };
            let receiver_eq_ctor = self.eq_term(receiver_term, ctor_term);
            let payload_eq_field = self.eq_term(projection_term, field_terms[field_index]);
            let implication = self.solver.implies(receiver_eq_ctor, payload_eq_field);
            let axiom =
                self.solver
                    .forall_with_triggers(&field_terms, implication, &[&[ctor_term]]);
            self.assert_solver_term("datatype_enum_payload/ground_constructor_eq", axiom);

            // Also assert the selector-shaped bridge for the exact constructor
            // field. This helps the reconstruction path when the solver knows
            // only the tester but has not unfolded native selector semantics.
            let Ok(native_sel) = self.solver.try_datatype_selector(
                &field_def.name,
                receiver_term,
                field_def.sort.clone(),
            ) else {
                continue;
            };
            let eq = self.eq_term(projection_term, native_sel);
            let receiver_eq_ctor = self.eq_term(receiver_term, ctor_term);
            let implication = self.solver.implies(receiver_eq_ctor, eq);
            let axiom =
                self.solver
                    .forall_with_triggers(&field_terms, implication, &[&[ctor_term]]);
            self.assert_solver_term("datatype_enum_payload/ground_constructor_selector", axiom);
        }

        // Ground reconstruction: is_Ctor(recv) ==> Ctor(projection) = recv
        // Only valid for single-field constructors where projection IS the sole arg.
        for constructor in &datatype.constructors {
            if constructor.fields.len() != 1 || field_index != 0 {
                continue;
            }

            let Ok(tester) = self
                .solver
                .try_datatype_tester(&constructor.name, receiver_term)
            else {
                continue;
            };
            let Some(reconstructed) = self.axiom_datatype_constructor(
                "datatype enum payload ground reconstruct",
                &datatype,
                &constructor.name,
                &[projection_term],
            ) else {
                continue;
            };
            let eq = self.eq_term(reconstructed, receiver_term);
            let implication = self.solver.implies(tester, eq);
            self.assert_solver_term("datatype_enum_payload/ground_reconstruct", implication);
        }

        // Ground selector bridge: is_Ctor(recv) ==> projection = native_selector(recv)
        // Works for multi-field constructors too — connects the specific field's
        // enum_payload_get_N projection to the native datatype selector. (#1296)
        for constructor in &datatype.constructors {
            let Some(field_def) = constructor.fields.get(field_index) else {
                continue;
            };
            let Ok(tester) = self
                .solver
                .try_datatype_tester(&constructor.name, receiver_term)
            else {
                continue;
            };
            let Ok(native_sel) = self.solver.try_datatype_selector(
                &field_def.name,
                receiver_term,
                field_def.sort.clone(),
            ) else {
                continue;
            };
            let eq = self.eq_term(projection_term, native_sel);
            let implication = self.solver.implies(tester, eq);
            self.assert_solver_term("datatype_enum_payload/ground_selector_bridge", implication);
        }

        // Unconditional ITE-based payload definition (#1296):
        //
        // When ALL constructors that have field `field_index` share the same sort,
        // the payload projection has a complete, unconditional definition via
        // exhaustive case-split on the datatype testers:
        //
        //   projection = ite(is_C1(recv), C1.f(recv), ite(is_C2(recv), C2.f(recv), ...))
        //
        // Unlike the conditional bridges above (which require `is_Ctor(recv)` as a
        // known ground fact), this ITE definition is unconditionally asserted. The
        // solver can use it in any context — crucially when `self.0` appears in a
        // precondition without an explicit constructor guard.
        //
        // Example: `T::clone.postcondition(self.0, call_5)` where self: OwnResult<T,E>.
        // The conditional bridge `is_Ok(self) ==> projection = Ok.ok(self)` fires
        // only when `is_Ok(self)` is established. The ITE definition lets the solver
        // evaluate `self.0` immediately regardless of variant knowledge.
        self.assert_ground_ite_payload_definition(
            &datatype,
            receiver_term,
            field_index,
            projection_term,
        );
    }

    /// Assert an unconditional ITE-chain definition for a ground enum payload projection.
    ///
    /// For a datatype with constructors C1, C2, ..., Cn where each has field at
    /// `field_index` with the same sort, emits:
    ///
    /// `projection = ite(is_C1(recv), C1.f(recv), ite(is_C2(recv), C2.f(recv), ... Cn.f(recv)))`
    ///
    /// The last branch is unconditional (the else case of the final ITE), which is
    /// sound because datatype testers are exhaustive.
    fn assert_ground_ite_payload_definition(
        &mut self,
        datatype: &ay_dpll::api::DatatypeSort,
        receiver_term: Term,
        field_index: usize,
        projection_term: Term,
    ) {
        // Collect (tester, native_selector) pairs for all constructors that have
        // the field at field_index.
        let mut branches: Vec<(Term, Term)> = Vec::new();
        for constructor in &datatype.constructors {
            let Some(field_def) = constructor.fields.get(field_index) else {
                continue;
            };
            let Ok(tester) = self
                .solver
                .try_datatype_tester(&constructor.name, receiver_term)
            else {
                continue;
            };
            let Ok(native_sel) = self.solver.try_datatype_selector(
                &field_def.name,
                receiver_term,
                field_def.sort.clone(),
            ) else {
                continue;
            };
            branches.push((tester, native_sel));
        }

        // Need at least 2 branches for the ITE to add value beyond the
        // conditional bridges already asserted above.
        if branches.len() < 2 {
            return;
        }

        // Build the ITE chain right-to-left: the last branch's selector is the
        // else-case, then wrap each preceding branch as ite(tester, sel, acc).
        // Use safe_ite to harmonize branch sorts and prevent ay panics from
        // residual sort mismatches between constructors. (#2687)
        let mut ite_chain = branches.last().unwrap().1;
        for (tester, native_sel) in branches.iter().rev().skip(1) {
            ite_chain = self.safe_ite(*tester, *native_sel, ite_chain);
        }

        let eq = self.eq_term(projection_term, ite_chain);
        self.assert_solver_term("datatype_enum_payload/ground_ite_definition", eq);
    }
}
