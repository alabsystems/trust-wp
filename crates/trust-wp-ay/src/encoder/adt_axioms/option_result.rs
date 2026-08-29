// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Standard Option/Result axiom assertion and type disjointness.

use std::{
    collections::{HashMap, HashSet},
    sync::OnceLock,
};

use ay_dpll::api::{FuncDecl, Sort, Term, TermKind};

use super::super::{match_enc::datatype_constructor_matches, AYEncoder};

impl AYEncoder {
    /// Choke-point hook for [`Self::bridge_tuple_get_0_to_option_some_value`]:
    /// recognize an application of the positional `.0` accessor FAMILY by its
    /// SMT declaration name and emit the guarded Option payload bridge.
    ///
    /// The accessor reaches the solver under three declaration-name shapes:
    /// the raw Rust name (`__trust_wp_tuple_get_0`, the legacy Int->Int
    /// spec-func lane), the raw SMT name (`logic_..._tuple_get_0`), and the
    /// signature-keyed placeholder family
    /// (`logic_..._tuple_get_0__placeholder_<params>__ret_<sort>`).
    /// The bridge used to be emitted only on the `apply_logic_fn` path, so any
    /// OTHER application of a pre-declared placeholder decl — qualified
    /// logic-method dispatch, structural receiver hints, mut-borrow resolve
    /// propagation, match payload bindings — produced an application carrying
    /// NO bridge fact. A VC premise could then force `is-Some(x)` and pin
    /// `tuple_get_0_placeholder(x)` without the solver ever learning that the
    /// placeholder equals `option_some_value(x)` (the ghost_vec decisive-fact
    /// gap). Hooking [`AYEncoder::safe_apply`] — the single helper every one of
    /// those paths uses to build the application — closes the whole family at
    /// one choke point.
    ///
    /// SOUNDNESS: this is only a dispatcher; every emitted fact goes through
    /// `bridge_tuple_get_0_to_option_some_value`, whose guards (genuine Option
    /// datatype receiver, Int payload, `is-Some` antecedent, ground context
    /// only) make each assertion a true consequence of the datatype semantics.
    pub(crate) fn bridge_tuple_get_0_family_application(
        &mut self,
        decl_name: &str,
        arg_terms: &[Term],
        result: Term,
    ) {
        // Cheap early-out for the hot safe_apply path: the accessor is unary.
        if arg_terms.len() != 1 {
            return;
        }
        static NEEDLES: OnceLock<(String, String, String)> = OnceLock::new();
        let (rust_name, exact_smt, placeholder_prefix) = NEEDLES.get_or_init(|| {
            let rust_name =
                trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0);
            let exact_smt = trust_wp_core::logic::logic_fn_smt_name(&rust_name);
            let placeholder_prefix = format!("{exact_smt}__placeholder_");
            (rust_name, exact_smt, placeholder_prefix)
        });
        if decl_name != rust_name
            && decl_name != exact_smt
            && !decl_name.starts_with(placeholder_prefix.as_str())
        {
            return;
        }
        self.bridge_tuple_get_0_to_option_some_value(rust_name, arg_terms, result);
    }

    /// Bridge a generic tuple-`.0` placeholder accessor to the native Option
    /// `Some`-payload selector when (and only when) the placeholder is applied
    /// to an Option-datatype receiver.
    ///
    /// In logic contexts the `Some`-payload of an `Option` is reached by two
    /// unrelated encodings: a generic positional `__trust_wp_tuple_get_0`
    /// placeholder UF (created on the placeholder path for any `.0` access) and
    /// the datatype's real `option_some_value` field selector. A premise like
    /// `tuple_get_0(get(l, i)) == 0` therefore cannot be connected to a
    /// reconstruction that uses `option_some_value`, so the solver gets stuck
    /// (the L3 gap in the all_zero_list dissection).
    ///
    /// For an `Option` the two accessors denote the SAME value on the `Some`
    /// branch — `Some(x).0 == x == option_some_value(Some(x))` — so we emit the
    /// guarded ground equality
    ///   `is-Some(receiver) ==> tuple_get_0_placeholder(receiver) == option_some_value(receiver)`.
    ///
    /// CARDINAL SOUNDNESS: the bridge is gated to receivers whose sort is a
    /// genuine Option datatype (a `Some`-with-one-field / `None`-nullary enum).
    /// It is NEVER emitted for a non-Option tuple `.0` placeholder, where the
    /// generic accessor and `option_some_value` denote unrelated values; doing
    /// so would relate distinct terms and admit a false-accept. The guard
    /// `is-Some(receiver)` further makes the fact vacuously true on the `None`
    /// branch, and the equality is a genuine consequence of the datatype
    /// semantics, so it can never manufacture a spurious UNSAT.
    ///
    /// Only the positional `.0` accessor (`__trust_wp_tuple_get_0`) and only
    /// the first (index-0) field of `Some` participate — an `Option` payload is
    /// a single value, so higher indices have no native counterpart.
    pub(crate) fn bridge_tuple_get_0_to_option_some_value(
        &mut self,
        accessor_name: &str,
        arg_terms: &[Term],
        result: Term,
    ) {
        // Only assert ground bridges in the top-level (non-quantified) context.
        // Inside a quantifier body the `result`/`receiver` terms reference bound
        // variables, so a free-standing equality would constrain the Skolem
        // reading rather than the universal — emit nothing there.
        if self.quantifier_state.quantifier_depth() != 0 {
            return;
        }
        // Only the positional `.0` accessor participates.
        if accessor_name
            != trust_wp_core::formula::internal::tuple_lowering::tuple_field_logic_fn_name(0)
        {
            return;
        }
        let [receiver] = arg_terms else {
            return;
        };
        let receiver = *receiver;

        // The result of `.0` on an Option<Int> payload is Int; if the
        // placeholder return sort diverged (e.g., not Int), the native selector
        // can't be the same value, so skip.
        if self.solver.get_sort(result) != Sort::Int {
            return;
        }

        // Identify the receiver's Option datatype and its `Some`-payload
        // selector. Requires a `Some` constructor with exactly one Int field
        // and a `None` nullary constructor (a genuine Option shape).
        //
        // Term sorts surface declared datatypes as either `Sort::Datatype` or
        // `Sort::Uninterpreted(name)` (the `as_term_sort()` carrier form), so
        // resolve the registered datatype declaration by name in the latter
        // case before inspecting its constructors.
        let receiver_sort = self.solver.get_sort(receiver);
        let dt = match &receiver_sort {
            Sort::Datatype(dt) => dt.clone(),
            Sort::Uninterpreted(name) => {
                let Some(dt) = self.get_datatype_decl(name).cloned() else {
                    return;
                };
                dt
            }
            _ => return,
        };
        let dt = &dt;
        let has_none = dt.constructors.iter().any(|ctor| {
            datatype_constructor_matches(dt, &ctor.name, "None") && ctor.fields.is_empty()
        });
        if !has_none {
            return;
        }
        let Some(some_ctor) = dt
            .constructors
            .iter()
            .find(|ctor| datatype_constructor_matches(dt, &ctor.name, "Some"))
        else {
            return;
        };
        let [some_field] = some_ctor.fields.as_slice() else {
            return;
        };
        if some_field.sort != Sort::Int {
            return;
        }
        let selector_name = some_field.name.clone();

        // is-Some(receiver) guard.
        let Ok(is_some) = self.solver.try_datatype_tester("Some", receiver) else {
            return;
        };
        // option_some_value(receiver).
        let Ok(native) = self
            .solver
            .try_datatype_selector(&selector_name, receiver, Sort::Int)
        else {
            return;
        };

        let same_payload = self.eq_term(result, native);
        let guarded = self.solver.implies(is_some, same_payload);
        self.assert_solver_term("option_tuple_get_0_bridge", guarded);
    }

    fn constructor_family_decls(&self, rust_name: &str, arity: usize) -> Vec<FuncDecl> {
        let smt_name = trust_wp_core::logic::logic_fn_smt_name(rust_name);
        let placeholder_prefix = format!("{smt_name}__placeholder_");
        let mut decls = Vec::new();

        if let Some(raw_decl) = self.logic_func_decl_cloned(&smt_name) {
            if raw_decl.domain().len() == arity {
                decls.push(raw_decl);
            }
        }

        decls.extend(
            self.logic_funcs_iter()
                .filter(|(name, decl)| {
                    name.starts_with(&placeholder_prefix) && decl.domain().len() == arity
                })
                .map(|(_, decl)| decl.clone()),
        );

        decls
    }

    fn assert_some_none_constructor_disequality_axioms(&mut self) {
        let some_decls = self.constructor_family_decls("Some", 1);
        let none_decls = self.constructor_family_decls("None", 0);

        for some_decl in &some_decls {
            let Some(domain_sort) = some_decl.domain().first() else {
                continue;
            };
            for none_decl in &none_decls {
                if some_decl.range() != none_decl.range() {
                    continue;
                }

                let v = self
                    .solver
                    .fresh_var("opt_ax_some_none_v", domain_sort.clone());
                let some_v = self.solver.apply(some_decl, &[v]);
                let none = self.solver.apply(none_decl, &[]);
                let eq = self.eq_term(some_v, none);
                let distinct = self.solver.not(eq);
                let axiom = self
                    .solver
                    .forall_with_triggers(&[v], distinct, &[&[some_v]]);
                self.solver.assert_term(axiom);
            }

            if let Sort::Datatype(dt) = some_decl.range() {
                let has_none_ctor = dt.constructors.iter().any(|ctor| {
                    datatype_constructor_matches(dt, &ctor.name, "None") && ctor.fields.is_empty()
                });
                if has_none_ctor {
                    let v = self
                        .solver
                        .fresh_var("opt_ax_some_native_none_v", domain_sort.clone());
                    let some_v = self.solver.apply(some_decl, &[v]);
                    let Some(none) =
                        self.axiom_datatype_constructor("option_some_native_none", dt, "None", &[])
                    else {
                        continue;
                    };
                    let eq = self.eq_term(some_v, none);
                    let distinct = self.solver.not(eq);
                    let axiom = self
                        .solver
                        .forall_with_triggers(&[v], distinct, &[&[some_v]]);
                    self.solver.assert_term(axiom);
                }
            }
        }
    }

    fn collect_native_option_ground_bridge_terms(
        &self,
        term: Term,
        option_sort: &Sort,
        seen: &mut HashSet<Term>,
        candidates: &mut HashSet<Term>,
        some_tests: &mut HashMap<Term, Term>,
        none_tests: &mut HashMap<Term, Term>,
        native_selectors: &mut HashMap<Term, Term>,
        spec_unwraps: &mut HashMap<Term, Term>,
    ) {
        if !seen.insert(term) {
            return;
        }

        if self.solver.get_sort(term) == *option_sort {
            candidates.insert(term);
        }

        if let TermKind::App { name, num_args: 1 } = self.solver.term_kind(term) {
            let children = self.solver.term_children(term);
            if let [receiver] = children.as_slice() {
                if self.solver.get_sort(*receiver) == *option_sort {
                    match name.as_str() {
                        "is-Some" => {
                            candidates.insert(*receiver);
                            some_tests.insert(*receiver, term);
                        }
                        "is-None" => {
                            candidates.insert(*receiver);
                            none_tests.insert(*receiver, term);
                        }
                        "option_some_value" if self.solver.get_sort(term) == Sort::Int => {
                            candidates.insert(*receiver);
                            native_selectors.insert(*receiver, term);
                        }
                        _ if name.starts_with("spec_unwrap")
                            && self.solver.get_sort(term) == Sort::Int =>
                        {
                            candidates.insert(*receiver);
                            spec_unwraps.insert(*receiver, term);
                        }
                        _ => {}
                    }
                }
            }

            for child in children {
                self.collect_native_option_ground_bridge_terms(
                    child,
                    option_sort,
                    seen,
                    candidates,
                    some_tests,
                    none_tests,
                    native_selectors,
                    spec_unwraps,
                );
            }
            return;
        }

        for child in self.solver.term_children(term) {
            self.collect_native_option_ground_bridge_terms(
                child,
                option_sort,
                seen,
                candidates,
                some_tests,
                none_tests,
                native_selectors,
                spec_unwraps,
            );
        }
    }

    /// Assert finite bridges between native OptionInt selectors/testers and the
    /// sort-aware `spec_unwrap` UF used by recursive logic-function contracts.
    ///
    /// The datatype axiom plugin understands `option_some_value(t)` while the
    /// spec contract instances often mention `spec_unwrap__dom_OptionInt(t)`.
    /// Without an observed-term bridge, AY cannot connect those payload terms
    /// without falling back to broad quantified reconstruction axioms.
    pub(crate) fn assert_native_option_ground_bridges(&mut self) -> usize {
        const MAX_OPTION_BRIDGE_TERMS: usize = 128;

        let Some(option_dt) = self.get_datatype_decl("OptionInt").cloned() else {
            return 0;
        };
        let option_sort = Sort::Datatype(option_dt).as_term_sort();
        let assertions = self.solver.assertions();
        if assertions.is_empty() {
            return 0;
        }

        let mut seen = HashSet::new();
        let mut candidates = HashSet::new();
        let mut some_tests = HashMap::new();
        let mut none_tests = HashMap::new();
        let mut native_selectors = HashMap::new();
        let mut spec_unwraps = HashMap::new();

        for assertion in &assertions {
            self.collect_native_option_ground_bridge_terms(
                *assertion,
                &option_sort,
                &mut seen,
                &mut candidates,
                &mut some_tests,
                &mut none_tests,
                &mut native_selectors,
                &mut spec_unwraps,
            );
        }

        let mut count = 0;
        for candidate in candidates.into_iter().take(MAX_OPTION_BRIDGE_TERMS) {
            if self.solver.get_sort(candidate) != option_sort {
                continue;
            }

            let is_some = some_tests
                .get(&candidate)
                .copied()
                .or_else(|| self.solver.try_datatype_tester("Some", candidate).ok());
            let is_none = none_tests
                .get(&candidate)
                .copied()
                .or_else(|| self.solver.try_datatype_tester("None", candidate).ok());

            if let (Some(is_some), Some(is_none)) = (is_some, is_none) {
                let exhaustive = self.solver.or(is_some, is_none);
                if self.assert_solver_term("ground/native_option_exhaustive", exhaustive) {
                    count += 1;
                }
                let both = self.solver.and(is_some, is_none);
                let disjoint = self.solver.not(both);
                if self.assert_solver_term("ground/native_option_disjoint", disjoint) {
                    count += 1;
                }
            }

            let Some(native_selector) = native_selectors.get(&candidate).copied() else {
                continue;
            };
            let Some(spec_unwrap) = spec_unwraps.get(&candidate).copied() else {
                continue;
            };
            let Some(is_some) = some_tests
                .get(&candidate)
                .copied()
                .or_else(|| self.solver.try_datatype_tester("Some", candidate).ok())
            else {
                continue;
            };

            let same_payload = self.eq_term(spec_unwrap, native_selector);
            let guarded = self.solver.implies(is_some, same_payload);
            if self.assert_solver_term("ground/native_option_spec_unwrap", guarded) {
                count += 1;
            }

            count += self.assert_native_option_canonical_payload_clauses(
                &assertions,
                is_some,
                spec_unwrap,
                native_selector,
                MAX_OPTION_BRIDGE_TERMS.saturating_sub(count),
            );
        }

        count
    }

    fn term_is_not_of(&self, term: Term, target: Term) -> bool {
        if !matches!(self.solver.term_kind(term), TermKind::Not) {
            return false;
        }
        let children = self.solver.term_children(term);
        matches!(children.as_slice(), [inner] if *inner == target)
    }

    fn term_mentions(&self, term: Term, needle: Term, seen: &mut HashSet<Term>) -> bool {
        if term == needle {
            return true;
        }
        if !seen.insert(term) {
            return false;
        }
        self.solver
            .term_children(term)
            .into_iter()
            .any(|child| self.term_mentions(child, needle, seen))
    }

    fn replace_payload_term(
        &mut self,
        term: Term,
        spec_unwrap: Term,
        native_selector: Term,
    ) -> Option<Term> {
        if term == spec_unwrap {
            return Some(native_selector);
        }

        let TermKind::App { name, num_args } = self.solver.term_kind(term) else {
            return None;
        };
        if num_args != 2 {
            return None;
        }
        let children = self.solver.term_children(term);
        let [left, right] = children.as_slice() else {
            return None;
        };
        let new_left = self.replace_payload_term(*left, spec_unwrap, native_selector);
        let new_right = self.replace_payload_term(*right, spec_unwrap, native_selector);
        if new_left.is_none() && new_right.is_none() {
            return None;
        }
        let left = new_left.unwrap_or(*left);
        let right = new_right.unwrap_or(*right);
        match name.as_str() {
            "+" => Some(self.solver.add(left, right)),
            "-" => Some(self.solver.sub(left, right)),
            "*" => Some(self.solver.mul(left, right)),
            "select" => Some(self.solver.select(left, right)),
            _ => None,
        }
    }

    fn canonicalize_payload_bool_term(
        &mut self,
        term: Term,
        spec_unwrap: Term,
        native_selector: Term,
    ) -> Option<Term> {
        let TermKind::App { name, num_args } = self.solver.term_kind(term) else {
            return None;
        };
        if num_args != 2 {
            return None;
        }
        let children = self.solver.term_children(term);
        let [left, right] = children.as_slice() else {
            return None;
        };
        let new_left = self.replace_payload_term(*left, spec_unwrap, native_selector);
        let new_right = self.replace_payload_term(*right, spec_unwrap, native_selector);
        if new_left.is_none() && new_right.is_none() {
            return None;
        }
        let left = new_left.unwrap_or(*left);
        let right = new_right.unwrap_or(*right);
        match name.as_str() {
            "=" => Some(self.eq_term(left, right)),
            "<" => Some(self.solver.lt(left, right)),
            "<=" => Some(self.solver.le(left, right)),
            ">" => Some(self.solver.gt(left, right)),
            ">=" => Some(self.solver.ge(left, right)),
            _ => None,
        }
    }

    fn term_is_int_one(&self, term: Term) -> bool {
        self.solver.get_sort(term) == Sort::Int
            && matches!(self.solver.term_kind(term), TermKind::Const)
            && self.solver.format_term(term) == "1"
    }

    fn successor_base_term(&self, term: Term) -> Option<Term> {
        let TermKind::App { name, num_args: 2 } = self.solver.term_kind(term) else {
            return None;
        };
        if name != "+" {
            return None;
        }
        let children = self.solver.term_children(term);
        let [left, right] = children.as_slice() else {
            return None;
        };
        if self.term_is_int_one(*left) {
            Some(*right)
        } else if self.term_is_int_one(*right) {
            Some(*left)
        } else {
            None
        }
    }

    fn weakened_successor_payload_bound(
        &mut self,
        term: Term,
        spec_unwrap: Term,
        native_selector: Term,
    ) -> Option<Term> {
        let TermKind::App { name, num_args: 2 } = self.solver.term_kind(term) else {
            return None;
        };
        if name != "<=" {
            return None;
        }
        let children = self.solver.term_children(term);
        let [left, right] = children.as_slice() else {
            return None;
        };
        if *right != spec_unwrap {
            return None;
        }
        let base = self.successor_base_term(*left)?;
        Some(self.solver.le(base, native_selector))
    }

    fn canonicalize_payload_conjunction(
        &mut self,
        term: Term,
        spec_unwrap: Term,
        native_selector: Term,
    ) -> Option<Term> {
        let TermKind::App { name, .. } = self.solver.term_kind(term) else {
            return None;
        };
        if name != "and" {
            return None;
        }

        let mut changed = false;
        let mut children = Vec::new();
        for child in self.solver.term_children(term) {
            if let Some(canonical) =
                self.canonicalize_payload_bool_term(child, spec_unwrap, native_selector)
            {
                children.push(canonical);
                if let Some(weakened) =
                    self.weakened_successor_payload_bound(child, spec_unwrap, native_selector)
                {
                    children.push(weakened);
                }
                changed = true;
            } else {
                children.push(child);
            }
        }
        changed.then(|| self.solver.and_many(&children))
    }

    fn assert_native_option_canonical_payload_clauses(
        &mut self,
        assertions: &[Term],
        is_some: Term,
        spec_unwrap: Term,
        native_selector: Term,
        remaining_budget: usize,
    ) -> usize {
        if remaining_budget == 0 {
            return 0;
        }

        let mut count = 0;
        let mut seen = HashSet::new();
        for assertion in assertions {
            if count >= remaining_budget {
                break;
            }
            let children = match self.solver.term_kind(*assertion) {
                TermKind::App { name, .. } if name == "or" => self.solver.term_children(*assertion),
                _ => continue,
            };
            if !children
                .iter()
                .any(|child| self.term_is_not_of(*child, is_some))
            {
                continue;
            }
            let Some(payload_child) = children.iter().copied().find(|child| {
                matches!(self.solver.term_kind(*child), TermKind::App { ref name, .. } if name == "and")
                    && self.term_mentions(*child, spec_unwrap, &mut HashSet::new())
            }) else {
                continue;
            };
            let Some(canonical_payload_child) =
                self.canonicalize_payload_conjunction(payload_child, spec_unwrap, native_selector)
            else {
                continue;
            };

            let canonical_children: Vec<Term> = children
                .into_iter()
                .map(|child| {
                    if child == payload_child {
                        canonical_payload_child
                    } else {
                        child
                    }
                })
                .collect();
            let canonical_clause = self.solver.or_many(&canonical_children);
            if seen.insert(canonical_clause)
                && self.assert_solver_term(
                    "ground/native_option_payload_canonical_clause",
                    canonical_clause,
                )
            {
                count += 1;
            }
        }
        count
    }

    /// Assert axioms connecting Option/Result constructors, testers, and accessors.
    ///
    /// When both a constructor (e.g., `logic_Some`) and a tester (`is_some`) or
    /// accessor (`spec_unwrap`) are declared, this asserts defining axioms:
    ///
    /// **Option axioms**:
    /// ```text
    /// not(is_some(logic_None()))                      -- None values test as not-Some
    /// is_option(logic_None())                          -- None is an Option value
    /// forall v. is_some(logic_Some(v))                 -- Some values test as Some
    /// forall v. is_option(logic_Some(v))               -- Some values are Option values
    /// forall v. spec_unwrap(logic_Some(v)) = v         -- unwrap extracts inner value
    /// forall x. is_some(x) ==> logic_Some(spec_unwrap(x)) = x  -- Some reconstruction
    /// forall x. is_option(x) && !is_some(x) ==> x = None       -- None reconstruction (#1109)
    /// ```
    /// The `is_option` predicate restricts None reconstruction to Option-domain values,
    /// preventing cross-type collapse with Result disjointness axioms (#1109).
    ///
    /// **Result axioms** (when `logic_Ok`, `is_ok`, and `spec_unwrap`/`result_err_error`
    /// are declared):
    /// ```text
    /// forall v. is_ok(logic_Ok(v))                     -- Ok values test as Ok
    /// forall v. spec_unwrap(logic_Ok(v)) = v           -- unwrap extracts Ok value
    /// forall x. is_ok(x) ==> logic_Ok(spec_unwrap(x)) = x      -- Ok reconstruction
    /// forall v. not(is_ok(logic_Err(v)))               -- Err values test as not-Ok
    /// forall v. result_err_error(logic_Err(v)) = v     -- unwrap_err extracts Err value
    /// forall x. !is_ok(x) ==> logic_Err(result_err_error(x)) = x  -- Err reconstruction
    /// ```
    #[allow(clippy::too_many_lines)] // Cohesive axiom block; splitting would fragment related logic
    pub(crate) fn assert_option_result_axioms(&mut self) {
        // Option: logic_None / logic_Some + is_some + spec_unwrap
        let none_decl = Some(self.find_or_declare_standard_int_constructor_decl("None", 0));
        let some_decl = Some(self.find_or_declare_standard_int_constructor_decl("Some", 1));
        let is_some_decl = self.spec_func_decl_cloned("is_some");
        let unwrap_decl = self.spec_func_decl_cloned("spec_unwrap");

        // Declare type-discriminating predicate for Option values (#1109).
        // This allows a safe None reconstruction axiom that does not collapse
        // Result values to None via the disjointness chain.
        let is_option_decl = if none_decl.is_some() || some_decl.is_some() {
            let decl = self
                .solver
                .declare_fun("__trust_wp_is_option", &[Sort::Int], Sort::Bool);
            self.register_spec_func("__trust_wp_is_option".to_string(), decl.clone());
            Some(decl)
        } else {
            None
        };

        // Constructor disequality must hold even when no tester/accessor path
        // is present in the query. This is the minimal semantic fact needed for
        // branches like `Some(OwnResult::Err(_)) != None`, where nested payloads
        // keep `Some` on the placeholder path. (#1296)
        self.assert_some_none_constructor_disequality_axioms();

        // Bridge the Int-flattened Option discriminant to the `is_some` tester
        // (#transpose, Ok-None arm). When a nested Option payload is flattened
        // to Int, the match body reads its variant through
        // `method_discriminant_1_i(v)` while a guard such as `self == Ok(None)`
        // constrains only `is_some(v)` — nothing connects the two, so the body
        // discriminant stays free and a non-matching arm can be spuriously
        // selected (the `aux` free-variable SAT model). An Option's
        // discriminant IS 1 for `Some` and 0 for `None`, so for genuine Option
        // values this is a tautology:
        //   forall v. is_option(v) ==> method_discriminant_1_i(v) = ite(is_some(v),1,0)
        // Guarded by `__trust_wp_is_option(v)` so it can NEVER constrain a
        // non-Option Int-flattened enum (whose discriminants may exceed {0,1});
        // triggered on `method_discriminant_1_i(v)` so it is fully inert on
        // queries that have no nested-Option discriminant. SOUND — it only adds
        // a true consequence for genuine Options, so it can never manufacture a
        // spurious UNSAT (zero false-accept risk).
        if let (Some(is_some_for_bridge), Some(is_option_for_bridge)) =
            (is_some_decl.as_ref(), is_option_decl.as_ref())
        {
            let v = self.solver.fresh_var("opt_ax_disc_bridge_v", Sort::Int);
            let disc_decl =
                self.get_or_declare_method_func("method_discriminant_1_i", &[Sort::Int], Sort::Int);
            let disc_v = self.solver.apply(&disc_decl, &[v]);
            let is_some_v = self.solver.apply(is_some_for_bridge, &[v]);
            let is_option_v = self.solver.apply(is_option_for_bridge, &[v]);
            let one = self.solver.int_const(1);
            let zero = self.solver.int_const(0);
            let some_tag = self.solver.ite(is_some_v, one, zero);
            let eq = self.eq_term(disc_v, some_tag);
            let implies = self.solver.implies(is_option_v, eq);
            let axiom = self
                .solver
                .forall_with_triggers(&[v], implies, &[&[disc_v]]);
            self.solver.assert_term(axiom);
        }

        if let (Some(none_decl), Some(is_some_decl)) = (none_decl.as_ref(), is_some_decl.as_ref()) {
            let none = self.solver.apply(none_decl, &[]);

            // not(is_some(logic_None()))
            let is_some_of_none = self.solver.apply(is_some_decl, &[none]);
            let axiom = self.solver.not(is_some_of_none);
            self.solver.assert_term(axiom);

            // is_option(logic_None()) — None is an Option value
            if let Some(is_option_decl) = is_option_decl.as_ref() {
                let is_option_none = self.solver.apply(is_option_decl, &[none]);
                self.solver.assert_term(is_option_none);
            }

            // None reconstruction: forall x. is_option(x) && !is_some(x) ==> x = None
            // Safe because is_option(x) restricts the axiom to Option-domain values.
            // Result values (Ok(v), Err(v)) don't have is_option(x) = true, so the
            // disjointness axiom !is_some(Ok(v)) does NOT derive Ok(v) = None. (#1109)
            if let Some(is_option_decl) = is_option_decl.as_ref() {
                let x = self.solver.fresh_var("opt_ax_none_recon", Sort::Int);
                let is_option_x = self.solver.apply(is_option_decl, &[x]);
                let is_some_x = self.solver.apply(is_some_decl, &[x]);
                let not_some_x = self.solver.not(is_some_x);
                let guard = self.solver.and(is_option_x, not_some_x);
                let eq_none = self.eq_term(x, none);
                let implies = self.solver.implies(guard, eq_none);
                let axiom = self
                    .solver
                    .forall_with_triggers(&[x], implies, &[&[is_option_x]]);
                self.solver.assert_term(axiom);
            }
        }

        if let Some(some_decl) = some_decl.as_ref() {
            if is_some_decl.is_some() || unwrap_decl.is_some() || is_option_decl.is_some() {
                let v = self.solver.fresh_var("opt_ax_v", Sort::Int);

                // logic_Some(v)
                let some_v = self.solver.apply(some_decl, &[v]);

                if let Some(is_some_decl) = is_some_decl.as_ref() {
                    // forall v. is_some(logic_Some(v))
                    let is_some_of_some = self.solver.apply(is_some_decl, &[some_v]);
                    let axiom =
                        self.solver
                            .forall_with_triggers(&[v], is_some_of_some, &[&[some_v]]);
                    self.solver.assert_term(axiom);
                }

                // forall v. is_option(logic_Some(v)) — Some values are Option values (#1109)
                if let Some(is_option_decl) = is_option_decl.as_ref() {
                    let is_option_some = self.solver.apply(is_option_decl, &[some_v]);
                    let axiom =
                        self.solver
                            .forall_with_triggers(&[v], is_option_some, &[&[some_v]]);
                    self.solver.assert_term(axiom);
                }

                if let Some(unwrap_decl) = unwrap_decl.as_ref() {
                    // forall v. spec_unwrap(logic_Some(v)) = v
                    let unwrap_of_some = self.solver.apply(unwrap_decl, &[some_v]);
                    let eq = self.eq_term(unwrap_of_some, v);
                    let axiom = self.solver.forall_with_triggers(&[v], eq, &[&[some_v]]);
                    self.solver.assert_term(axiom);

                    // Some reconstruction (`is_some(x) ==> logic_Some(spec_unwrap(x)) = x`)
                    // is NOT emitted as a quantified axiom here: triggered on
                    // `spec_unwrap(x)`, it forms an E-matching ping-pong with the
                    // `spec_unwrap(logic_Some(v)) = v` selector axiom above and builds
                    // unbounded `logic_Some(spec_unwrap(logic_Some(spec_unwrap(...))))`
                    // towers (the quantified reconstruction is the ONLY axiom that
                    // creates a fresh constructor term from a selector term, so it is the
                    // sole engine of the loop). or_pat / all_zero_list degraded to Unknown
                    // at ~200s through that loop. It is re-emitted instead as GROUND
                    // instances over the `spec_unwrap` applications actually present in
                    // the query — see `assert_option_result_ground_reconstruction`, called
                    // at the end of this method. Ground instances carry no trigger, so no
                    // tower can form, while the reconstruction power is retained for the
                    // problem-level opaque options that genuinely need it. (loop-free)
                }
            }
        }

        // Result: logic_Ok / logic_Err + is_ok + spec_unwrap / result_err_error
        let ok_decl = Some(self.find_or_declare_standard_int_constructor_decl("Ok", 1));
        let err_decl = Some(self.find_or_declare_standard_int_constructor_decl("Err", 1));
        let is_ok_decl = self.spec_func_decl_cloned("is_ok");
        let err_acc_decl = self.spec_func_decl_cloned("result_err_error");

        if let Some(ok_decl) = ok_decl.as_ref() {
            if is_ok_decl.is_some() || unwrap_decl.is_some() {
                let v = self.solver.fresh_var("res_ax_v", Sort::Int);
                let ok_v = self.solver.apply(ok_decl, &[v]);

                if let Some(is_ok_decl) = is_ok_decl.as_ref() {
                    // forall v. is_ok(logic_Ok(v))
                    let is_ok_of_ok = self.solver.apply(is_ok_decl, &[ok_v]);
                    let axiom = self
                        .solver
                        .forall_with_triggers(&[v], is_ok_of_ok, &[&[ok_v]]);
                    self.solver.assert_term(axiom);
                }

                if let Some(unwrap_decl) = unwrap_decl.as_ref() {
                    // forall v. spec_unwrap(logic_Ok(v)) = v
                    let unwrap_of_ok = self.solver.apply(unwrap_decl, &[ok_v]);
                    let eq = self.eq_term(unwrap_of_ok, v);
                    let axiom = self.solver.forall_with_triggers(&[v], eq, &[&[ok_v]]);
                    self.solver.assert_term(axiom);

                    // Ok reconstruction (`is_ok(x) ==> logic_Ok(spec_unwrap(x)) = x`) is
                    // emitted as GROUND instances, not a quantified axiom — same
                    // selector/constructor E-matching loop as the Some case above. See
                    // `assert_option_result_ground_reconstruction`. (loop-free)
                }
            }
        }

        if let Some(err_decl) = err_decl.as_ref() {
            if is_ok_decl.is_some() || err_acc_decl.is_some() {
                let v = self.solver.fresh_var("res_ax_ev", Sort::Int);
                let err_v = self.solver.apply(err_decl, &[v]);

                if let Some(is_ok_decl) = is_ok_decl.as_ref() {
                    // forall v. not(is_ok(logic_Err(v)))
                    let is_ok_of_err = self.solver.apply(is_ok_decl, &[err_v]);
                    let not_ok = self.solver.not(is_ok_of_err);
                    let axiom = self.solver.forall_with_triggers(&[v], not_ok, &[&[err_v]]);
                    self.solver.assert_term(axiom);
                }

                if let Some(err_acc_decl) = err_acc_decl.as_ref() {
                    // forall v. result_err_error(logic_Err(v)) = v
                    let err_acc_of_err = self.solver.apply(err_acc_decl, &[err_v]);
                    let eq = self.eq_term(err_acc_of_err, v);
                    let axiom = self.solver.forall_with_triggers(&[v], eq, &[&[err_v]]);
                    self.solver.assert_term(axiom);

                    // Err reconstruction (`!is_ok(x) ==> logic_Err(result_err_error(x)) = x`)
                    // is emitted as GROUND instances, not a quantified axiom — same
                    // selector/constructor E-matching loop as the Some/Ok cases. See
                    // `assert_option_result_ground_reconstruction`. (loop-free)
                }
            }
        }

        // Type disjointness: Option and Result values are disjoint (#599).
        // Without these, the shared spec_unwrap UF allows the solver to conflate
        // Option and Result values.

        // Cross-type exclusion: Result constructors are not Option-Some
        // forall v. !is_some(logic_Ok(v))
        if let (Some(is_some_decl), Some(ok_decl)) = (is_some_decl.as_ref(), ok_decl.as_ref()) {
            let v = self.solver.fresh_var("disjoint_ok_v", Sort::Int);
            let ok_v = self.solver.apply(ok_decl, &[v]);
            let is_some_ok = self.solver.apply(is_some_decl, &[ok_v]);
            let not_is_some_ok = self.solver.not(is_some_ok);
            let axiom = self
                .solver
                .forall_with_triggers(&[v], not_is_some_ok, &[&[ok_v]]);
            self.solver.assert_term(axiom);
        }
        // forall v. !is_some(logic_Err(v))
        if let (Some(is_some_decl), Some(err_decl)) = (is_some_decl.as_ref(), err_decl.as_ref()) {
            let v = self.solver.fresh_var("disjoint_err_v", Sort::Int);
            let err_v = self.solver.apply(err_decl, &[v]);
            let is_some_err = self.solver.apply(is_some_decl, &[err_v]);
            let not_is_some_err = self.solver.not(is_some_err);
            let axiom = self
                .solver
                .forall_with_triggers(&[v], not_is_some_err, &[&[err_v]]);
            self.solver.assert_term(axiom);
        }

        // Cross-type exclusion: Option constructors are not Result-Ok
        // forall v. !is_ok(logic_Some(v))
        if let (Some(is_ok_decl), Some(some_decl)) = (is_ok_decl.as_ref(), some_decl.as_ref()) {
            let v = self.solver.fresh_var("disjoint_some_v", Sort::Int);
            let some_v = self.solver.apply(some_decl, &[v]);
            let is_ok_some = self.solver.apply(is_ok_decl, &[some_v]);
            let not_is_ok_some = self.solver.not(is_ok_some);
            let axiom = self
                .solver
                .forall_with_triggers(&[v], not_is_ok_some, &[&[some_v]]);
            self.solver.assert_term(axiom);
        }
        // !is_ok(logic_None())
        if let (Some(is_ok_decl), Some(none_decl)) = (is_ok_decl.as_ref(), none_decl.as_ref()) {
            let none = self.solver.apply(none_decl, &[]);
            let is_ok_none = self.solver.apply(is_ok_decl, &[none]);
            let not_is_ok_none = self.solver.not(is_ok_none);
            self.solver.assert_term(not_is_ok_none);
        }

        // Mutual exclusion when both testers exist:
        // forall x. !(is_some(x) && is_ok(x))
        // Multi-trigger [is_some(x), is_ok(x)] ensures the axiom only fires when
        // BOTH testers appear in the E-graph for the same term, avoiding cascade
        // instantiation from a single-trigger match. (#1110)
        if let (Some(is_some_decl), Some(is_ok_decl)) = (is_some_decl.as_ref(), is_ok_decl.as_ref())
        {
            let x = self.solver.fresh_var("disjoint_ax_x", Sort::Int);
            let is_some_x = self.solver.apply(is_some_decl, &[x]);
            let is_ok_x = self.solver.apply(is_ok_decl, &[x]);
            let both = self.solver.and(is_some_x, is_ok_x);
            let not_both = self.solver.not(both);
            let axiom = self
                .solver
                .forall_with_triggers(&[x], not_both, &[&[is_some_x, is_ok_x]]);
            self.solver.assert_term(axiom);
        }

        // Qualified constructors: scan logic_funcs for user-defined enum constructors
        // with qualified names (e.g., `logic_OwnResult_P__P_Ok` from `OwnResult::Ok`).
        // These receive no axioms from the standard path above because it only looks up
        // unqualified names like `logic_Ok`. Generate the same axiom families for each
        // qualified constructor, using the shared testers/accessors. (#1766)
        self.assert_qualified_constructor_axioms();

        // Loop-free reconstruction: the Some/Ok/Err reconstruction axioms removed
        // above are re-emitted here as GROUND instances over the selector
        // applications (`spec_unwrap(_)`, `result_err_error(_)`) actually present
        // in the query. Must run AFTER the goal/assumptions are asserted (so the
        // selector applications are visible) — `assert_standard_axioms` invokes
        // `assert_option_result_axioms` only once the obligation is on the stack.
        self.assert_option_result_ground_reconstruction();
    }

    /// Emit GROUND Option/Result reconstruction instances, replacing the
    /// quantified reconstruction axioms.
    ///
    /// The quantified reconstruction `is_some(x) ==> logic_Some(spec_unwrap(x)) = x`
    /// (and the Ok/Err analogues) is the ONLY axiom family that fabricates a fresh
    /// constructor application from a selector application. Paired with the
    /// selector-over-constructor axiom `spec_unwrap(logic_Some(v)) = v`, its
    /// `spec_unwrap(x)` trigger forms an E-matching ping-pong that builds unbounded
    /// `logic_Some(spec_unwrap(logic_Some(spec_unwrap(...))))` towers — the dominant
    /// cost that pushed or_pat / all_zero_list past the harness budget (degrading to
    /// Unknown after ~200s).
    ///
    /// Reconstruction is genuinely needed only for problem-level OPAQUE option/result
    /// terms (the `?`-operator and the reconstruction regression tests). Every such
    /// term already carries a `spec_unwrap(_)` / `result_err_error(_)` application in
    /// the asserted query, so a single GROUND instance per selector application
    /// preserves the proving power while carrying no trigger — no tower can form.
    ///
    /// SOUNDNESS: each emitted clause is exactly one instance of the (sound)
    /// quantified axiom, guarded by the same tester. It only ADDS a true consequence,
    /// so it can never admit a model the quantified form rejected (zero false-accept
    /// risk; identical accept/reject decisions on terms it covers).
    fn assert_option_result_ground_reconstruction(&mut self) {
        // Bound the number of selector applications considered, mirroring the native
        // bridge cap, so a pathological query cannot blow up emission.
        const MAX_RECON_TERMS: usize = 256;

        let some_decl = self.find_or_declare_standard_int_constructor_decl("Some", 1);
        let ok_decl = self.find_or_declare_standard_int_constructor_decl("Ok", 1);
        let err_decl = self.find_or_declare_standard_int_constructor_decl("Err", 1);
        let is_some_decl = self.spec_func_decl_cloned("is_some");
        let is_ok_decl = self.spec_func_decl_cloned("is_ok");
        let err_acc_decl = self.spec_func_decl_cloned("result_err_error");

        // Read-only pass: collect (receiver, selector_application) pairs for the
        // `spec_unwrap` and `result_err_error` selectors appearing anywhere in the
        // current assertions. Dedup terms via `seen` to keep the walk linear on the
        // shared DAG; dedup receivers at emission time.
        let mut seen: HashSet<Term> = HashSet::new();
        let mut unwrap_apps: Vec<(Term, Term)> = Vec::new();
        let mut err_acc_apps: Vec<(Term, Term)> = Vec::new();
        let mut stack: Vec<Term> = self.solver.assertions();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            match self.solver.term_kind(term) {
                // Do NOT descend into quantifier bodies: their selector applications
                // are over BOUND variables, not real terms, so a ground reconstruction
                // instance there would be meaningless (and ill-formed).
                TermKind::Forall | TermKind::Exists => continue,
                TermKind::App { name, num_args: 1 } => {
                    let children = self.solver.term_children(term);
                    if let [receiver] = children.as_slice() {
                        // The reconstruction clauses apply the Int-carrier
                        // constructors/testers (`logic_Some`, `is_some`, …) to the
                        // RECEIVER, so the receiver must itself be Int-sorted.
                        // A sort-specialised `spec_unwrap__dom_OptionInt` selector
                        // returns Int but takes an OptionInt receiver — applying an
                        // Int-domain tester there panics (`sort mismatch in apply`).
                        // This matches the removed quantified axiom, whose Int bound
                        // variable only ever E-matched Int-sorted selector receivers;
                        // native-datatype receivers are reconstructed by ay's datatype
                        // theory, not this Int lane.
                        if self.solver.get_sort(term) == Sort::Int
                            && self.solver.get_sort(*receiver) == Sort::Int
                        {
                            if name.starts_with("spec_unwrap") {
                                if unwrap_apps.len() < MAX_RECON_TERMS {
                                    unwrap_apps.push((*receiver, term));
                                }
                            } else if (name == "result_err_error"
                                || name.starts_with("result_err_error__dom_"))
                                && err_acc_apps.len() < MAX_RECON_TERMS
                            {
                                err_acc_apps.push((*receiver, term));
                            }
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

        // Some / Ok reconstruction over every distinct `spec_unwrap` receiver. The
        // tester guard (`is_some` / `is_ok`) keeps each clause inert unless the
        // receiver is genuinely of that family, so emitting both for a shared
        // `spec_unwrap` UF is sound and self-selecting.
        let mut recon_seen: HashSet<Term> = HashSet::new();
        for (receiver, unwrap_term) in unwrap_apps {
            if !recon_seen.insert(receiver) {
                continue;
            }
            if let Some(is_some_decl) = is_some_decl.as_ref() {
                let is_some_x = self.solver.apply(is_some_decl, &[receiver]);
                let some_unwrap = self.solver.apply(&some_decl, &[unwrap_term]);
                let eq = self.eq_term(some_unwrap, receiver);
                let guarded = self.solver.implies(is_some_x, eq);
                self.assert_solver_term("ground/option_some_reconstruction", guarded);
            }
            if let Some(is_ok_decl) = is_ok_decl.as_ref() {
                let is_ok_x = self.solver.apply(is_ok_decl, &[receiver]);
                let ok_unwrap = self.solver.apply(&ok_decl, &[unwrap_term]);
                let eq = self.eq_term(ok_unwrap, receiver);
                let guarded = self.solver.implies(is_ok_x, eq);
                self.assert_solver_term("ground/result_ok_reconstruction", guarded);
            }
        }

        // Err reconstruction over every distinct `result_err_error` receiver:
        // `!is_ok(x) ==> logic_Err(result_err_error(x)) = x`.
        if let (Some(is_ok_decl), Some(_)) = (is_ok_decl.as_ref(), err_acc_decl.as_ref()) {
            let mut err_seen: HashSet<Term> = HashSet::new();
            for (receiver, err_acc_term) in err_acc_apps {
                if !err_seen.insert(receiver) {
                    continue;
                }
                let is_ok_x = self.solver.apply(is_ok_decl, &[receiver]);
                let not_ok = self.solver.not(is_ok_x);
                let err_of = self.solver.apply(&err_decl, &[err_acc_term]);
                let eq = self.eq_term(err_of, receiver);
                let guarded = self.solver.implies(not_ok, eq);
                self.assert_solver_term("ground/result_err_reconstruction", guarded);
            }
        }
    }
}
