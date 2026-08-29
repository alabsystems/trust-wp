// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Seq sort coercion and equality decomposition.
//!
//! - `coerce_to_seq` — bridge UF from Vec-like sorts to Seq sort
//! - `coerce_seq_element_to_int` — bridge UF from non-Int element sorts to Int
//! - `try_decompose_seq_equality` — component-wise Array+Length+Offset equality

use ay_dpll::api::{FuncDecl, Sort, Term, TermKind};

use super::AYEncoder;
use crate::error::EncodingError;

/// Whether a bridge-UF `sort_name` denotes a Seq-backed iterator type, i.e. one
/// whose `View` is canonically represented by a `<var>_view` projector proxy.
///
/// Used to gate the View-term unification anchor in `coerce_to_seq` so only
/// iterator coercions (`SeqIter`, `Vec::IntoIter`) emit the proxy congruence;
/// plain collection coercions (Vec/List/user ADTs) are left untouched.
pub(in crate::encoder) fn is_seq_iterator_sort_leaf(sort_name: &str) -> bool {
    let leaf = sort_name.rsplit("::").next().unwrap_or(sort_name);
    leaf == "SeqIter" || leaf == "IntoIter"
}

/// Whether a ay sort is a Seq-backed iterator carrier (`SeqIter`,
/// `Vec::IntoIter`) — a single-field wrapper whose state IS its underlying
/// sequence (`trust-wp-std/src/logic/seq/iter.rs`: `SeqIter { inner: Seq<T> }`,
/// drained front-to-back with no auxiliary position). Used by
/// `harmonize_eq_or_ite_terms` to bridge iterator terms to Seq via
/// `coerce_to_seq` (the injective `__vec_to_seq_*` bridge with its #2116
/// View-anchor congruence) instead of falling through to `coerce_ite_sorts`,
/// which mints a fresh unconstrained constant that discards the value.
/// (ce-census 2026-08-20, ghost/seq_iter reverse_ghost loop_initialization)
pub(in crate::encoder) fn sort_is_seq_iterator_carrier(sort: &Sort) -> bool {
    match sort {
        Sort::Uninterpreted(name) => is_seq_iterator_sort_leaf(name),
        Sort::Datatype(dt) => is_seq_iterator_sort_leaf(&dt.name),
        _ => false,
    }
}

/// Stable string key for a ay Sort, used for bridge UF naming.
fn sort_display_key(sort: &Sort) -> String {
    match sort {
        Sort::Int => "Int".to_string(),
        Sort::Bool => "Bool".to_string(),
        Sort::Uninterpreted(name) => name.replace("::", "_"),
        Sort::Datatype(dt) => dt.name.replace("::", "_"),
        Sort::Array(_) => "Array".to_string(),
        Sort::Seq(_) => "Seq".to_string(),
        _ => format!("{sort:?}"),
    }
}

#[cfg(test)]
#[allow(clippy::items_after_test_module)]
mod tests {
    use std::sync::Arc;

    use ay_dpll::api::{SolveResult, Solver, Sort, Term, TermKind};
    use ntest::timeout;
    use trust_wp_core::formula::{ExprSort, PureExpr};

    use super::AYEncoder;

    fn seq_var(name: &str) -> PureExpr {
        PureExpr::Var(name.to_string(), Some(ExprSort::Seq))
    }

    fn term_contains_app(solver: &Solver, term: Term, expected: &str) -> bool {
        matches!(solver.term_kind(term), TermKind::App { name, .. } if name == expected)
            || solver
                .term_children(term)
                .into_iter()
                .any(|child| term_contains_app(solver, child, expected))
    }

    fn contradictory_extensional_pair(reverse: bool) -> SolveResult {
        let mut encoder = AYEncoder::new_all();
        let seq_sort = encoder.get_seq_sort();
        let first = encoder.solver.declare_const("first_seq", seq_sort.clone());
        let second = encoder.solver.declare_const("second_seq", seq_sort);
        let (first_array, second_array) = if reverse {
            let second_array = encoder.seq_array_term(second).unwrap();
            let first_array = encoder.seq_array_term(first).unwrap();
            (first_array, second_array)
        } else {
            let first_array = encoder.seq_array_term(first).unwrap();
            let second_array = encoder.seq_array_term(second).unwrap();
            (first_array, second_array)
        };
        let first_len = encoder.seq_len_projector_term(first).unwrap();
        let zero = encoder.solver.int_const(0);
        let first_is_nonempty = encoder.solver.gt(first_len, zero);
        let same_argument = encoder.seq_aware_equality_term(first, second);
        let same_value = encoder.solver.eq(first_array, second_array);
        let different_value = encoder.solver.not(same_value);
        encoder.solver.assert_term(first_is_nonempty);
        encoder.solver.assert_term(same_argument);
        encoder.solver.assert_term(different_value);
        encoder.check_sat()
    }

    #[test]
    #[timeout(30000)]
    fn symbolic_seq_index_restores_mapping_term_2316() {
        let mut encoder = AYEncoder::new();
        let index_expr = PureExpr::MethodCall {
            receiver: Arc::new(seq_var("preds")),
            method: "index_logic".to_string(),
            args: vec![PureExpr::Int(0)],
        };

        let index_term = encoder
            .encode_pure(&index_expr)
            .expect("symbolic seq index should encode");
        assert_eq!(
            encoder.solver.get_sort(index_term),
            Sort::Int,
            "symbolic seq indexing still produces an Int carrier term"
        );
        assert!(
            encoder.seq_state.has_seq_index_source(&index_term),
            "seq index provenance should be recorded for later restoration"
        );

        let mapping_sort = Sort::Uninterpreted("Mapping".to_string());
        let restored = encoder
            .try_restore_seq_element_from_int(index_term, &mapping_sort)
            .expect("symbolic seq element should restore to Mapping");
        assert_eq!(
            encoder.solver.get_sort(restored),
            mapping_sort,
            "restored symbolic seq element should use Mapping sort"
        );

        let restored_again = encoder
            .try_restore_seq_element_from_int(
                index_term,
                &Sort::Uninterpreted("Mapping".to_string()),
            )
            .expect("restoration should be stable across repeated uses");
        assert_eq!(
            restored, restored_again,
            "same seq/index source should restore to the same Mapping term"
        );
    }

    #[test]
    fn observed_seq_element_bridge_terms_get_exact_injectivity() {
        let mut encoder = AYEncoder::new();
        let sort = Sort::Uninterpreted("ObservedElem".to_string());
        let left = encoder.solver.declare_const("left", sort.clone());
        let right = encoder.solver.declare_const("right", sort);
        let bridged_left = encoder.coerce_seq_element_to_int(left);
        let bridged_right = encoder.coerce_seq_element_to_int(right);
        let same_image = encoder.solver.eq(bridged_left, bridged_right);
        let same_source = encoder.solver.eq(left, right);
        let distinct_sources = encoder.solver.not(same_source);
        encoder.solver.assert_term(same_image);
        encoder.solver.assert_term(distinct_sources);

        assert!(matches!(encoder.check_sat(), SolveResult::Unsat(_)));
    }

    #[test]
    fn unobserved_seq_element_bridge_term_is_not_globally_strengthened() {
        let mut encoder = AYEncoder::new();
        let sort = Sort::Uninterpreted("UnobservedElem".to_string());
        let observed = encoder.solver.declare_const("observed", sort.clone());
        let unobserved = encoder.solver.declare_const("unobserved", sort.clone());
        let observed_image = encoder.coerce_seq_element_to_int(observed);

        // Apply the bridge directly so this source stays outside WP's observed
        // finite-grounding lane.
        let bridge = encoder.ensure_seq_element_bridge_fn(&sort);
        let unobserved_image = encoder.solver.apply(&bridge, &[unobserved]);
        let same_image = encoder.solver.eq(observed_image, unobserved_image);
        let same_source = encoder.solver.eq(observed, unobserved);
        let distinct_sources = encoder.solver.not(same_source);
        encoder.solver.assert_term(same_image);
        encoder.solver.assert_term(distinct_sources);

        assert!(matches!(encoder.check_sat(), SolveResult::Sat));
        assert!(encoder
            .solver
            .assertions()
            .iter()
            .all(|term| encoder.solver.term_kind(*term) != TermKind::Forall));
    }

    #[test]
    fn seq_length_nonnegativity_is_grounded_only_for_observed_receivers() {
        let mut observed_encoder = AYEncoder::new();
        let seq_sort = observed_encoder.get_seq_sort();
        let observed = observed_encoder
            .solver
            .declare_const("observed_seq", seq_sort);
        let observed_len = observed_encoder
            .seq_len_term(observed)
            .expect("observed Seq length should encode");
        let zero = observed_encoder.solver.int_const(0);
        let negative = observed_encoder.solver.lt(observed_len, zero);
        observed_encoder.solver.assert_term(negative);
        assert!(matches!(
            observed_encoder.check_sat(),
            SolveResult::Unsat(_)
        ));

        let mut unobserved_encoder = AYEncoder::new();
        let funcs = unobserved_encoder.seq_funcs();
        let seq_sort = unobserved_encoder.get_seq_sort();
        let unobserved = unobserved_encoder
            .solver
            .declare_const("unobserved_seq", seq_sort);
        let raw_len = unobserved_encoder
            .solver
            .apply(&funcs.seq_len, &[unobserved]);
        let zero = unobserved_encoder.solver.int_const(0);
        let negative = unobserved_encoder.solver.lt(raw_len, zero);
        unobserved_encoder.solver.assert_term(negative);
        assert!(unobserved_encoder
            .solver
            .assertions()
            .iter()
            .all(|term| unobserved_encoder.solver.term_kind(*term) != TermKind::Forall));
    }

    #[test]
    fn seq_array_component_proxy_is_stable_and_uf_free() {
        let mut encoder = AYEncoder::new_all();
        let seq_sort = encoder.get_seq_sort();
        let observed = encoder.solver.declare_const("observed_seq", seq_sort);
        let first = encoder.seq_array_term(observed).unwrap();
        let duplicate = encoder.seq_array_term(observed).unwrap();

        assert_eq!(first, duplicate, "one observed application needs one proxy");
        let first_kind = encoder.solver.term_kind(first);
        assert!(
            matches!(first_kind, TermKind::Var { ref name } if name.starts_with("seq_array_proxy")),
            "expected proxy var, got {first_kind:?}; SMT:\n{}",
            encoder.solver.to_smtlib2()
        );
        assert!(encoder
            .solver
            .assertions()
            .iter()
            .all(|term| !term_contains_app(&encoder.solver, *term, "seq_array")));
    }

    #[test]
    fn nonempty_seq_array_extensional_equality_is_complete_in_both_orders() {
        let forward = contradictory_extensional_pair(false);
        assert!(matches!(forward, SolveResult::Unsat(_)), "{forward:?}");
        let reverse = contradictory_extensional_pair(true);
        assert!(matches!(reverse, SolveResult::Unsat(_)), "{reverse:?}");
    }

    #[test]
    fn unobserved_seq_array_term_does_not_gain_a_proxy_or_constraint() {
        let mut encoder = AYEncoder::new_all();
        let seq_sort = encoder.get_seq_sort();
        let observed = encoder
            .solver
            .declare_const("observed_seq", seq_sort.clone());
        let unobserved = encoder.solver.declare_const("unobserved_seq", seq_sort);
        let _ = encoder.seq_array_term(observed).unwrap();

        assert!(encoder.seq_state.get_seq_array_aux(&unobserved).is_none());
        let result = encoder.check_sat();
        assert!(matches!(result, SolveResult::Sat), "{result:?}");
    }

    // --- restore-route audit (2026-08-26): the residual M4 named ---------
    //
    // `try_restore_seq_element_from_int` reconstructs a Seq element as
    // `__seq_index_restore_<sort>(seq, index)` — a function of the Seq and the
    // index ALONE. At a mut-ref prophecy carrier sort that is an IDENTITY
    // CLAIM: two distinct borrows harmonized against the same element both
    // become that one term, so `a == b` and `id(a) == id(b)`. That is the
    // bug/869 borrow-identity collapse.

    /// Register a symbolic `preds[0]` and return its Int element token (the
    /// term the restore route keys on) together with the carrier sort of
    /// `&mut i32`.
    fn restore_route_fixture(encoder: &mut AYEncoder) -> (Term, Sort) {
        let index_expr = PureExpr::MethodCall {
            receiver: Arc::new(seq_var("preds")),
            method: "index_logic".to_string(),
            args: vec![PureExpr::Int(0)],
        };
        let index_term = encoder
            .encode_pure(&index_expr)
            .expect("symbolic seq index should encode");
        assert_eq!(
            encoder.solver.get_sort(index_term),
            Sort::Int,
            "the element arrives through the Int carrier"
        );
        assert!(
            encoder.seq_state.has_seq_index_source(&index_term),
            "the restore route needs the (seq, index) provenance"
        );
        let carrier = encoder.sort_from_expr_sort(ExprSort::MutRef(Box::new(ExprSort::Int)));
        (index_term, carrier)
    }

    /// Declare a borrow carrier with pinned `(current, final, id)` components —
    /// what the driver's not-final/id analysis produces for a real `&mut`.
    fn restore_route_borrow(
        encoder: &mut AYEncoder,
        carrier: &Sort,
        name: &str,
        current: i64,
        final_val: i64,
        id: i64,
    ) -> Term {
        let term = encoder.solver.declare_const(name, carrier.clone());
        let current = encoder.solver.int_const(current);
        let final_val = encoder.solver.int_const(final_val);
        let id = encoder.solver.int_const(id);
        encoder
            .bind_whole_mut_ref(carrier, &Sort::Int, term, current, final_val, id)
            .expect("bind the borrow's (current, final, id)");
        term
    }

    /// THE PIN. A carrier-sorted target is REFUSED: no `__seq_index_restore_*`
    /// is minted at the `(current, final, id)` record sort, and no carrier
    /// element bridge is declared for it.
    #[test]
    #[timeout(30000)]
    fn restore_route_refuses_a_mut_ref_carrier_target() {
        let mut encoder = AYEncoder::new_all();
        let (index_term, carrier) = restore_route_fixture(&mut encoder);

        assert!(
            encoder
                .try_restore_seq_element_from_int(index_term, &carrier)
                .is_none(),
            "reconstructing a Seq element at a prophecy-carrier sort must be refused"
        );
        assert!(
            encoder
                .seq_state
                .get_seq_index_restore_fn(&super::seq_index_restore_key(&carrier))
                .is_none(),
            "a refused restore must not declare the carrier restore function"
        );
    }

    /// The refusal follows the CARRIER, not the spelling: a datatype whose
    /// field sits at the carrier sort (the M1/M3 `Option<&mut T>` family) is
    /// refused too — `some_value(restore(s, i))` would collapse identically.
    #[test]
    #[timeout(30000)]
    fn restore_route_refuses_a_datatype_that_embeds_a_carrier() {
        let mut encoder = AYEncoder::new_all();
        let (index_term, carrier) = restore_route_fixture(&mut encoder);
        let family = crate::encoder::match_enc::stdlib_option_datatype_for_payload(carrier);
        encoder.ensure_datatype_declared(&family);
        let option_sort = Sort::Datatype(family);

        assert!(
            encoder
                .try_restore_seq_element_from_int(index_term, &option_sort)
                .is_none(),
            "a datatype carrying a prophecy slot must be refused as well"
        );
    }

    /// THE TEETH — the guard disabled, exercising the identical minting code
    /// through `mint_seq_index_restore_unguarded`. Two borrows with distinct
    /// ids, each equated to the reconstruction of the SAME Seq element, force
    /// `a == b` and contradict their distinct ids: UNSAT. On a real VC that is
    /// a vacuous base (every goal "proves").
    #[test]
    #[timeout(30000)]
    fn restore_route_teeth_two_borrows_at_one_element_collapse_borrow_ids() {
        let mut encoder = AYEncoder::new_all();
        let (index_term, carrier) = restore_route_fixture(&mut encoder);
        let a = restore_route_borrow(&mut encoder, &carrier, "a", 3, 7, 1);
        let b = restore_route_borrow(&mut encoder, &carrier, "b", 4, 8, 2);

        let restored_a = encoder
            .mint_seq_index_restore_unguarded(index_term, &carrier)
            .expect("the unguarded route mints a carrier element");
        let restored_b = encoder
            .mint_seq_index_restore_unguarded(index_term, &carrier)
            .expect("the unguarded route mints a carrier element");
        assert_eq!(
            restored_a, restored_b,
            "one (seq, index) source reconstructs to ONE term — the collapse enabler"
        );

        let eq_a = encoder.solver.eq(a, restored_a);
        let eq_b = encoder.solver.eq(b, restored_b);
        encoder.assert_term(eq_a);
        encoder.assert_term(eq_b);

        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Unsat(_)),
            "the unguarded route must reproduce the id collapse (two distinct \
             borrows forced equal), got {result:?}"
        );
    }

    /// THE GUARDED TWIN of the teeth. Same two borrows, same element — but
    /// with the refusal in force each side takes its caller's fallback, a
    /// FRESH per-call constant (`coerce_ite_sorts` mints
    /// `__trust_wp_coerce_<n>` from a global counter). No identity is forced
    /// and the base stays satisfiable.
    #[test]
    #[timeout(30000)]
    fn restore_route_guarded_two_borrows_keep_distinct_ids() {
        let mut encoder = AYEncoder::new_all();
        let (index_term, carrier) = restore_route_fixture(&mut encoder);
        let a = restore_route_borrow(&mut encoder, &carrier, "a", 3, 7, 1);
        let b = restore_route_borrow(&mut encoder, &carrier, "b", 4, 8, 2);

        assert!(
            encoder
                .try_restore_seq_element_from_int(index_term, &carrier)
                .is_none()
                && encoder
                    .try_restore_seq_element_from_int(index_term, &carrier)
                    .is_none(),
            "both harmonizations must be refused"
        );
        let fallback_a = encoder
            .solver
            .declare_const("__trust_wp_coerce_0", carrier.clone());
        let fallback_b = encoder.solver.declare_const("__trust_wp_coerce_1", carrier);
        let eq_a = encoder.solver.eq(a, fallback_a);
        let eq_b = encoder.solver.eq(b, fallback_b);
        encoder.assert_term(eq_a);
        encoder.assert_term(eq_b);

        let result = encoder.check_sat();
        assert!(
            matches!(result, SolveResult::Sat),
            "with the restore refused the two borrows must stay distinct, got {result:?}"
        );
    }

    /// CONTROL: the refusal is scoped to prophecy carriers. A value-sorted
    /// target still reconstructs — the #2316 behaviour the route exists for
    /// (and which `symbolic_seq_index_restores_mapping_term_2316` pins) must
    /// survive, including its two-uses-one-term stability.
    #[test]
    #[timeout(30000)]
    fn restore_route_still_reconstructs_a_value_sorted_element() {
        let mut encoder = AYEncoder::new_all();
        let (index_term, _carrier) = restore_route_fixture(&mut encoder);
        let mapping = Sort::Uninterpreted("Mapping".to_string());

        let first = encoder
            .try_restore_seq_element_from_int(index_term, &mapping)
            .expect("a value-sorted element must still restore");
        let second = encoder
            .try_restore_seq_element_from_int(index_term, &mapping)
            .expect("a value-sorted element must still restore");
        assert_eq!(first, second, "value-sort restoration stays stable");
        assert_eq!(encoder.solver.get_sort(first), mapping);
    }
}

fn seq_element_bridge_key(sort: &Sort) -> String {
    format!("__seq_elem_{}", sort_display_key(sort))
}

fn seq_index_restore_key(sort: &Sort) -> String {
    format!("__seq_index_restore_{}", sort_display_key(sort))
}

impl AYEncoder {
    /// Apply an injective representation bridge and materialize exactly the
    /// instances needed by the closed terms observed so far.
    fn apply_observed_injective_bridge(
        &mut self,
        bridge_key: &str,
        bridge_fn: &FuncDecl,
        term: Term,
    ) -> Term {
        let bridged = self.solver.apply(bridge_fn, &[term]);
        if self.quantifier_state.quantifier_depth() > 0 {
            return bridged;
        }

        let prior_terms = self
            .injective_bridge_ground_terms
            .get(bridge_key)
            .cloned()
            .unwrap_or_default();
        for prior in prior_terms {
            if prior == term {
                continue;
            }
            let prior_bridged = self.solver.apply(bridge_fn, &[prior]);
            let images_equal = self.eq_term(bridged, prior_bridged);
            let sources_equal = self.eq_term(term, prior);
            let injective_instance = self.solver.implies(images_equal, sources_equal);
            self.solver.assert_term(injective_instance);
        }

        let observed = self
            .injective_bridge_ground_terms
            .entry(bridge_key.to_string())
            .or_default();
        if !observed.contains(&term) {
            observed.push(term);
        }
        bridged
    }

    fn seq_push_back_payload_term(&self, term: Term) -> Option<Term> {
        let TermKind::App { name, num_args: 2 } = self.solver.term_kind(term) else {
            return None;
        };
        if name != "seq_push_back" {
            return None;
        }
        let children = self.solver.term_children(term);
        let [_, payload] = children.as_slice() else {
            return None;
        };
        Some(*payload)
    }

    fn terms_are_distinct_constants_for_seq(&self, lhs: Term, rhs: Term) -> bool {
        let lhs_sort = self.solver.get_sort(lhs);
        let rhs_sort = self.solver.get_sort(rhs);
        lhs_sort == rhs_sort
            && matches!(lhs_sort, Sort::Bool | Sort::Int | Sort::Real)
            && matches!(self.solver.term_kind(lhs), TermKind::Const)
            && matches!(self.solver.term_kind(rhs), TermKind::Const)
            && self.solver.format_term(lhs) != self.solver.format_term(rhs)
    }

    /// Coerce an Int fallback carrier into the native Seq sort for contexts
    /// where the source expression is semantically known to be Seq.
    pub(in crate::encoder) fn bridge_int_to_seq_carrier(&mut self, term: Term) -> Term {
        if self.solver.term_sort(term) != Sort::Int {
            return term;
        }

        crate::encoder::unsoundness::increment(
            crate::encoder::unsoundness::UnsoundnessCategory::SortCoercionBridge,
        );
        let seq_sort = self.get_seq_sort();
        let bridge_name = "__int_to_seq_bridge";
        let bridge_fn = if let Some(existing) = self.seq_state.get_bridge_fn(bridge_name) {
            existing.clone()
        } else {
            let bridge =
                self.solver
                    .declare_fun(bridge_name, std::slice::from_ref(&Sort::Int), seq_sort);
            self.seq_state
                .insert_bridge_fn(bridge_name.to_string(), bridge.clone());
            bridge
        };
        self.solver.apply(&bridge_fn, &[term])
    }

    fn ensure_seq_element_bridge_fn(&mut self, term_sort: &Sort) -> FuncDecl {
        let bridge_key = seq_element_bridge_key(term_sort);
        if let Some(existing) = self.seq_state.get_bridge_fn(&bridge_key) {
            return existing.clone();
        }

        let bridge =
            self.solver
                .declare_fun(&bridge_key, std::slice::from_ref(term_sort), Sort::Int);
        self.seq_state.insert_bridge_fn(bridge_key, bridge.clone());
        bridge
    }

    /// Coerce a term to Seq sort if it was declared with a Vec-like
    /// Uninterpreted sort (e.g., `Uninterpreted("std::vec::Vec")`).
    ///
    /// The ay solver rejects function application when argument sorts don't
    /// match. Seq UF functions (seq_len, seq_array, seq_offset) expect
    /// `Sort::Seq(Int)`, but terms from the driver sometimes arrive as
    /// `Uninterpreted("std::vec::Vec")` or similar when the sort normalization
    /// in `get_or_declare_var` was bypassed (e.g., terms created via
    /// `rebind_var`, quantifier-bound variables, or direct `vars.insert`).
    ///
    /// When a mismatch is detected, this method declares a bridge
    /// UF `__vec_to_seq: Vec-Sort -> Seq` (once per Vec-like sort name) and
    /// applies it to produce a Seq-sorted term. The bridge is an uninterpreted
    /// function, so ay treats `__vec_to_seq(x)` as an opaque Seq value.
    ///
    /// **Soundness note:** UFs guarantee *congruence* (`x == y => f(x) == f(y)`)
    /// but NOT *injectivity* (`f(x) == f(y) => x == y`) by default. An explicit
    /// injectivity axiom is asserted for each bridge UF to prevent the solver from
    /// collapsing two distinct Vec terms to the same Seq value. (#2163)
    /// The proper long-term fix is to normalize Vec sorts to Seq at declaration
    /// time so the bridge is unnecessary. See #2124.
    /// (#2124)
    pub(crate) fn coerce_to_seq(&mut self, term: Term) -> Term {
        let term_sort = self.solver.term_sort(term);
        let seq_sort = self.get_seq_sort();
        if term_sort == seq_sort {
            return term;
        }
        // Determine a bridge key for the term's sort. We coerce:
        // (a) Known Seq-model types (Vec, VecDeque, List, Seq) — always safe.
        // (b) ay Datatype sorts (e.g., Adt_Cons_Nil from match encoding) —
        //     user-defined ADTs whose view is Seq but whose ay sort is a
        //     native Datatype, not Uninterpreted. (#2155)
        // (c) Any other Uninterpreted sort that isn't a known non-Seq category
        //     (FMap, Unit, Bool, Int) — catches user-defined ADT types whose
        //     view is Seq but that aren't in the is_seq_model_type list.
        //     We do NOT coerce FMap/Unit since those indicate a dispatch bug
        //     that should surface as an error.
        let sort_name = if term_sort.is_seq() {
            Some("native_seq".to_string())
        } else {
            match &term_sort {
                Sort::Uninterpreted(name) => {
                    let type_name = name.rsplit("::").next().unwrap_or(name);
                    if super::super::sort_context::sort_inference::is_seq_model_type(type_name) {
                        // (a) Known Seq-model type
                        Some(name.clone())
                    } else if super::super::sort_context::sort_inference::is_fmap_model_type(
                        type_name,
                    ) || matches!(type_name, "Unit" | "FSet")
                    {
                        // Known non-Seq category — do not coerce (dispatch bug)
                        None
                    } else {
                        // (c) Unknown ADT type in a Seq context — coerce defensively.
                        // User-defined types like custom list implementations may
                        // have Seq as their deep model but aren't in the static list.
                        Some(name.clone())
                    }
                }
                Sort::Datatype(dt) => {
                    // (b) ay native Datatype sort (from match encoding).
                    // e.g., Adt_Cons_Nil for List's cons/nil constructors.
                    Some(dt.name.clone())
                }
                _ => None,
            }
        };
        let Some(sort_name) = sort_name else {
            return term;
        };
        let is_iterator_sort = is_seq_iterator_sort_leaf(&sort_name);
        let bridge_key = format!("__vec_to_seq_{}", sort_name.replace("::", "_"));
        // Get or create the bridge UF for this sort name.
        let bridge_fn = if let Some(existing) = self.seq_state.get_bridge_fn(&sort_name) {
            existing.clone()
        } else {
            let bridge = self.solver.declare_fun(
                &bridge_key,
                std::slice::from_ref(&term_sort),
                seq_sort.clone(),
            );
            self.seq_state.insert_bridge_fn(sort_name, bridge.clone());
            bridge
        };
        // Re-materialize observed pairwise injectivity even on a cache hit:
        // observations survive a slice pop while scoped assertions may not.
        let coerced = self.apply_observed_injective_bridge(&bridge_key, &bridge_fn, term);
        self.seq_state.insert_coerced_term(term, coerced);

        // View-term unification anchor for Seq-backed iterators (#2116).
        //
        // `View(iter)` of a `SeqIter`/`IntoIter` reaches the solver as TWO
        // distinct terms that the encoder never makes congruent:
        //   1. this bridge UF `__vec_to_seq_<Sort>(iter)` — emitted whenever the
        //      raw iterator var is used in a Seq position (e.g. as a `concat`
        //      argument inside the for-loop structural invariant), and
        //   2. the View-projector proxy Seq var `<iter>_view` — emitted by the
        //      loop body's `produces`/`push_front` transition facts.
        // Without a connecting equality, the structural invariant's
        // `len(View(iter))` (bridge UF) is divorced from the body's
        // `len(View(iter)) >= 1` (proxy), so the inductive produced-length bound
        // never reaches the goal and reverse_ghost's preservation/postcondition
        // VCs fail.
        //
        // When the coerced term is a named iterator variable, declare the
        // canonical `<name>_view` proxy Seq var and assert `bridge(iter) ==
        // <name>_view`. SOUND: the bridge UF `__vec_to_seq_<Sort>(iter)` IS, by
        // definition, the Seq view of `iter`, and `<name>_view` is the Seq view
        // of the SAME variable — equating them unifies two faithful
        // representations of one value, never two distinct values. Gated to
        // iterator sorts so non-iterator coercions (Vec/List/user ADTs) are
        // untouched.
        if is_iterator_sort {
            if let TermKind::Var { name } = self.solver.term_kind(term) {
                let proxy_name = format!("{name}_view");
                if let Ok(proxy) = self.get_or_declare_var(&proxy_name, seq_sort.clone()) {
                    let anchor = self.eq_term(coerced, proxy);
                    self.solver.assert_term(anchor);
                }
            }
        }

        // Native-selector unification anchor for single-Seq-field structs
        // (list_reversal_lasso `Memory(Vec<Ptr>)`).
        //
        // The Seq view of a transparent single-field Vec wrapper reaches the
        // solver as TWO distinct terms:
        //   1. this bridge UF `__vec_to_seq_<Sort>(x)` — emitted when the
        //      driver's newtype collapse leaves the raw ADT var in a Seq
        //      position at MIR call sites (`x.0@` collapsed onto `x`), and
        //   2. the native datatype field selector `<field0>(x)` — emitted by
        //      logic-fn registration for the same `x.0@` inside #[logic]
        //      bodies (e.g. `memory_0(self)` in nonnull_ptr / index_logic
        //      defining axioms).
        // Without a connecting equality, call-site facts and defining axioms
        // talk about disconnected Seq values and the goal never closes.
        //
        // Assert the ground per-term link `bridge(x) == field0(x)`, gated to
        // registered single-constructor structs whose ONLY field is
        // Seq-sorted. SOUND: for such a struct the field IS the canonical Seq
        // view — this equates two faithful representations of one value
        // (mirrors the iterator view anchor above).
        if let Sort::Datatype(dt) = &term_sort {
            if let [ctor] = dt.constructors.as_slice() {
                if let [field] = ctor.fields.as_slice() {
                    if field.sort == seq_sort {
                        if let Ok(selector) =
                            self.solver
                                .try_datatype_selector(&field.name, term, field.sort.clone())
                        {
                            let anchor = self.eq_term(coerced, selector);
                            self.solver.assert_term(anchor);
                        }
                    }
                }
            }
        }

        coerced
    }

    /// Coerce a non-Int element term to Int sort for use in Seq operations.
    ///
    /// Seq element operations (`seq_contains`, `seq_push_back`) are declared with
    /// `Sort::Int` element sort. When the actual element has a different sort
    /// (e.g., Tuple2 from `__trust_wp_tuple2(k1, v)`), this method declares an
    /// injective bridge UF `__trust_wp_seq_elem_<sort>: <sort> -> Int` and applies
    /// it to produce an Int-sorted term.
    ///
    /// If the element already has Int sort, it is returned unchanged.
    ///
    /// **Soundness note:** injectivity is materialized for every pair of closed
    /// source terms observed through the bridge. This is exactly the finite
    /// equality reflection available to the current VC. (#994)
    pub(in crate::encoder) fn coerce_seq_element_to_int(&mut self, term: Term) -> Term {
        let term_sort = self.solver.term_sort(term);
        if term_sort == Sort::Int {
            return term;
        }
        let bridge_key = seq_element_bridge_key(&term_sort);
        let bridge_fn = self.ensure_seq_element_bridge_fn(&term_sort);
        let coerced = self.apply_observed_injective_bridge(&bridge_key, &bridge_fn, term);
        self.seq_state.insert_coerced_term(term, coerced);
        self.seq_state
            .insert_seq_elem_source(coerced, term_sort, term);
        coerced
    }

    /// Recover a bridged Seq element back to its original non-Int sort.
    ///
    /// `coerce_seq_element_to_int` stores non-Int Seq elements as bridge-UF
    /// applications of sort `Int`. When a later equality compares such an Int
    /// token against a richer sort (for example `Mapping` in
    /// `result[i]@ == _pred[i]`), replacing the token with a fresh constant
    /// discards the element semantics. Direct bridge tokens map back to their
    /// exact source; indexed tokens get a stable reconstruction term plus an
    /// exact ground bridge equality. (#2316)
    ///
    /// FAIL-CLOSED on mut-ref prophecy carriers (restore-route audit
    /// 2026-08-26, the residual M4 named). See
    /// [`Self::mint_seq_index_restore_unguarded`] for why.
    pub(crate) fn try_restore_seq_element_from_int(
        &mut self,
        term: Term,
        target_sort: &Sort,
    ) -> Option<Term> {
        if self.solver.term_sort(term) != Sort::Int || *target_sort == Sort::Int {
            return None;
        }
        // Exact recovery: this Int token IS a bridged source term, so hand back
        // the very term that was bridged in. An identity, never a fabrication —
        // sound at every sort, carriers included.
        if let Some(original_sort) = self.seq_state.get_seq_elem_sort(&term) {
            if original_sort != target_sort {
                return None;
            }

            return self.seq_state.get_seq_elem_source(&term);
        }

        // THE GUARD. Refuse to RECONSTRUCT an element at a prophecy-carrier
        // sort. Refusing returns `None`, and every caller's fallback
        // (`coerce_ite_sorts`, `coerce_to_mapping`) mints a FRESH per-call
        // constant — strictly weaker than the restore, so this can only remove
        // information, never add a premise.
        //
        // Measured live: 20 firings across `cc/seq` (a ghost `Seq<&mut usize>`),
        // `take_first_mut` and `pair_bor_mut`, with byte-identical status and
        // telemetry on all three (restore-route audit 2026-08-26). The route is
        // reachable; the refusal is free.
        if self.restore_target_carries_a_prophecy_slot(target_sort) {
            return None;
        }

        self.mint_seq_index_restore_unguarded(term, target_sort)
    }

    /// Whether reconstructing a Seq element at `target_sort` would mint a term
    /// that carries a prophecy slot — the fail-closed condition of the guard
    /// above.
    ///
    /// Resolves `Sort::Uninterpreted(name)` spellings of declared datatypes
    /// through the encoder's own registry, because a carrier-payload `Option`
    /// family reaches the encoder under BOTH spellings: `Sort::Datatype(family)`
    /// (whose field sorts the predicate can read directly) and
    /// `Sort::Uninterpreted(family.name)` (whose payload is only recoverable
    /// from the declaration — `stdlib_option_datatype_for_payload` hex-encodes
    /// the payload into the family NAME, which is not the carrier grammar).
    fn restore_target_carries_a_prophecy_slot(&self, target_sort: &Sort) -> bool {
        crate::encoder::sort_context::sort_mapping::ay_sort_contains_mut_ref_carrier_with(
            target_sort,
            &|name| self.get_datatype_decl(name).cloned(),
        )
    }

    /// The seq-index reconstruction branch of
    /// [`Self::try_restore_seq_element_from_int`], WITHOUT its carrier guard.
    ///
    /// **Every caller must go through the guarded entry point.** This body is
    /// split out only so the guard's teeth can be demonstrated by a test that
    /// bypasses it (`restore_route_teeth_*`), exercising the identical minting
    /// code.
    ///
    /// Why the guard exists: `__seq_index_restore_<sort> : (Seq, Int) -> sort`
    /// is a function of the Seq and the index ALONE. Its only constraint is the
    /// roundtrip `__seq_elem_<sort>(restore(s, i)) == <the Int token>`; it
    /// carries no component content of its own. At a value sort that is merely
    /// information-destroying. At a `(current, final, id)` carrier sort it is an
    /// IDENTITY CLAIM: two distinct borrows harmonized against the same Seq
    /// element both become `restore(s, i)`, so `a == b` and therefore
    /// `id(a) == id(b)` — the bug/869 borrow-identity collapse, on a premise set
    /// that stays satisfiable (so no vacuity counter fires) whenever the ids are
    /// not separately pinned.
    fn mint_seq_index_restore_unguarded(
        &mut self,
        term: Term,
        target_sort: &Sort,
    ) -> Option<Term> {
        let (seq_term, index_term) = *self.seq_state.get_seq_index_source(&term)?;
        let restore_key = seq_index_restore_key(target_sort);
        let restore_fn = if let Some(existing) =
            self.seq_state.get_seq_index_restore_fn(&restore_key)
        {
            existing.clone()
        } else {
            let seq_sort = self.get_seq_sort();
            let restore =
                self.solver
                    .declare_fun(&restore_key, &[seq_sort, Sort::Int], target_sort.clone());
            self.seq_state
                .insert_seq_index_restore_fn(restore_key, restore.clone());
            restore
        };

        let restored = self.solver.apply(&restore_fn, &[seq_term, index_term]);
        let bridge_fn = self.ensure_seq_element_bridge_fn(target_sort);
        let bridge_key = seq_element_bridge_key(target_sort);
        let bridged = self.apply_observed_injective_bridge(&bridge_key, &bridge_fn, restored);
        let roundtrip = self.eq_term(bridged, term);
        self.assert_term(roundtrip);
        Some(restored)
    }

    /// Decompose Seq equality into component-wise Array+Length+Offset equality (#1317).
    ///
    /// When at least one of `lt` or `rt` has a `SeqValue` in the registry,
    /// the native Seq-sort `eq(lt, rt)` is undecidable — ay-dpll cannot
    /// leverage Array theory on `Sort::Seq(Int)` terms directly. This method
    /// decomposes the equality into three decidable conjuncts:
    ///
    ///   `seq_array(lt) == seq_array(rt)`   (Array extensional equality)
    ///   `seq_len(lt) == seq_len(rt)`       (Int equality)
    ///   `seq_offset(lt) == seq_offset(rt)` (Int equality)
    ///
    /// Returns `None` when neither term has a SeqValue and no Seq sort is
    /// detectable, allowing the caller to fall through to standard `eq`.
    ///
    /// Except for the explicitly certified temporal-monitor lane below, there
    /// are no side-effect assertions: the returned term IS the equality. The
    /// caller may negate it (for postcondition checking) or assert it directly.
    pub(in crate::encoder) fn try_decompose_seq_equality(
        &mut self,
        lt: Term,
        rt: Term,
    ) -> Result<Option<Term>, EncodingError> {
        if let (Some(lt_payload), Some(rt_payload)) = (
            self.seq_push_back_payload_term(lt),
            self.seq_push_back_payload_term(rt),
        ) {
            if self.terms_are_distinct_constants_for_seq(lt_payload, rt_payload) {
                return Ok(Some(self.solver.bool_const(false)));
            }
        }

        let lt_has_sv = self.seq_state.has_seq_value(&lt);
        let rt_has_sv = self.seq_state.has_seq_value(&rt);
        let both_ground_seq_terms = self.use_seq_len_proxies()
            && self.quantifier_state.quantifier_depth() == 0
            && crate::encoder::sort_context::is_seq_family_sort(&self.solver.get_sort(lt))
            && crate::encoder::sort_context::is_seq_family_sort(&self.solver.get_sort(rt));
        if !lt_has_sv && !rt_has_sv && !both_ground_seq_terms {
            // Neither term has a concrete representation and this is not a
            // finite ground Seq lane; fall through to native equality.
            return Ok(None);
        }

        // A symbolic temporal post-state assignment such as
        // `(^self)@ == self@.push_back(v)` is a particularly hostile negative
        // Array query: the contingent negation asks ay to find a model for an
        // extensional array disequality before an inexpensive scalar witness.
        // Give this relation one stable Bool identity. Its certificate is
        // emitted below, after the component formula is available.
        let temporal_pushback_assignment = (self.term_is_temporal_final_var(lt)
            && self.seq_push_back_payload_term(rt).is_some())
            || (self.term_is_temporal_final_var(rt)
                && self.seq_push_back_payload_term(lt).is_some());
        let temporal_monitor =
            if temporal_pushback_assignment && self.quantifier_state.quantifier_depth() == 0 {
                Some(
                    self.seq_state
                        .certified_equality_monitor(lt, rt)
                        .unwrap_or_else(|| {
                            self.solver
                                .fresh_var("seq_temporal_equality_monitor", Sort::Bool)
                        }),
                )
            } else {
                None
            };

        // Get components for both sides (fast-path from registry or UF fallback).
        let lt_arr = self.seq_array_term(lt)?;
        let lt_len = self.seq_len_projector_term(lt)?;
        let lt_off = self.seq_offset_term(lt)?;

        let rt_arr = self.seq_array_term(rt)?;
        let rt_len = self.seq_len_projector_term(rt)?;
        let rt_off = self.seq_offset_term(rt)?;

        // Check if either side has a known concrete length. When present,
        // use pointwise `select` comparisons instead of Array extensional
        // equality. ay-dpll's Array theory cannot efficiently decide
        // `NOT(array_eq)` when both sides involve UF-produced arrays and
        // concrete store chains, causing timeouts on negated postconditions.
        // Pointwise `select` produces Int equalities that ay handles well.
        // (#2242)
        let known_len = self
            .seq_state
            .get_seq_value(&lt)
            .and_then(|sv| sv.known_len)
            .or_else(|| {
                self.seq_state
                    .get_seq_value(&rt)
                    .and_then(|sv| sv.known_len)
            });

        let arr_eq = if let Some(n) = known_len {
            // Pointwise: select(lt_arr, lt_off+i) == select(rt_arr, rt_off+i)
            let mut conjuncts = Vec::with_capacity(n);
            for i in 0..n {
                #[allow(clippy::cast_possible_wrap)] // Seq known_len < 2^63
                let idx = self.solver.int_const(i as i64);
                let lt_idx = self.solver.add(lt_off, idx);
                let rt_idx = self.solver.add(rt_off, idx);
                let lt_sel = self.solver.select(lt_arr, lt_idx);
                let rt_sel = self.solver.select(rt_arr, rt_idx);
                conjuncts.push(self.eq_term(lt_sel, rt_sel));
            }
            if conjuncts.is_empty() {
                self.solver.bool_const(true)
            } else {
                conjuncts
                    .into_iter()
                    .reduce(|a, b| self.solver.and(a, b))
                    .expect("invariant: conjuncts is non-empty")
            }
        } else {
            // Fallback: extensional Array equality (may timeout on negation).
            self.eq_term(lt_arr, rt_arr)
        };
        let len_eq = self.eq_term(lt_len, rt_len);
        let off_eq = self.eq_term(lt_off, rt_off);

        // Empty sequences have no observable element or offset.  When the
        // length is symbolic at encoding time, retain that semantic case in
        // the formula instead of permanently requiring equality of backing
        // arrays that later premises may prove irrelevant:
        //
        //   len_l = len_r && (len_l = 0 || (array_l = array_r && off_l = off_r))
        //
        // For a known-empty SeqValue this simplifies to length equality.  The
        // non-empty lane keeps the existing conservative representation check.
        let mut decomposed = if known_len == Some(0) {
            len_eq
        } else if known_len.is_some() {
            let arr_and_len = self.solver.and(arr_eq, len_eq);
            self.solver.and(arr_and_len, off_eq)
        } else {
            let zero = self.solver.int_const(0);
            let is_empty = self.eq_term(lt_len, zero);
            let nonempty_shape = self.solver.and(arr_eq, off_eq);
            let shape_or_empty = self.solver.or(is_empty, nonempty_shape);
            self.solver.and(len_eq, shape_or_empty)
        };

        // In bound/non-finite lanes, special-case one side being the
        // `seq_empty` UF constant by including direct UF equality `lt == rt`
        // as an extra conjunct (trust-wp #994).
        //
        // The shape decomposition alone leaves `s` and `seq_empty` as
        // disconnected UF terms in ay-dpll's E-graph, even when their
        // projector triples agree. As a result, ground-level R1 instances
        // such as `reverse(seq_empty) == seq_empty` cannot propagate via
        // congruence to `reverse(s) == seq_empty`. This blocks
        // `ghost/seq_iter::reverse_ghost` at loop initialization where
        // both `produced` and `result` are bound to `seq_empty()` but the
        // invariant `result == produced.reverse()` ultimately needs
        // `reverse(produced) == seq_empty`.
        //
        // Restricting the direct-equality conjunct to the `seq_empty` case
        // preserves the existing behavior for `s.subsequence(0, s.len()) == s`
        // and other shape-only decompositions where two distinct UF terms
        // share a shape but cannot soundly be forced to be the same
        // UF identity. The finite ground lane intentionally omits it: its
        // carrier semantics are the exact Array+Length+Offset tuple, and a
        // native non-string Seq equality would escape that representation and
        // defeat independent SAT validation.
        let seq_empty = self.seq_state.funcs_clone().map(|f| f.seq_empty);
        if let Some(empty) = seq_empty {
            if (!self.use_seq_len_proxies() || self.quantifier_state.quantifier_depth() != 0)
                && (lt == empty || rt == empty)
            {
                let direct_eq = self.eq_term(lt, rt);
                decomposed = self.solver.and(direct_eq, decomposed);
            }
        }

        if let Some(monitor) = temporal_monitor {
            // A positive monitor must carry both identities:
            //
            //   monitor ==> native-carrier equality
            //   monitor ==> observable Array+Length+Offset equality
            //
            // The native leg prevents the monitor from becoming an
            // unconstrained verification oracle. The observable leg is
            // load-bearing for consumers which normalize a temporal carrier
            // through a distinct `final_*_view` term: native congruence alone
            // does not connect that normalized view to its registered Seq
            // components. Re-encoding the same assignment reuses `monitor`,
            // so `effect && !post` remains directly contradictory. With a
            // false monitor neither identity follows, preserving contingent
            // SAT countermodels. (#2828)
            if self.seq_state.certified_equality_monitor(lt, rt).is_none() {
                let native_identity = self.eq_term(lt, rt);
                let meaning = self.solver.and(native_identity, decomposed);
                let certificate = self.solver.implies(monitor, meaning);
                self.assert_solver_term("seq_temporal_equality_monitor/certificate", certificate);
                self.seq_state
                    .insert_certified_equality_monitor(lt, rt, monitor);
            }
            self.seq_state
                .insert_semantic_equality_certificate(lt, rt, vec![monitor]);
            return Ok(Some(monitor));
        }
        if self.use_seq_len_proxies() && self.quantifier_state.quantifier_depth() == 0 {
            let mut positive_leaves = Vec::new();
            self.collect_assertion_conjuncts(decomposed, &mut positive_leaves);
            self.seq_state
                .insert_semantic_equality_certificate(lt, rt, positive_leaves);
        }

        Ok(Some(decomposed))
    }
}
