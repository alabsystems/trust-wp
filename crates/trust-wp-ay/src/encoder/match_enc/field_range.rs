// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Ground ADT field-range assumptions for native match datatypes.

use ay_dpll::api::{DatatypeSort, Sort, Term, TermKind};
use trust_wp_core::logic::FieldRangeKind;

use super::{short_constructor_name, AYEncoder};

/// Maximum nesting depth (count of chained unary `App` selectors that
/// return the same datatype family) for which we still emit a ground
/// field-range constraint on a recursive-ADT scrutinee.
///
/// For recursive ADTs like `enum List { Cons(u32, Box<List>), Nil }`,
/// the ground pool can flush the `sum` body multiple rounds, producing
/// scrutinees `cons_1(self)`, `cons_1(cons_1(self))`, etc. Emitting a
/// field-range guard for every such deep scrutinee blows up the
/// quantifier search space without contributing facts that the
/// structural induction needs (the spec axiom + base case + one
/// constructor unfold are sufficient). (#5)
const MAX_RECURSIVE_FIELD_RANGE_DEPTH: usize = 1;

impl AYEncoder {
    /// Assert ground field-range assumptions for every already-bound encoder
    /// variable of this datatype's sort. Called once per datatype at
    /// declaration time (`ensure_datatype_declared`); variables bound after
    /// the declaration are covered by the `rebind_var` hook
    /// ([`Self::assert_field_range_assumptions_for_binding`]), and compound
    /// scrutinee terms by the match-encoding sites (#2178).
    ///
    /// History (#2097 → ay #enum-forall): this used to emit a universally
    /// quantified axiom per hinted field,
    /// `∀ x:ADT [is_Ctor(x)]. is_Ctor(x) → lo <= field(x) <= hi`,
    /// which is wrong on both ends:
    ///
    /// - Under term-algebra datatype semantics the axiom is UNSATISFIABLE
    ///   whenever the field's SMT sort (`Int`) is wider than `[lo, hi]`: the
    ///   datatype domain contains `Ctor(v)` for *every* integer `v`,
    ///   including out-of-range ones, so a datatype-complete solver refutes
    ///   the axiom outright and every obligation in the query would become
    ///   vacuously provable. The axiom only ever "worked" through
    ///   instantiation incompleteness.
    /// - ay-dpll's #enum-forall soundness gate correctly refuses to trust a
    ///   ground SAT while a `forall` over a datatype binder sits in the
    ///   assertion set (MBQI cannot synthesize datatype witnesses), so any
    ///   otherwise-ground obligation that merely *declared* a range-hinted
    ///   ADT degraded to `unknown (quantifier-unhandled)` — e.g.
    ///   `NonZero::new` in `type_invariants/borrows.rs` and
    ///   `vector/07_read_write.rs`.
    ///
    /// The intended meaning — "ADT values flowing through the program have
    /// integer fields within their Rust-type ranges" — is a statement about
    /// the specific terms of the VC, not about the whole datatype domain, and
    /// is exactly captured by the satisfiable ground per-term constraints of
    /// [`Self::assert_ground_field_range_constraints`]. This mirrors the
    /// discriminant-axiom precedent (`assert_datatype_discriminant_axioms`
    /// skips payload `forall`s for the same QuantifierUnhandled reason).
    pub(super) fn assert_adt_field_range_ground_assumptions(&mut self, datatype: &DatatypeSort) {
        if !self.has_adt_field_ranges(&datatype.name) {
            return;
        }
        let bound_terms: Vec<Term> = self
            .var_names()
            .into_iter()
            .filter(|name| {
                self.var_sort(name).is_some_and(|sort| match sort {
                    Sort::Datatype(dt) => dt.name == datatype.name,
                    Sort::Uninterpreted(n) => *n == datatype.name,
                    _ => false,
                })
            })
            .filter_map(|name| self.var_term(&name))
            .collect();
        for term in bound_terms {
            self.assert_ground_field_range_constraints(term, datatype);
        }
    }

    /// Assert ground field-range assumptions for a freshly (re)bound variable
    /// of an already-declared, range-hinted datatype sort.
    ///
    /// Invoked from [`AYEncoder::rebind_var`], the chokepoint every production
    /// variable binding flows through (fresh declarations, sort upgrades,
    /// result/borrow rebinding). Bindings made *before* the datatype is
    /// declared are picked up by the declaration-time sweep instead
    /// ([`Self::assert_adt_field_range_ground_assumptions`]). Quantifier
    /// binders are unaffected: quantifier body encoding uses
    /// `insert_var`/`restore_var`, never `rebind_var`.
    pub(in crate::encoder) fn assert_field_range_assumptions_for_binding(
        &mut self,
        term: Term,
        sort: &Sort,
    ) {
        let name = match sort {
            Sort::Datatype(dt) => dt.name.as_str(),
            Sort::Uninterpreted(name) => name.as_str(),
            _ => return,
        };
        if !self.has_adt_field_ranges(name) {
            return;
        }
        // The registered declaration carries the constructor/field layout the
        // solver knows about; without one there are no testers or selectors
        // to constrain yet (the declaration-time sweep covers the binding).
        let Some(datatype) = self.get_datatype_decl(name).cloned() else {
            return;
        };
        self.assert_ground_field_range_constraints(term, &datatype);
    }

    /// Assert ground (non-quantified) range constraints for a specific scrutinee.
    ///
    /// For each constructor field with a `FieldRangeKind` hint in
    /// `self.adt_field_ranges`, asserts on the given term:
    /// - Unsigned(bits): `is_Ctor(t) → field(t) >= 0 ∧ field(t) <= 2^bits - 1`
    /// - Signed(bits): `is_Ctor(t) → field(t) >= -2^(bits-1) ∧ field(t) <= 2^(bits-1) - 1`
    ///
    /// This prevents the solver from assigning impossible values (e.g., -1 for
    /// a u32 field) to program values, eliminating spurious 0-conflict SAT
    /// counterexamples (#2097). Ground instances are always available to the
    /// solver without E-matching and — unlike the retired quantified axiom
    /// (see [`Self::assert_adt_field_range_ground_assumptions`]) — they are
    /// satisfiable under term-algebra datatype semantics. (#2178)
    ///
    /// For recursive ADTs, scrutinees produced by nested unary selectors
    /// (e.g., `cons_1(cons_1(self))`) are skipped beyond
    /// [`MAX_RECURSIVE_FIELD_RANGE_DEPTH`] levels. The ground-pool flushing of
    /// the `sum`-style body for recursive logic functions would otherwise emit
    /// a fresh range axiom for every deeper tail constructor, inflating the
    /// quantifier search space without contributing new induction facts. (#5)
    pub(super) fn assert_ground_field_range_constraints(
        &mut self,
        scrutinee: Term,
        datatype: &DatatypeSort,
    ) {
        let Some(ctor_ranges) = self.adt_field_ranges_for(&datatype.name) else {
            return;
        };

        if datatype_is_recursive(datatype)
            && scrutinee_selector_chain_depth(self, scrutinee, datatype)
                > MAX_RECURSIVE_FIELD_RANGE_DEPTH
        {
            return;
        }

        for (ctor_name, field_ranges) in &ctor_ranges {
            let short_ctor = short_constructor_name(ctor_name);

            let Some(ctor) = datatype.constructors.iter().find(|c| c.name == short_ctor) else {
                continue;
            };

            let Ok(is_ctor) = self.solver.try_datatype_tester(short_ctor, scrutinee) else {
                continue;
            };

            for &(field_idx, range_kind) in field_ranges {
                let Some(field) = ctor.fields.get(field_idx) else {
                    continue;
                };

                let Ok(field_val) =
                    self.solver
                        .try_datatype_selector(&field.name, scrutinee, field.sort.clone())
                else {
                    continue;
                };

                let constraints = match range_kind {
                    FieldRangeKind::Unsigned(bits) => {
                        let zero = self.solver.int_const(0);
                        let ge_zero = self.solver.ge(field_val, zero);
                        if bits <= 63 {
                            let max_val = self.solver.int_const((1i64 << bits) - 1);
                            let le_max = self.solver.le(field_val, max_val);
                            self.solver.and(ge_zero, le_max)
                        } else {
                            ge_zero
                        }
                    }
                    FieldRangeKind::Signed(bits) => {
                        // Signed range: -2^(bits-1) <= field <= 2^(bits-1)-1.
                        let half = bits.saturating_sub(1);
                        let (min_val, max_val) = if half < 63 {
                            (
                                self.solver.int_const(-(1i64 << half)),
                                self.solver.int_const((1i64 << half) - 1),
                            )
                        } else if half == 63 {
                            // 64-bit signed (isize / i64): the bounds are exactly
                            // i64::MIN (-2^63) and i64::MAX (2^63-1), both directly
                            // representable. The old `1i64 << 63` overflowed, so this
                            // case was skipped, leaving isize/i64 struct fields
                            // UNBOUNDED — the solver could pick e.g. `p.x = 2^64`,
                            // defeating cast/comparison reasoning (#knights-tour
                            // Board::available, where p.x: isize on `struct Point`).
                            (
                                self.solver.int_const(i64::MIN),
                                self.solver.int_const(i64::MAX),
                            )
                        } else {
                            // i128 fields: bounds exceed i64; skip (rare, no const).
                            continue;
                        };
                        let ge_min = self.solver.ge(field_val, min_val);
                        let le_max = self.solver.le(field_val, max_val);
                        self.solver.and(ge_min, le_max)
                    }
                    #[allow(unreachable_patterns)]
                    _ => continue,
                };

                let guarded = self.solver.implies(is_ctor, constraints);
                self.solver.assert_term(guarded);
            }
        }
    }
}

/// Returns `true` when the datatype declaration has at least one constructor
/// field whose sort references the same datatype (i.e., the ADT is structurally
/// recursive, like `enum List { Cons(u32, Box<List>), Nil }`).
fn datatype_is_recursive(datatype: &DatatypeSort) -> bool {
    datatype
        .constructors
        .iter()
        .flat_map(|ctor| ctor.fields.iter())
        .any(|field| sort_references_datatype(&field.sort, &datatype.name))
}

fn sort_references_datatype(sort: &Sort, name: &str) -> bool {
    match sort {
        Sort::Datatype(dt) => dt.name == name,
        Sort::Uninterpreted(n) => n == name,
        _ => false,
    }
}

/// Compute the chained-unary-selector depth of a scrutinee within the given
/// recursive datatype.
///
/// Walks down unary `App` nodes whose result sort references `datatype`,
/// counting the levels. The base `self` (a `Var`) has depth 0;
/// `cons_1(self)` has depth 1; `cons_1(cons_1(self))` has depth 2; and so on.
/// Non-`App` heads (constants, variables, `Ite`, etc.) terminate the walk.
fn scrutinee_selector_chain_depth(
    encoder: &AYEncoder,
    scrutinee: Term,
    datatype: &DatatypeSort,
) -> usize {
    let solver = encoder.solver();
    let mut depth = 0usize;
    let mut current = scrutinee;
    loop {
        // Stop when the term is no longer of the recursive datatype sort.
        let sort = solver.term_sort(current);
        if !sort_references_datatype(&sort, &datatype.name) {
            return depth;
        }
        match solver.term_kind(current) {
            TermKind::App { num_args: 1, .. } => {
                let children = solver.term_children(current);
                if children.len() == 1 {
                    depth = depth.saturating_add(1);
                    current = children[0];
                    continue;
                }
                return depth;
            }
            _ => return depth,
        }
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use ay_dpll::api::{DatatypeConstructor, DatatypeField, DatatypeSort, Sort};
    use trust_wp_core::logic::FieldRangeKind;

    use super::*;
    use crate::encoder::AYEncoder;

    fn list_datatype_with_u32_field() -> DatatypeSort {
        DatatypeSort {
            name: "List".to_string(),
            constructors: vec![
                DatatypeConstructor {
                    name: "Cons".to_string(),
                    fields: vec![
                        DatatypeField {
                            name: "list_cons_0".to_string(),
                            sort: Sort::Int,
                        },
                        DatatypeField {
                            name: "list_cons_1".to_string(),
                            sort: Sort::Uninterpreted("List".to_string()),
                        },
                    ],
                },
                DatatypeConstructor {
                    name: "Nil".to_string(),
                    fields: vec![],
                },
            ],
        }
    }

    #[test]
    fn datatype_is_recursive_detects_self_reference() {
        let list = list_datatype_with_u32_field();
        assert!(datatype_is_recursive(&list));
    }

    #[test]
    fn datatype_is_recursive_rejects_non_recursive_adt() {
        let pair = DatatypeSort {
            name: "Pair".to_string(),
            constructors: vec![DatatypeConstructor {
                name: "Pair".to_string(),
                fields: vec![
                    DatatypeField {
                        name: "fst".to_string(),
                        sort: Sort::Int,
                    },
                    DatatypeField {
                        name: "snd".to_string(),
                        sort: Sort::Int,
                    },
                ],
            }],
        };
        assert!(!datatype_is_recursive(&pair));
    }

    #[test]
    fn ground_field_range_skips_deep_recursive_scrutinee() {
        // Build an encoder with a recursive List datatype and a u32 field
        // range hint on Cons.0. Assert ground field-range constraints at
        // depth 0, 1, 2, 3 and check that depths > MAX_RECURSIVE_FIELD_RANGE_DEPTH
        // are skipped (no new solver assertion added).
        let mut encoder = AYEncoder::new_all();
        let dt = list_datatype_with_u32_field();
        encoder.ensure_datatype_declared(&dt);

        // Canonical declared form (after declaration the recursive field
        // sort becomes `Sort::Datatype(dt)`).
        let dt = encoder.canonical_declared_datatype(&dt);

        let mut ranges = HashMap::new();
        ranges.insert(
            "List".to_string(),
            vec![("Cons".to_string(), vec![(0, FieldRangeKind::Unsigned(32))])],
        );
        encoder.set_adt_field_ranges(ranges);

        let self_var = encoder
            .get_or_declare_var("self", Sort::Datatype(dt.clone()))
            .expect("declare self");
        let cons_1_self = encoder
            .solver_mut()
            .try_datatype_selector("list_cons_1", self_var, Sort::Datatype(dt.clone()))
            .expect("cons_1 selector");
        let cons_1_cons_1_self = encoder
            .solver_mut()
            .try_datatype_selector("list_cons_1", cons_1_self, Sort::Datatype(dt.clone()))
            .expect("cons_1 cons_1 selector");
        let cons_1_cubed = encoder
            .solver_mut()
            .try_datatype_selector(
                "list_cons_1",
                cons_1_cons_1_self,
                Sort::Datatype(dt.clone()),
            )
            .expect("cons_1^3 selector");

        assert_eq!(scrutinee_selector_chain_depth(&encoder, self_var, &dt), 0);
        assert_eq!(
            scrutinee_selector_chain_depth(&encoder, cons_1_self, &dt),
            1
        );
        assert_eq!(
            scrutinee_selector_chain_depth(&encoder, cons_1_cons_1_self, &dt),
            2
        );
        assert_eq!(
            scrutinee_selector_chain_depth(&encoder, cons_1_cubed, &dt),
            3
        );

        // Baseline assertion count before any range constraints.
        let before = encoder.solver().assertions().len();

        // Depth 0: should emit (within bound).
        encoder.assert_ground_field_range_constraints(self_var, &dt);
        let after_0 = encoder.solver().assertions().len();
        assert!(
            after_0 > before,
            "depth-0 scrutinee should emit a ground range constraint"
        );

        // Depth 1: should emit (== MAX_RECURSIVE_FIELD_RANGE_DEPTH).
        encoder.assert_ground_field_range_constraints(cons_1_self, &dt);
        let after_1 = encoder.solver().assertions().len();
        assert!(
            after_1 > after_0,
            "depth-1 scrutinee should emit a ground range constraint (within bound)"
        );

        // Depth 2: should be skipped (> MAX_RECURSIVE_FIELD_RANGE_DEPTH).
        encoder.assert_ground_field_range_constraints(cons_1_cons_1_self, &dt);
        assert_eq!(
            encoder.solver().assertions().len(),
            after_1,
            "depth-2 scrutinee on recursive ADT must NOT emit a fresh range axiom"
        );

        // Depth 3: same, skipped.
        encoder.assert_ground_field_range_constraints(cons_1_cubed, &dt);
        assert_eq!(
            encoder.solver().assertions().len(),
            after_1,
            "depth-3 scrutinee on recursive ADT must NOT emit a fresh range axiom"
        );
    }
}
