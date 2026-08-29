// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Datatype discriminant axiom encoding for enum match arms.
//!
//! Generates quantified axioms that relate datatype constructors to their
//! discriminant integer values. Supports explicit `#[repr]` discriminant
//! values via `AdtDecl` metadata, falling back to variant indices when
//! no metadata is available. (#2631)

use ay_dpll::api::{DatatypeSort, Sort};
use num_bigint::BigInt;

use super::super::AYEncoder;

impl AYEncoder {
    pub(crate) fn assert_datatype_discriminant_axioms(&mut self, datatype: &DatatypeSort) {
        // Single-constructor datatypes (structs, newtypes) have a fixed
        // discriminant of 0 that never needs quantified axioms. Skipping the
        // axiom avoids injecting a `forall` into the solver during bootstrap,
        // which would cause ay-dpll to return QuantifierUnhandled for unrelated
        // postconditions that happen to use the same datatype.
        if datatype.constructors.len() <= 1 {
            return;
        }

        let receiver_sort = Sort::Datatype(datatype.clone());
        let sort_tag = Self::method_sort_tag(&receiver_sort);
        let smt_name = format!("method_discriminant_1_{sort_tag}");
        let discr_decl = self.get_or_declare_method_func(&smt_name, &[receiver_sort], Sort::Int);
        let dedup_key = format!("datatype_discriminant_axioms::{}", datatype.name);
        if !self.mark_logic_fn_axiom_asserted(dedup_key) {
            return;
        }

        // Look up actual discriminant values from the AdtDecl (#2631).
        // For #[repr] enums, discriminant values may differ from variant indices.
        let adt_decl = self.adt_decl_for_name(&datatype.name).cloned();

        for (variant_idx, constructor) in datatype.constructors.iter().enumerate() {
            let discr_val = Self::datatype_discriminant_value(
                adt_decl.as_ref(),
                &constructor.name,
                variant_idx,
            );
            let tag = self.solver.int_const_bigint(&discr_val);
            if constructor.fields.is_empty() {
                // Recursive compat enums can reach this with constructor return
                // sorts that resolve to a synthesized alias rather than the
                // declared datatype name. Treat that as a skipped axiom, not a
                // solver panic.
                let Some(ctor_term) = self.axiom_datatype_constructor(
                    "datatype discriminant nullary",
                    datatype,
                    &constructor.name,
                    &[],
                ) else {
                    continue;
                };
                let discr_term = self.solver.apply(&discr_decl, &[ctor_term]);
                let eq = self.eq_term(discr_term, tag);
                self.assert_solver_term("datatype_discriminant/nullary", eq);
                continue;
            }

            // Payload-constructor discriminator axioms are optional proof fuel:
            // observed discriminant calls already get exact ground
            // tester-to-tag implications in `encode_int_method_uf`. Emitting a
            // global `forall payloads. discriminant(Ctor(payloads)) = tag`
            // leaves otherwise ground VCs with QuantifierUnhandled, including
            // PersistentArray::new's OptionInt::Some and Inner::Link context.
            // Keep nullary constructor equalities above, and weaken by skipping
            // only the quantified payload-constructor form.
            continue;
        }
    }

    /// Look up the discriminant value for a constructor, falling back to the
    /// variant index when no explicit value is registered.
    pub(in crate::encoder) fn datatype_discriminant_value(
        adt_decl: Option<&trust_wp_core::logic::AdtDecl>,
        constructor_name: &str,
        variant_idx: usize,
    ) -> BigInt {
        adt_decl
            .and_then(|decl| {
                decl.constructors
                    .iter()
                    .find(|c| c.smt_name == constructor_name)
                    .and_then(|c| c.discriminant_value.clone())
            })
            .unwrap_or_else(|| BigInt::from(variant_idx))
    }
}

#[cfg(test)]
mod tests {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, Term, TermKind};

    use super::*;

    fn assertion_has_forall(encoder: &AYEncoder, assertion: Term) -> bool {
        let solver = encoder.solver();
        let mut stack = vec![assertion];
        let mut seen = std::collections::HashSet::new();
        while let Some(term) = stack.pop() {
            if !seen.insert(term) {
                continue;
            }
            if matches!(solver.term_kind(term), TermKind::Forall) {
                return true;
            }
            stack.extend(solver.term_children(term));
        }
        false
    }

    #[test]
    fn discriminant_axioms_skip_payload_constructor_foralls() {
        let mut encoder = AYEncoder::new();
        let datatype = DatatypeSort {
            name: "Inner".to_string(),
            constructors: vec![
                DatatypeConstructor {
                    name: "Direct".to_string(),
                    fields: vec![DatatypeField {
                        name: "value".to_string(),
                        sort: Sort::seq(Sort::Int),
                    }],
                },
                DatatypeConstructor {
                    name: "Link".to_string(),
                    fields: vec![DatatypeField {
                        name: "id".to_string(),
                        sort: Sort::Int,
                    }],
                },
            ],
        };
        encoder.ensure_datatype_declared(&datatype);

        assert!(
            !encoder
                .solver()
                .assertions()
                .into_iter()
                .any(|assertion| assertion_has_forall(&encoder, assertion)),
            "datatype discriminator axioms must not introduce payload-constructor foralls"
        );
    }
}
