// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Demand-driven axiom family flags for `assert_standard_axioms`.
//!
//! Performs a single O(N) scan of the spec-function and logic-function
//! registries to determine which axiom families have declared symbols. The
//! solver tail uses these flags to skip axiom families whose symbols are
//! absent, avoiding unnecessary UF lookups, quantifier variable allocation,
//! and solver term construction.
//!
//! The scan replaces per-family O(N) `spec_func_decl_cloned()` + full
//! `logic_funcs_iter()` scans that previously happened inside each axiom
//! assertion method. For verification queries that don't use FMap, FSet,
//! Option, Result, or tuples (e.g., pure arithmetic, bitvector proofs), this
//! eliminates all axiom-family overhead in a single pass.
//!
//! Issue: #2674 Phase 5

use super::super::AYEncoder;

/// Which standard axiom families have declared symbols and need assertion.
///
/// All fields default to `false` (no demand). A field is set to `true` when
/// the single-pass scan finds at least one declared symbol for that family.
#[derive(Debug, Default)]
pub(crate) struct StandardAxiomDemand {
    /// FMap axioms: requires `fmap_insert` spec function.
    pub(crate) has_fmap: bool,

    /// FSet axioms: requires any of `fset_contains`, `fset_is_empty`,
    /// `fset_peek`, `fset_insert`, `fset_remove`.
    pub(crate) has_fset: bool,

    /// Mapping ground instances: requires any `mapping_*` spec function.
    pub(crate) has_mapping: bool,

    /// Option/Result axioms: requires any of `Some`, `None`, `Ok`, `Err`
    /// logic functions, or `is_some`, `spec_unwrap`, `is_ok` spec functions.
    pub(crate) has_option_result: bool,

    /// Tuple axioms: requires `__trust_wp_tuple*` or `__trust_wp_tuple_get_*`
    /// logic functions.
    pub(crate) has_tuples: bool,

    /// Unit singleton axioms: requires the unit sort type to have been
    /// declared (checked separately via `unit_sort()` usage).
    /// Set when any `__trust_wp_tuple*` function is present (tuples use
    /// unit for 0-element entries) or when unit_sort UF exists.
    pub(crate) has_unit: bool,

    /// Deep model axioms: requires `method_deep_model_1_i` logic function.
    pub(crate) has_deep_model: bool,

    /// Layout axioms: requires any `size_of_logic` or `align_of_logic`
    /// logic function placeholder.
    pub(crate) has_layout: bool,

    /// Trait postcondition axioms: requires both a `closure_postcondition_*`
    /// and `Default::default` logic function. We only track whether
    /// `Default::default` is present; the closure_postcondition check is
    /// already done by `closure_postcondition_flags()`.
    pub(crate) has_trait_postcondition: bool,

    /// Type invariant axioms: requires `method___trust_wp_invariant_*` logic
    /// function.
    pub(crate) has_type_invariant: bool,
}

impl StandardAxiomDemand {
    /// Returns `true` when no axiom family has demand.
    ///
    /// Used by the extended axiom-free probe (#2692) to determine whether an
    /// Inconclusive axiom-free result should trigger an extended probe (no
    /// axiom demand = pure arithmetic case) or fall through to the axiom path.
    pub(crate) fn is_empty(&self) -> bool {
        !self.has_fmap
            && !self.has_fset
            && !self.has_mapping
            && !self.has_option_result
            && !self.has_tuples
            && !self.has_unit
            && !self.has_deep_model
            && !self.has_layout
            && !self.has_trait_postcondition
            && !self.has_type_invariant
    }

    /// Returns `true` when Option/Result is the only demanded family.
    pub(crate) fn only_option_result(&self) -> bool {
        self.has_option_result
            && !self.has_fmap
            && !self.has_fset
            && !self.has_mapping
            && !self.has_tuples
            && !self.has_unit
            && !self.has_deep_model
            && !self.has_layout
            && !self.has_trait_postcondition
            && !self.has_type_invariant
    }
}

use std::sync::OnceLock;

/// Lazily compute the SMT-encoded prefix for `__trust_wp_tuple`.
fn smt_tuple_prefix() -> &'static str {
    static PREFIX: OnceLock<String> = OnceLock::new();
    PREFIX.get_or_init(|| {
        trust_wp_core::logic::logic_fn_smt_name(
            trust_wp_core::formula::internal::tuple_lowering::TUPLE_LOGIC_FN_PREFIX,
        )
    })
}

/// Lazily compute the SMT-encoded prefix for `__trust_wp_tuple_get_`.
fn smt_tuple_field_prefix() -> &'static str {
    static PREFIX: OnceLock<String> = OnceLock::new();
    PREFIX.get_or_init(|| {
        trust_wp_core::logic::logic_fn_smt_name(
            trust_wp_core::formula::internal::tuple_lowering::TUPLE_FIELD_LOGIC_FN_PREFIX,
        )
    })
}

/// SMT name prefix for `size_of_logic` placeholder UFs.
const SIZE_OF_LOGIC_PREFIX: &str = "logic_size__of__logic";

/// SMT name prefix for `align_of_logic` placeholder UFs.
const ALIGN_OF_LOGIC_PREFIX: &str = "logic_align__of__logic";

/// SMT name for `core::default::Default::default` logic function.
const DEFAULT_DEFAULT_SMT_NAME: &str = "logic_core_P__P_default_P__P_Default_P__P_default";

/// SMT name prefix for type invariant method UFs.
const TYPE_INVARIANT_SMT_PREFIX: &str = "method___trust_wp_invariant_";

impl AYEncoder {
    /// Count observed standard-library ground applications for a symbol.
    ///
    /// This is used by demand guards that need to distinguish declarations made
    /// by another built-in theory from actual goal-level use of that family.
    pub(crate) fn standard_ground_entry_count(&self, symbol: &str) -> usize {
        self.ground_pool
            .entries_for(symbol)
            .map_or(0, |entries| entries.len())
    }

    /// Single-pass scan of declared functions to determine which axiom families
    /// need assertion. (#2674 Phase 5)
    ///
    /// Scans both the logic-function and spec-function registries in one pass
    /// each. Each name is checked against prefix patterns for all axiom families
    /// simultaneously, amortizing the iteration cost.
    pub(crate) fn standard_axiom_demand(&self) -> StandardAxiomDemand {
        let mut demand = StandardAxiomDemand::default();

        // Scan spec functions (FMap, FSet, Option/Result testers/accessors).
        for name in self.spec_func_names_iter() {
            if !demand.has_fmap && name.starts_with("fmap_") {
                demand.has_fmap = true;
            }
            if !demand.has_fset && name.starts_with("fset_") {
                demand.has_fset = true;
            }
            if !demand.has_mapping && name.starts_with("mapping_") {
                demand.has_mapping = true;
            }
            if !demand.has_option_result {
                match name.as_str() {
                    "is_some"
                    | "spec_unwrap"
                    | "is_ok"
                    | "result_err_error"
                    | "__trust_wp_is_option"
                    | "__trust_wp_is_result" => {
                        demand.has_option_result = true;
                    }
                    _ => {}
                }
            }

            // Early exit if all spec-function families are satisfied.
            if demand.has_fmap && demand.has_fset && demand.has_mapping && demand.has_option_result
            {
                break;
            }
        }

        // Scan logic functions (tuples, deep_model, layout, Option/Result
        // constructors, Default::default, type invariants).
        for name in self.logic_func_names_iter() {
            if !demand.has_tuples
                && (name.starts_with(smt_tuple_prefix())
                    || name.starts_with(smt_tuple_field_prefix()))
            {
                demand.has_tuples = true;
                // Tuples imply unit usage for 0-element entries.
                demand.has_unit = true;
            }
            if !demand.has_deep_model && name == "method_deep_model_1_i" {
                demand.has_deep_model = true;
            }
            if !demand.has_layout
                && (name.starts_with(SIZE_OF_LOGIC_PREFIX)
                    || name.starts_with(ALIGN_OF_LOGIC_PREFIX))
            {
                demand.has_layout = true;
            }
            if !demand.has_option_result {
                // Check for Option/Result constructor logic functions.
                // These are encoded as `logic_Some`, `logic_None`, `logic_Ok`, `logic_Err`
                // (plus placeholder variants like `logic_Some__placeholder_*`).
                if name.starts_with("logic_Some")
                    || name.starts_with("logic_None")
                    || name.starts_with("logic_Ok")
                    || name.starts_with("logic_Err")
                {
                    demand.has_option_result = true;
                }
            }
            if !demand.has_trait_postcondition && name.starts_with(DEFAULT_DEFAULT_SMT_NAME) {
                demand.has_trait_postcondition = true;
            }
            if !demand.has_type_invariant && name.starts_with(TYPE_INVARIANT_SMT_PREFIX) {
                demand.has_type_invariant = true;
            }

            // Early exit if all logic-function families are satisfied.
            if demand.has_tuples
                && demand.has_deep_model
                && demand.has_layout
                && demand.has_option_result
                && demand.has_trait_postcondition
                && demand.has_type_invariant
            {
                break;
            }
        }

        if !demand.has_trait_postcondition
            && self.var_term("core::default::Default::default").is_some()
        {
            demand.has_trait_postcondition = true;
        }

        demand
    }
}

#[cfg(test)]
mod tests {
    use ay_dpll::api::Sort;

    use crate::AYEncoder;

    #[test]
    fn test_empty_encoder_no_demand() {
        let encoder = AYEncoder::new();
        let demand = encoder.standard_axiom_demand();
        assert!(
            !demand.has_fmap,
            "fresh encoder should not demand FMap axioms"
        );
        assert!(
            !demand.has_fset,
            "fresh encoder should not demand FSet axioms"
        );
        assert!(
            !demand.has_mapping,
            "fresh encoder should not demand Mapping ground instances"
        );
        assert!(
            !demand.has_option_result,
            "fresh encoder should not demand Option/Result axioms"
        );
        assert!(
            !demand.has_tuples,
            "fresh encoder should not demand tuple axioms"
        );
        assert!(
            !demand.has_unit,
            "fresh encoder should not demand unit axioms"
        );
        assert!(
            !demand.has_deep_model,
            "fresh encoder should not demand deep_model axioms"
        );
        assert!(
            !demand.has_layout,
            "fresh encoder should not demand layout axioms"
        );
        assert!(
            !demand.has_trait_postcondition,
            "fresh encoder should not demand trait postcondition axioms"
        );
        assert!(
            !demand.has_type_invariant,
            "fresh encoder should not demand type invariant axioms"
        );
    }

    #[test]
    fn test_fmap_spec_func_triggers_demand() {
        let mut encoder = AYEncoder::new();
        encoder.get_or_declare_spec_func(
            "fmap_insert",
            &[Sort::Int, Sort::Int, Sort::Int],
            Sort::Int,
        );
        let demand = encoder.standard_axiom_demand();
        assert!(demand.has_fmap, "fmap_insert should trigger FMap demand");
        assert!(
            !demand.has_fset,
            "fmap_insert should not trigger FSet demand"
        );
    }

    #[test]
    fn test_fset_spec_func_triggers_demand() {
        let mut encoder = AYEncoder::new();
        encoder.get_or_declare_spec_func("fset_contains", &[Sort::Int, Sort::Int], Sort::Bool);
        let demand = encoder.standard_axiom_demand();
        assert!(demand.has_fset, "fset_contains should trigger FSet demand");
        assert!(
            !demand.has_fmap,
            "fset_contains should not trigger FMap demand"
        );
    }

    #[test]
    fn test_mapping_spec_func_triggers_demand() {
        let mut encoder = AYEncoder::new();
        encoder.get_or_declare_spec_func("mapping_get", &[Sort::Int, Sort::Int], Sort::Int);
        let demand = encoder.standard_axiom_demand();
        assert!(
            demand.has_mapping,
            "mapping_get should trigger Mapping demand"
        );
        assert!(
            !demand.has_fmap,
            "mapping_get should not trigger FMap demand"
        );
        assert!(
            !demand.has_fset,
            "mapping_get should not trigger FSet demand"
        );
    }

    #[test]
    fn test_option_spec_func_triggers_demand() {
        let mut encoder = AYEncoder::new();
        encoder.get_or_declare_spec_func("is_some", &[Sort::Int], Sort::Bool);
        let demand = encoder.standard_axiom_demand();
        assert!(
            demand.has_option_result,
            "is_some should trigger Option/Result demand"
        );
    }

    #[test]
    fn test_option_constructor_logic_func_triggers_demand() {
        let mut encoder = AYEncoder::new();
        encoder.get_or_declare_logic_func("logic_Some", &[Sort::Int], Sort::Int);
        let demand = encoder.standard_axiom_demand();
        assert!(
            demand.has_option_result,
            "logic_Some should trigger Option/Result demand"
        );
    }

    #[test]
    fn test_tuple_logic_func_triggers_demand() {
        let mut encoder = AYEncoder::new();
        // The SMT name for __trust_wp_tuple2 is logic___trust_wp__tuple2
        let smt_name = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_tuple2");
        encoder.get_or_declare_logic_func(&smt_name, &[Sort::Int, Sort::Int], Sort::Int);
        let demand = encoder.standard_axiom_demand();
        assert!(
            demand.has_tuples,
            "tuple constructor should trigger tuple demand"
        );
        assert!(
            demand.has_unit,
            "tuple constructor should trigger unit demand"
        );
    }

    #[test]
    fn test_deep_model_triggers_demand() {
        let mut encoder = AYEncoder::new();
        encoder.get_or_declare_logic_func("method_deep_model_1_i", &[Sort::Int], Sort::Int);
        let demand = encoder.standard_axiom_demand();
        assert!(
            demand.has_deep_model,
            "deep_model should trigger deep_model demand"
        );
    }

    #[test]
    fn test_layout_triggers_demand() {
        let mut encoder = AYEncoder::new();
        let smt_name = trust_wp_core::logic::logic_fn_smt_name("size_of_logic");
        encoder.get_or_declare_logic_func(&smt_name, &[], Sort::Int);
        let demand = encoder.standard_axiom_demand();
        assert!(
            demand.has_layout,
            "size_of_logic should trigger layout demand"
        );
    }

    #[test]
    fn test_default_default_triggers_trait_postcondition() {
        let mut encoder = AYEncoder::new();
        encoder.get_or_declare_logic_func(super::DEFAULT_DEFAULT_SMT_NAME, &[], Sort::Int);
        let demand = encoder.standard_axiom_demand();
        assert!(
            demand.has_trait_postcondition,
            "Default::default should trigger trait postcondition demand"
        );
    }

    /// Placeholder-suffixed Default::default declarations (from production
    /// encoding) should also trigger trait postcondition demand. (#2670)
    #[test]
    fn test_default_default_placeholder_triggers_trait_postcondition() {
        let mut encoder = AYEncoder::new();
        // Production encoding creates placeholder names like:
        // logic_core_P__P_default_P__P_Default_P__P_default__placeholder_nullary__ret_i
        let placeholder_name = format!(
            "{}__placeholder_nullary__ret_i",
            super::DEFAULT_DEFAULT_SMT_NAME
        );
        encoder.get_or_declare_logic_func(&placeholder_name, &[], Sort::Int);
        let demand = encoder.standard_axiom_demand();
        assert!(
            demand.has_trait_postcondition,
            "Default::default placeholder should trigger trait postcondition demand (#2670)"
        );
    }

    /// Generated derive postconditions encode `Default::default` as a receiver
    /// variable and do not always declare a separate logic function.
    #[test]
    fn test_default_default_var_receiver_triggers_trait_postcondition() {
        let mut encoder = AYEncoder::new();
        encoder
            .get_or_declare_var("core::default::Default::default", Sort::Int)
            .unwrap();
        let demand = encoder.standard_axiom_demand();
        assert!(
            demand.has_trait_postcondition,
            "Default::default receiver variable should trigger trait postcondition demand"
        );
    }

    #[test]
    fn test_type_invariant_triggers_demand() {
        let mut encoder = AYEncoder::new();
        encoder.get_or_declare_logic_func(
            "method___trust_wp_invariant_TestType_1_i",
            &[Sort::Int],
            Sort::Bool,
        );
        let demand = encoder.standard_axiom_demand();
        assert!(
            demand.has_type_invariant,
            "type invariant UF should trigger type invariant demand"
        );
    }

    #[test]
    fn test_all_families_can_be_triggered() {
        let mut encoder = AYEncoder::new();

        // Trigger all families.
        encoder.get_or_declare_spec_func(
            "fmap_insert",
            &[Sort::Int, Sort::Int, Sort::Int],
            Sort::Int,
        );
        encoder.get_or_declare_spec_func("fset_contains", &[Sort::Int, Sort::Int], Sort::Bool);
        encoder.get_or_declare_spec_func("mapping_get", &[Sort::Int, Sort::Int], Sort::Int);
        encoder.get_or_declare_spec_func("is_some", &[Sort::Int], Sort::Bool);
        let smt_tuple = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_tuple2");
        encoder.get_or_declare_logic_func(&smt_tuple, &[Sort::Int, Sort::Int], Sort::Int);
        encoder.get_or_declare_logic_func("method_deep_model_1_i", &[Sort::Int], Sort::Int);
        let smt_size = trust_wp_core::logic::logic_fn_smt_name("size_of_logic");
        encoder.get_or_declare_logic_func(&smt_size, &[], Sort::Int);
        encoder.get_or_declare_logic_func(super::DEFAULT_DEFAULT_SMT_NAME, &[], Sort::Int);
        encoder.get_or_declare_logic_func(
            "method___trust_wp_invariant_T_1_i",
            &[Sort::Int],
            Sort::Bool,
        );

        let demand = encoder.standard_axiom_demand();
        assert!(demand.has_fmap);
        assert!(demand.has_fset);
        assert!(demand.has_mapping);
        assert!(demand.has_option_result);
        assert!(demand.has_tuples);
        assert!(demand.has_unit);
        assert!(demand.has_deep_model);
        assert!(demand.has_layout);
        assert!(demand.has_trait_postcondition);
        assert!(demand.has_type_invariant);
    }

    #[test]
    fn test_is_empty_on_fresh_encoder() {
        let encoder = AYEncoder::new();
        let demand = encoder.standard_axiom_demand();
        assert!(demand.is_empty(), "fresh encoder demand should be empty");
    }

    #[test]
    fn test_is_empty_false_when_fmap_declared() {
        let mut encoder = AYEncoder::new();
        encoder.get_or_declare_spec_func(
            "fmap_insert",
            &[Sort::Int, Sort::Int, Sort::Int],
            Sort::Int,
        );
        let demand = encoder.standard_axiom_demand();
        assert!(!demand.is_empty(), "demand should not be empty with FMap");
    }

    #[test]
    fn test_is_empty_false_when_all_families_present() {
        let mut encoder = AYEncoder::new();
        encoder.get_or_declare_spec_func(
            "fmap_insert",
            &[Sort::Int, Sort::Int, Sort::Int],
            Sort::Int,
        );
        encoder.get_or_declare_spec_func("fset_contains", &[Sort::Int, Sort::Int], Sort::Bool);
        encoder.get_or_declare_spec_func("mapping_get", &[Sort::Int, Sort::Int], Sort::Int);
        encoder.get_or_declare_spec_func("is_some", &[Sort::Int], Sort::Bool);
        let smt_tuple = trust_wp_core::logic::logic_fn_smt_name("__trust_wp_tuple2");
        encoder.get_or_declare_logic_func(&smt_tuple, &[Sort::Int, Sort::Int], Sort::Int);
        encoder.get_or_declare_logic_func("method_deep_model_1_i", &[Sort::Int], Sort::Int);
        let smt_size = trust_wp_core::logic::logic_fn_smt_name("size_of_logic");
        encoder.get_or_declare_logic_func(&smt_size, &[], Sort::Int);
        encoder.get_or_declare_logic_func(super::DEFAULT_DEFAULT_SMT_NAME, &[], Sort::Int);
        encoder.get_or_declare_logic_func(
            "method___trust_wp_invariant_T_1_i",
            &[Sort::Int],
            Sort::Bool,
        );
        let demand = encoder.standard_axiom_demand();
        assert!(
            !demand.is_empty(),
            "demand should not be empty with all families"
        );
    }
}
