// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::{HashMap, HashSet};

use ay_dpll::api::{DatatypeSort, FuncDecl};

use crate::encoder::match_enc::logical_constructor_alias_for_datatype;

/// Function and datatype declaration registry (#840).
///
/// Groups the four declaration-tracking fields: logic function declarations
/// (`#[logic]` attribute), axiom dedup tracking, algebraic datatype declarations
/// (Option, Result, etc.), and spec function declarations (testers, accessors, FSet ops).
/// These are used across `axioms.rs`, `logic_fn.rs`, `match_enc.rs`, and `sort_context.rs`.
pub(crate) struct DeclarationState {
    /// User-defined logic functions (from `#[logic]` attribute)
    logic_funcs: HashMap<String, FuncDecl>,
    /// Logic functions with asserted axioms (by SMT name).
    /// Prevents re-asserting defining axioms for already-registered functions.
    logic_fn_axioms: HashSet<String>,
    /// Datatypes declared for native constructor/tester/selector operations.
    declared_datatypes: HashMap<String, DatatypeSort>,
    /// Reverse index: constructor short name → datatype name(s).
    /// Updated at `insert_datatype` time for O(1) constructor lookup. (#1294)
    /// Multiple datatypes can share constructor names (e.g., "Ok" in both
    /// OwnResult and OtherResult), so we store a Vec of datatype names.
    constructor_to_datatype: HashMap<String, Vec<String>>,
    /// Whether any declared datatype uses a synthesized constructor-family name
    /// such as `Adt_Cons_Nil`.
    has_synthesized_datatype: bool,
    /// Uninterpreted spec functions: constructor testers, accessors, and `FSet` ops.
    spec_functions: HashMap<String, FuncDecl>,
    /// Type invariant methods with trivially-true bodies (#1296).
    /// When `inv(x) = true` for all `x`, we skip the quantified axiom and
    /// inline `true` at call sites to avoid ay E-matching bottlenecks.
    trivial_true_invariants: HashSet<String>,
    /// Total number of type invariants registered (trivial + non-trivial).
    /// Used by `all_type_invariants_trivially_true` to verify that ALL
    /// registered invariants are trivial, not just that some are. (#1296)
    total_type_invariant_count: usize,
}

impl DeclarationState {
    pub(crate) fn new() -> Self {
        Self {
            logic_funcs: HashMap::new(),
            logic_fn_axioms: HashSet::new(),
            declared_datatypes: HashMap::new(),
            constructor_to_datatype: HashMap::new(),
            has_synthesized_datatype: false,
            spec_functions: HashMap::new(),
            trivial_true_invariants: HashSet::new(),
            total_type_invariant_count: 0,
        }
    }

    // --- Logic function registry ---

    /// Look up a logic function declaration by SMT name.
    pub(crate) fn get_logic_func(&self, name: &str) -> Option<&FuncDecl> {
        self.logic_funcs.get(name)
    }

    /// Check whether a logic function with the given SMT name exists.
    pub(crate) fn has_logic_func(&self, name: &str) -> bool {
        self.logic_funcs.contains_key(name)
    }

    /// Register a logic function declaration.
    pub(crate) fn insert_logic_func(&mut self, name: String, decl: FuncDecl) {
        self.logic_funcs.insert(name, decl);
    }

    /// Iterate over all logic function names (for debug/discovery).
    pub(crate) fn logic_func_names(&self) -> impl Iterator<Item = &String> {
        self.logic_funcs.keys()
    }

    /// Iterate over all logic function entries.
    pub(crate) fn logic_funcs_iter(&self) -> impl Iterator<Item = (&String, &FuncDecl)> {
        self.logic_funcs.iter()
    }

    /// Read-only reference to the logic function map.
    ///
    /// Used by `param_sort_infer` which takes `&HashMap` for cross-function
    /// Seq parameter inference. Prefer specific methods for new code.
    pub(crate) fn logic_funcs_ref(&self) -> &HashMap<String, FuncDecl> {
        &self.logic_funcs
    }

    // --- Axiom dedup tracking ---

    /// Check whether the defining axiom for a logic function has been asserted.
    pub(crate) fn has_logic_fn_axiom(&self, name: &str) -> bool {
        self.logic_fn_axioms.contains(name)
    }

    /// Mark a logic function axiom as asserted. Returns `true` if newly inserted.
    pub(crate) fn mark_logic_fn_axiom(&mut self, name: String) -> bool {
        self.logic_fn_axioms.insert(name)
    }

    // --- Spec function registry ---

    /// Look up a spec function (constructor testers, accessors, FSet ops).
    pub(crate) fn get_spec_func(&self, name: &str) -> Option<&FuncDecl> {
        self.spec_functions.get(name)
    }

    /// Register a spec function declaration.
    pub(crate) fn insert_spec_func(&mut self, name: String, decl: FuncDecl) {
        self.spec_functions.insert(name, decl);
    }

    /// Iterate over all spec function names (for debug/discovery).
    pub(crate) fn spec_func_names(&self) -> impl Iterator<Item = &String> {
        self.spec_functions.keys()
    }

    /// Check whether a spec function exists.
    #[cfg(test)]
    pub(crate) fn has_spec_func(&self, name: &str) -> bool {
        self.spec_functions.contains_key(name)
    }

    /// Whether any axiom-relevant declarations exist in the registry.
    ///
    /// Returns `true` when either logic functions, spec functions, or datatypes
    /// have been declared during encoding. When `false`, the encoder contains
    /// only raw SMT variables with no UF symbols, meaning all axiom assertion
    /// families (closure, tuple, option/result, fmap, fset, deep_model, layout,
    /// and ground pool) are guaranteed to be no-ops. This enables callers to
    /// skip the entire `assert_standard_axioms` call for pure arithmetic
    /// obligations. (#2674)
    pub(crate) fn has_any_axiom_relevant_symbols(&self) -> bool {
        !self.logic_funcs.is_empty()
            || !self.spec_functions.is_empty()
            || !self.declared_datatypes.is_empty()
    }

    // --- Datatype registry ---

    /// Look up a declared datatype by name.
    pub(crate) fn get_datatype(&self, name: &str) -> Option<&DatatypeSort> {
        self.declared_datatypes.get(name)
    }

    /// Check whether a datatype has been declared.
    pub(crate) fn has_datatype(&self, name: &str) -> bool {
        self.declared_datatypes.contains_key(name)
    }

    /// Register a declared datatype and populate the constructor reverse index.
    pub(crate) fn insert_datatype(&mut self, name: String, dt: DatatypeSort) {
        fn push_constructor_alias(
            index: &mut HashMap<String, Vec<String>>,
            ctor_name: String,
            dt_name: &str,
        ) {
            let datatypes = index.entry(ctor_name).or_default();
            if !datatypes.iter().any(|existing| existing == dt_name) {
                datatypes.push(dt_name.to_string());
            }
        }

        if name.starts_with("Adt_") || dt.name.starts_with("Adt_") {
            self.has_synthesized_datatype = true;
        }
        for ctor in &dt.constructors {
            push_constructor_alias(&mut self.constructor_to_datatype, ctor.name.clone(), &name);
            if let Some(logical) = logical_constructor_alias_for_datatype(&name, &ctor.name) {
                push_constructor_alias(
                    &mut self.constructor_to_datatype,
                    logical.to_string(),
                    &name,
                );
            }
        }
        self.declared_datatypes.insert(name, dt);
    }

    /// Whether any synthesized `Adt_*` datatype has been registered.
    pub(crate) fn has_synthesized_datatype(&self) -> bool {
        self.has_synthesized_datatype
    }

    /// O(1) reverse lookup: constructor short name → candidate datatypes. (#1294)
    ///
    /// Returns an iterator over datatypes that have a constructor with the
    /// given short name. Most constructors are unique (1 candidate); shared
    /// names like "Ok" may yield multiple candidates for caller disambiguation.
    pub(crate) fn datatypes_for_constructor(
        &self,
        short_name: &str,
    ) -> impl Iterator<Item = &DatatypeSort> {
        self.constructor_to_datatype
            .get(short_name)
            .into_iter()
            .flat_map(|names| names.iter())
            .filter_map(|dt_name| self.declared_datatypes.get(dt_name))
    }

    /// Iterate over all declared datatypes.
    pub(crate) fn datatypes_iter(&self) -> impl Iterator<Item = &DatatypeSort> {
        self.declared_datatypes.values()
    }

    /// Whether any non-builtin (custom) datatypes have been declared.
    ///
    /// Returns `true` when the declared datatypes include types beyond the
    /// standard `OptionInt` and `ResultIntInt` builtins. Custom datatypes
    /// (user-defined structs/enums, closure environments, tuples, etc.)
    /// require `Logic::All` for ay's auto-theory detection — `AUFLIA`/`UFLIA`
    /// lack native datatype theory support. (#1944)
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn has_custom_datatypes(&self) -> bool {
        self.declared_datatypes
            .keys()
            .any(|name| !matches!(name.as_str(), "OptionInt" | "ResultIntInt"))
    }

    // --- Type invariant tracking ---

    /// Check whether a specific type invariant is trivially true.
    pub(crate) fn is_trivial_invariant(&self, name: &str) -> bool {
        self.trivial_true_invariants.contains(name)
    }

    /// Register a type invariant as trivially true.
    pub(crate) fn register_trivial_invariant(&mut self, name: String) {
        self.trivial_true_invariants.insert(name);
    }

    /// Check whether ALL registered type invariants are trivially true.
    pub(crate) fn all_type_invariants_trivially_true(&self) -> bool {
        !self.trivial_true_invariants.is_empty()
            && self.trivial_true_invariants.len() == self.total_type_invariant_count
    }

    /// Increment the total type invariant count.
    pub(crate) fn increment_type_invariant_count(&mut self) {
        self.total_type_invariant_count += 1;
    }

    // --- Snapshot/restore for obligation slice isolation (#2618) ---

    /// Snapshot the logic function axiom dedup set.
    pub(crate) fn logic_fn_axiom_snapshot(&self) -> HashSet<String> {
        self.logic_fn_axioms.clone()
    }

    /// Restore the logic function axiom dedup set from a snapshot.
    pub(crate) fn restore_logic_fn_axioms(&mut self, snapshot: HashSet<String>) {
        self.logic_fn_axioms = snapshot;
    }

    // --- Test-only accessors ---

    /// Read-only access to spec_functions for test assertions.
    #[cfg(test)]
    pub(crate) fn spec_functions_ref(&self) -> &HashMap<String, FuncDecl> {
        &self.spec_functions
    }

    /// Number of registered trivial invariants.
    #[cfg(test)]
    pub(crate) fn trivial_invariant_count(&self) -> usize {
        self.trivial_true_invariants.len()
    }

    /// Whether no trivial invariants have been registered.
    #[cfg(test)]
    pub(crate) fn trivial_invariants_is_empty(&self) -> bool {
        self.trivial_true_invariants.is_empty()
    }

    /// Number of declared datatypes.
    #[cfg(test)]
    pub(crate) fn datatype_count(&self) -> usize {
        self.declared_datatypes.len()
    }

    /// Whether no datatypes have been declared.
    #[cfg(test)]
    pub(crate) fn datatypes_is_empty(&self) -> bool {
        self.declared_datatypes.is_empty()
    }

    /// Iterator over declared datatype names.
    #[cfg(test)]
    pub(crate) fn datatype_names(&self) -> impl Iterator<Item = &String> {
        self.declared_datatypes.keys()
    }

    /// Whether no spec functions have been declared.
    #[cfg(test)]
    pub(crate) fn spec_funcs_is_empty(&self) -> bool {
        self.spec_functions.is_empty()
    }

    /// Total number of type invariant registrations (including non-trivial).
    #[cfg(test)]
    pub(crate) fn type_invariant_count(&self) -> usize {
        self.total_type_invariant_count
    }

    /// Number of registered logic functions.
    #[cfg(test)]
    pub(crate) fn logic_func_count(&self) -> usize {
        self.logic_funcs.len()
    }
}

#[cfg(test)]
mod tests {
    use ay_dpll::api::{DatatypeConstructor, DatatypeField, Logic, Sort};

    use super::*;

    // ── initialization ──

    #[test]
    fn test_new_declaration_state_is_empty() {
        let state = DeclarationState::new();
        assert_eq!(state.logic_func_count(), 0);
        assert!(state.datatypes_is_empty());
        assert!(state.spec_funcs_is_empty());
        assert!(state.trivial_invariants_is_empty());
        assert_eq!(state.type_invariant_count(), 0);
    }

    // ── logic function registry ──

    #[test]
    fn test_insert_and_get_logic_func() {
        let mut state = DeclarationState::new();
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let decl = solver.declare_fun("logic_f", &[Sort::Int], Sort::Int);
        state.insert_logic_func("logic_f".to_string(), decl);

        assert!(state.has_logic_func("logic_f"));
        assert!(!state.has_logic_func("logic_g"));
        assert!(state.get_logic_func("logic_f").is_some());
        assert!(state.get_logic_func("logic_g").is_none());
        assert_eq!(state.logic_func_count(), 1);
    }

    #[test]
    fn test_logic_func_names_iteration() {
        let mut state = DeclarationState::new();
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let decl_f = solver.declare_fun("logic_f", &[Sort::Int], Sort::Int);
        let decl_g = solver.declare_fun("logic_g", &[Sort::Bool], Sort::Bool);
        state.insert_logic_func("logic_f".to_string(), decl_f);
        state.insert_logic_func("logic_g".to_string(), decl_g);

        let names: HashSet<&String> = state.logic_func_names().collect();
        assert_eq!(names.len(), 2);
        assert!(names.iter().any(|n| n.as_str() == "logic_f"));
        assert!(names.iter().any(|n| n.as_str() == "logic_g"));
    }

    #[test]
    fn test_logic_funcs_iter_returns_all_entries() {
        let mut state = DeclarationState::new();
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let decl = solver.declare_fun("logic_f", &[Sort::Int], Sort::Bool);
        state.insert_logic_func("logic_f".to_string(), decl);

        let entries: Vec<_> = state.logic_funcs_iter().collect();
        assert_eq!(entries.len(), 1);
        assert_eq!(entries[0].0, "logic_f");
    }

    #[test]
    fn test_logic_funcs_ref_returns_map() {
        let mut state = DeclarationState::new();
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let decl = solver.declare_fun("logic_f", &[Sort::Int], Sort::Int);
        state.insert_logic_func("logic_f".to_string(), decl);

        let map = state.logic_funcs_ref();
        assert_eq!(map.len(), 1);
        assert!(map.contains_key("logic_f"));
    }

    // ── axiom dedup tracking ──

    #[test]
    fn test_mark_logic_fn_axiom_dedup() {
        let mut state = DeclarationState::new();
        assert!(!state.has_logic_fn_axiom("axiom_f"));

        let newly_inserted = state.mark_logic_fn_axiom("axiom_f".to_string());
        assert!(newly_inserted);
        assert!(state.has_logic_fn_axiom("axiom_f"));

        // Second mark returns false (already present)
        let second = state.mark_logic_fn_axiom("axiom_f".to_string());
        assert!(!second);
    }

    #[test]
    fn test_logic_fn_axiom_snapshot_and_restore() {
        let mut state = DeclarationState::new();
        state.mark_logic_fn_axiom("axiom_a".to_string());
        state.mark_logic_fn_axiom("axiom_b".to_string());

        let snapshot = state.logic_fn_axiom_snapshot();
        assert_eq!(snapshot.len(), 2);

        // Add more axioms after snapshot
        state.mark_logic_fn_axiom("axiom_c".to_string());
        assert!(state.has_logic_fn_axiom("axiom_c"));

        // Restore removes axiom_c
        state.restore_logic_fn_axioms(snapshot);
        assert!(state.has_logic_fn_axiom("axiom_a"));
        assert!(state.has_logic_fn_axiom("axiom_b"));
        assert!(!state.has_logic_fn_axiom("axiom_c"));
    }

    // ── spec function registry ──

    #[test]
    fn test_insert_and_get_spec_func() {
        let mut state = DeclarationState::new();
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let decl = solver.declare_fun("is_Some", &[Sort::Int], Sort::Bool);
        state.insert_spec_func("is_Some".to_string(), decl);

        assert!(state.has_spec_func("is_Some"));
        assert!(state.get_spec_func("is_Some").is_some());
        assert!(!state.has_spec_func("is_None"));
        assert!(!state.spec_funcs_is_empty());
    }

    #[test]
    fn test_spec_func_names_iteration() {
        let mut state = DeclarationState::new();
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        state.insert_spec_func(
            "is_Some".to_string(),
            solver.declare_fun("is_Some", &[Sort::Int], Sort::Bool),
        );
        state.insert_spec_func(
            "get_value".to_string(),
            solver.declare_fun("get_value", &[Sort::Int], Sort::Int),
        );

        let names: HashSet<&String> = state.spec_func_names().collect();
        assert_eq!(names.len(), 2);
    }

    // ── datatype registry ──

    #[test]
    fn test_insert_and_get_datatype() {
        let mut state = DeclarationState::new();
        let dt = DatatypeSort {
            name: "OptionInt".to_string(),
            constructors: vec![
                DatatypeConstructor {
                    name: "Some".to_string(),
                    fields: vec![DatatypeField {
                        name: "option_some_value".to_string(),
                        sort: Sort::Int,
                    }],
                },
                DatatypeConstructor {
                    name: "None".to_string(),
                    fields: vec![],
                },
            ],
        };
        state.insert_datatype("OptionInt".to_string(), dt);

        assert!(state.has_datatype("OptionInt"));
        assert!(!state.has_datatype("ResultIntInt"));
        assert_eq!(state.datatype_count(), 1);
        assert!(!state.datatypes_is_empty());

        let retrieved = state.get_datatype("OptionInt").unwrap();
        assert_eq!(retrieved.constructors.len(), 2);
    }

    #[test]
    fn test_constructor_reverse_index() {
        let mut state = DeclarationState::new();
        let dt = DatatypeSort {
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
        state.insert_datatype("OwnResult".to_string(), dt);

        // "Ok" constructor maps to "OwnResult"
        let dts: Vec<_> = state.datatypes_for_constructor("Ok").collect();
        assert_eq!(dts.len(), 1);
        assert_eq!(dts[0].name, "OwnResult");

        // Unknown constructor returns empty
        let empty: Vec<_> = state.datatypes_for_constructor("Unknown").collect();
        assert!(empty.is_empty());
    }

    #[test]
    fn test_shared_constructor_names_across_datatypes() {
        let mut state = DeclarationState::new();
        let dt1 = DatatypeSort {
            name: "Result_A".to_string(),
            constructors: vec![DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "a_ok".to_string(),
                    sort: Sort::Int,
                }],
            }],
        };
        let dt2 = DatatypeSort {
            name: "Result_B".to_string(),
            constructors: vec![DatatypeConstructor {
                name: "Ok".to_string(),
                fields: vec![DatatypeField {
                    name: "b_ok".to_string(),
                    sort: Sort::Bool,
                }],
            }],
        };
        state.insert_datatype("Result_A".to_string(), dt1);
        state.insert_datatype("Result_B".to_string(), dt2);

        // "Ok" should map to both datatypes
        let dts: Vec<_> = state.datatypes_for_constructor("Ok").collect();
        assert_eq!(dts.len(), 2);
        let dt_names: HashSet<_> = dts.iter().map(|d| d.name.as_str()).collect();
        assert!(dt_names.contains("Result_A"));
        assert!(dt_names.contains("Result_B"));
    }

    #[test]
    fn test_has_custom_datatypes() {
        let mut state = DeclarationState::new();
        assert!(!state.has_custom_datatypes());

        // Adding only builtins should not trigger custom
        let option_int = DatatypeSort {
            name: "OptionInt".to_string(),
            constructors: vec![],
        };
        state.insert_datatype("OptionInt".to_string(), option_int);
        assert!(!state.has_custom_datatypes());

        let result_int = DatatypeSort {
            name: "ResultIntInt".to_string(),
            constructors: vec![],
        };
        state.insert_datatype("ResultIntInt".to_string(), result_int);
        assert!(!state.has_custom_datatypes());

        // Adding a custom datatype triggers the flag
        let custom = DatatypeSort {
            name: "MyEnum".to_string(),
            constructors: vec![],
        };
        state.insert_datatype("MyEnum".to_string(), custom);
        assert!(state.has_custom_datatypes());
    }

    #[test]
    fn test_datatypes_iter() {
        let mut state = DeclarationState::new();
        let dt = DatatypeSort {
            name: "Foo".to_string(),
            constructors: vec![],
        };
        state.insert_datatype("Foo".to_string(), dt);

        let all: Vec<_> = state.datatypes_iter().collect();
        assert_eq!(all.len(), 1);
        assert_eq!(all[0].name, "Foo");
    }

    // ── type invariant tracking ──

    #[test]
    fn test_trivial_invariant_registration() {
        let mut state = DeclarationState::new();
        assert!(!state.is_trivial_invariant("inv_Foo"));
        assert!(state.trivial_invariants_is_empty());

        state.register_trivial_invariant("inv_Foo".to_string());
        assert!(state.is_trivial_invariant("inv_Foo"));
        assert!(!state.is_trivial_invariant("inv_Bar"));
        assert_eq!(state.trivial_invariant_count(), 1);
    }

    #[test]
    fn test_all_type_invariants_trivially_true() {
        let mut state = DeclarationState::new();

        // No invariants registered => false (empty set)
        assert!(!state.all_type_invariants_trivially_true());

        // Register one invariant as trivial, but total count is still 0
        state.register_trivial_invariant("inv_A".to_string());
        // Without incrementing count, trivial count (1) != total count (0)
        assert!(!state.all_type_invariants_trivially_true());

        // Now increment count to match
        state.increment_type_invariant_count();
        assert!(state.all_type_invariants_trivially_true());

        // Register a non-trivial invariant (increment count but don't register as trivial)
        state.increment_type_invariant_count();
        assert!(!state.all_type_invariants_trivially_true());
    }

    #[test]
    fn test_increment_type_invariant_count() {
        let mut state = DeclarationState::new();
        assert_eq!(state.type_invariant_count(), 0);

        state.increment_type_invariant_count();
        assert_eq!(state.type_invariant_count(), 1);

        state.increment_type_invariant_count();
        assert_eq!(state.type_invariant_count(), 2);
    }

    // ── axiom relevance check ──

    #[test]
    fn test_has_any_axiom_relevant_symbols_empty() {
        let state = DeclarationState::new();
        assert!(
            !state.has_any_axiom_relevant_symbols(),
            "fresh state should have no axiom-relevant symbols"
        );
    }

    #[test]
    fn test_has_any_axiom_relevant_symbols_with_logic_func() {
        let mut state = DeclarationState::new();
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let decl = solver.declare_fun("logic_f", &[Sort::Int], Sort::Int);
        state.insert_logic_func("logic_f".to_string(), decl);

        assert!(
            state.has_any_axiom_relevant_symbols(),
            "should detect logic function as axiom-relevant"
        );
    }

    #[test]
    fn test_has_any_axiom_relevant_symbols_with_spec_func() {
        let mut state = DeclarationState::new();
        let mut solver = ay_dpll::api::Solver::new(Logic::QfAuflia);
        let decl = solver.declare_fun("is_some", &[Sort::Int], Sort::Bool);
        state.insert_spec_func("is_some".to_string(), decl);

        assert!(
            state.has_any_axiom_relevant_symbols(),
            "should detect spec function as axiom-relevant"
        );
    }

    #[test]
    fn test_has_any_axiom_relevant_symbols_with_datatype() {
        let mut state = DeclarationState::new();
        let dt = DatatypeSort {
            name: "OptionInt".to_string(),
            constructors: vec![],
        };
        state.insert_datatype("OptionInt".to_string(), dt);

        assert!(
            state.has_any_axiom_relevant_symbols(),
            "should detect datatype as axiom-relevant"
        );
    }

    #[test]
    fn test_has_any_axiom_relevant_symbols_trivial_invariants_alone_not_relevant() {
        let mut state = DeclarationState::new();
        state.register_trivial_invariant("inv_Foo".to_string());
        state.increment_type_invariant_count();

        assert!(
            !state.has_any_axiom_relevant_symbols(),
            "trivial invariants alone should not trigger axiom relevance"
        );
    }
}
