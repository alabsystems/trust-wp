// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Declaration-registry forwarding methods for `AYEncoder`.
//!
//! These methods delegate to `DeclarationState` for logic functions, spec
//! functions, datatypes, and type invariant tracking.
//!
//! Issue: #2588

use std::collections::HashMap;

use ay_dpll::api::{DatatypeSort, FuncDecl, Sort};

use crate::encoder::{sort_context::register_adt_family_alias, AYEncoder, DeclarationState};

impl AYEncoder {
    /// Read-only access to the declaration registry. (#1584)
    ///
    /// Used by verify/setup/ for datatype iteration and sort bootstrapping.
    /// Test code also uses this for read assertions (write access via
    /// `decls_for_test_mut()`).
    pub(crate) fn decls(&self) -> &DeclarationState {
        &self.decls
    }

    /// Clone a registered logic-function declaration through the encoder shell. (#1584)
    pub(in crate::encoder) fn logic_func_decl_cloned(&self, name: &str) -> Option<FuncDecl> {
        self.decls.get_logic_func(name).cloned()
    }

    /// Iterate declared logic-function entries through the encoder shell. (#1584)
    pub(in crate::encoder) fn logic_funcs_iter(
        &self,
    ) -> impl Iterator<Item = (&String, &FuncDecl)> {
        self.decls.logic_funcs_iter()
    }

    /// Iterate declared logic-function names through the encoder shell. (#1584)
    pub(in crate::encoder) fn logic_func_names_iter(&self) -> impl Iterator<Item = &String> {
        self.decls.logic_func_names()
    }

    /// Shared read-only access to declared logic functions for parameter-sort inference. (#1584)
    pub(in crate::encoder) fn logic_funcs_ref(&self) -> &HashMap<String, FuncDecl> {
        self.decls.logic_funcs_ref()
    }

    /// Clone a registered spec-function declaration through the encoder shell. (#1584)
    pub(in crate::encoder) fn spec_func_decl_cloned(&self, name: &str) -> Option<FuncDecl> {
        self.decls.get_spec_func(name).cloned()
    }

    /// Iterate declared spec-function names through the encoder shell. (#1584)
    pub(in crate::encoder) fn spec_func_names_iter(&self) -> impl Iterator<Item = &String> {
        self.decls.spec_func_names()
    }

    /// Check whether a logic function with the given SMT name has been declared. (#1584)
    pub(in crate::encoder) fn has_logic_func_decl(&self, name: &str) -> bool {
        self.decls.has_logic_func(name)
    }

    /// Register a logic function declaration through the encoder shell. (#1584)
    pub(in crate::encoder) fn register_logic_func(&mut self, name: String, decl: FuncDecl) {
        self.decls.insert_logic_func(name, decl);
    }

    /// Get a logic function declaration, declaring it with the solver if absent. (#1584)
    ///
    /// Cross-subsystem helper: combines solver declaration with declaration
    /// registry, replacing the `get_or_declare` pattern repeated across 8+ files.
    pub(crate) fn get_or_declare_logic_func(
        &mut self,
        name: &str,
        domain: &[Sort],
        range: Sort,
    ) -> FuncDecl {
        if let Some(existing) = self.decls.get_logic_func(name) {
            existing.clone()
        } else {
            // Reserved native datatype names (OptionInt/ResultIntInt) must
            // not reach ay as opaque `declare_fun` signature sorts — AY 0.4
            // registers them on sight and rejects the later declare-datatype
            // upgrade. Mirror `normalize_sort`'s variable-path
            // canonicalization. (#2706 residual)
            let domain: Vec<Sort> = domain
                .iter()
                .map(|s| self.canonicalize_reserved_uf_sort(s.clone()))
                .collect();
            let range = self.canonicalize_reserved_uf_sort(range);
            let decl = self.solver.declare_fun(name, &domain, range);
            self.decls.insert_logic_func(name.to_string(), decl.clone());
            decl
        }
    }

    /// Check whether the defining axiom for a logic function has been asserted. (#1584)
    pub(in crate::encoder) fn has_logic_fn_axiom_asserted(&self, name: &str) -> bool {
        self.decls.has_logic_fn_axiom(name)
    }

    /// Mark a logic function axiom as asserted. Returns true if newly inserted. (#1584)
    pub(in crate::encoder) fn mark_logic_fn_axiom_asserted(&mut self, name: String) -> bool {
        self.decls.mark_logic_fn_axiom(name)
    }

    /// Check whether a specific type invariant is trivially true. (#1584)
    pub(in crate::encoder) fn is_trivial_type_invariant(&self, name: &str) -> bool {
        self.decls.is_trivial_invariant(name)
    }

    /// Register a type invariant as trivially true. (#1584)
    pub(in crate::encoder) fn register_trivial_type_invariant(&mut self, name: String) {
        self.decls.register_trivial_invariant(name);
    }

    /// Increment the total type invariant count. (#1584)
    pub(in crate::encoder) fn increment_type_invariant_count(&mut self) {
        self.decls.increment_type_invariant_count();
    }

    /// Check whether all type invariants seen so far are trivially true. (#1584)
    pub(in crate::encoder) fn all_type_invariants_trivially_true(&self) -> bool {
        self.decls.all_type_invariants_trivially_true()
    }

    // --- Spec function shell helpers (#1584) ---

    /// Register a spec function declaration through the encoder shell. (#1584)
    pub(in crate::encoder) fn register_spec_func(&mut self, name: String, decl: FuncDecl) {
        self.decls.insert_spec_func(name, decl);
    }

    /// Get a spec function declaration, declaring it with the solver if absent. (#1584)
    pub(in crate::encoder) fn get_or_declare_spec_func(
        &mut self,
        name: &str,
        domain: &[Sort],
        range: Sort,
    ) -> FuncDecl {
        if let Some(existing) = self.decls.get_spec_func(name) {
            existing.clone()
        } else {
            let decl = self.solver.declare_fun(name, domain, range);
            self.decls.insert_spec_func(name.to_string(), decl.clone());
            decl
        }
    }

    // --- Datatype shell helpers (#1584) ---

    /// Look up a registered datatype by name. (#1584)
    pub(in crate::encoder) fn get_datatype_decl(&self, name: &str) -> Option<&DatatypeSort> {
        self.decls.get_datatype(name)
    }

    /// Crate-visible datatype lookup for verification-layer callers that need to
    /// inspect a carrier's constructor shape (e.g. struct-field reconstruction
    /// bridging in `verify::mut_borrow::bindings`). (#2683)
    pub(crate) fn lookup_datatype_decl(&self, name: &str) -> Option<&DatatypeSort> {
        self.decls.get_datatype(name)
    }

    /// Check whether a datatype with the given name has been declared. (#1584)
    pub(in crate::encoder) fn has_datatype_decl(&self, name: &str) -> bool {
        self.decls.has_datatype(name)
    }

    /// Register a datatype declaration through the encoder shell. (#1584)
    pub(in crate::encoder) fn register_datatype(&mut self, name: String, dt: DatatypeSort) {
        let inferred_aliases =
            if is_synthesized_adt_name(&name) || self.decls.has_synthesized_datatype() {
                infer_synthesized_adt_aliases(&name, &dt, self.decls.datatypes_iter())
            } else {
                Vec::new()
            };
        self.decls.insert_datatype(name, dt);
        for (synthesized, source) in inferred_aliases {
            register_adt_family_alias(&synthesized, &source);
        }
    }

    /// Iterate datatypes that contain a given constructor name. (#1584)
    pub(in crate::encoder) fn datatypes_for_constructor(
        &self,
        ctor_name: &str,
    ) -> impl Iterator<Item = &DatatypeSort> {
        self.decls.datatypes_for_constructor(ctor_name)
    }

    /// Iterate declared datatypes through the encoder shell. (#1584)
    pub(in crate::encoder) fn datatypes_iter(&self) -> impl Iterator<Item = &DatatypeSort> {
        self.decls.datatypes_iter()
    }

    /// Whether any axiom-relevant declarations exist (logic funcs, spec funcs,
    /// or datatypes). When `false`, all axiom assertion families are guaranteed
    /// to be no-ops. (#2674)
    pub(crate) fn has_any_axiom_relevant_symbols(&self) -> bool {
        self.decls.has_any_axiom_relevant_symbols()
    }

    /// Whether any non-builtin (custom) datatypes have been declared. (#1944)
    ///
    /// Returns `true` when the encoder's declaration registry contains datatypes
    /// beyond the standard `OptionInt` and `ResultIntInt` builtins. This is a
    /// runtime check — the static detection in `detect_logic_requirements`
    /// performs the equivalent analysis on expressions before encoder creation.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn has_custom_datatypes(&self) -> bool {
        self.decls.has_custom_datatypes()
    }

    /// Test-only mutable access to the declaration registry. (#1584)
    #[cfg(test)]
    pub(crate) fn decls_for_test_mut(&mut self) -> &mut DeclarationState {
        &mut self.decls
    }
}

fn infer_synthesized_adt_aliases<'a>(
    name: &str,
    dt: &DatatypeSort,
    existing: impl Iterator<Item = &'a DatatypeSort>,
) -> Vec<(String, String)> {
    let mut aliases = Vec::new();
    let name_is_synthesized = is_synthesized_adt_name(name);
    for other in existing {
        let other_is_synthesized = is_synthesized_adt_name(&other.name);
        if name_is_synthesized == other_is_synthesized {
            continue;
        }
        if same_constructor_family(dt, other) {
            if let Some((synthesized, source)) = synthesized_alias_pair(name, &other.name) {
                aliases.push((synthesized, source));
            }
            if let Some((synthesized, source)) = synthesized_alias_pair(&other.name, name) {
                aliases.push((synthesized, source));
            }
        }
    }
    aliases
}

fn is_synthesized_adt_name(name: &str) -> bool {
    name.starts_with("Adt_")
}

fn same_constructor_family(a: &DatatypeSort, b: &DatatypeSort) -> bool {
    if a.constructors.len() != b.constructors.len() || a.constructors.is_empty() {
        return false;
    }

    let mut a_names = a
        .constructors
        .iter()
        .map(|ctor| ctor.name.as_str())
        .collect::<Vec<_>>();
    let mut b_names = b
        .constructors
        .iter()
        .map(|ctor| ctor.name.as_str())
        .collect::<Vec<_>>();
    a_names.sort_unstable();
    b_names.sort_unstable();
    a_names == b_names
}

fn synthesized_alias_pair(a: &str, b: &str) -> Option<(String, String)> {
    if is_synthesized_adt_name(a) && !is_synthesized_adt_name(b) {
        Some((a.to_string(), b.to_string()))
    } else {
        None
    }
}
