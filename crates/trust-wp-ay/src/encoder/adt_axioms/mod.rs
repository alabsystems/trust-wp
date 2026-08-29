// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Algebraic data type axioms: tuple, unit, Option, and Result.
//!
//! This module contains the axiom assertion methods for:
//! - Tuple constructor/destructor axioms (`forall xi. get_I(tupleN(x0..)) = xI`)
//! - Unit singleton axioms (`var = __trust_wp_unit` where `__trust_wp_unit : Sort::Uninterpreted("Unit")`)
//! - Option constructor/tester/accessor axioms (Some/None, is_some, spec_unwrap)
//! - Result constructor/tester/accessor axioms (Ok/Err, is_ok, spec_unwrap, result_err_error)
//! - Qualified (user-defined enum) constructor axioms
//! - Option/Result type disjointness axioms
//!
//! Extracted from `axioms.rs` in #1528 Phase 2.
//!
//! Submodule layout:
//! - `mod.rs` — utility helpers shared by axiom families
//! - `tuple` — tuple constructor/destructor and unit singleton axioms
//! - `option_result` — standard Option/Result axiom assertion
//! - `constructors` — qualified constructor axioms + individual Ok/Err/Some/None helpers
//!
//! # Panic isolation bypass (#1806)
//!
//! Axiom calls in this module use `self.solver.assert_term()` directly rather
//! than the panic-isolated `self.assert_solver_term()` wrapper from `solver.rs`.
//! This is acceptable because:
//!
//! 1. **Fixed sort signatures.** Axiom terms are built from solver-constructed
//!    sorts (e.g., `Sort::Bool`, `Sort::Int`, datatype accessors) with no
//!    user-supplied sort inference. Sort mismatches are therefore programming
//!    errors, not runtime data-dependent failures.
//! 2. **One-time setup.** Axioms are asserted once during theory initialization,
//!    not during per-expression encoding where ay sort mismatches are triggered
//!    by complex user contracts.
//! 3. **Revision tracking not needed.** The `assertion_revision` counter and
//!    pending-assertion flush in `assert_term()` exist for expression-encoding
//!    paths where quantified disjointness rechecks matter. Axiom setup happens
//!    before any `check_sat` calls, so revision ordering is irrelevant.

mod constructors;
mod option_result;
mod structural_induction;
mod tuple;

use std::collections::HashMap;

use ay_dpll::api::{FuncDecl, Sort};

use super::AYEncoder;

impl AYEncoder {
    pub(in crate::encoder) fn parse_leading_usize(suffix: &str) -> Option<usize> {
        let digits_len = suffix.bytes().take_while(u8::is_ascii_digit).count();
        if digits_len == 0 {
            return None;
        }
        suffix[..digits_len].parse::<usize>().ok()
    }

    fn is_int_model_constructor_decl(decl: &FuncDecl, arity: usize) -> bool {
        decl.domain().len() == arity
            && decl.domain().iter().all(|sort| *sort == Sort::Int)
            && *decl.range() == Sort::Int
    }

    fn logic_fn_family_name(name: &str) -> &str {
        name.split_once("__placeholder_")
            .map_or(name, |(family_name, _)| family_name)
    }

    fn record_qualified_constructor(
        constructors: &mut HashMap<String, FuncDecl>,
        full_name: &str,
        family_name: &str,
        decl: &FuncDecl,
    ) {
        let is_raw_decl = full_name == family_name;
        match constructors.entry(family_name.to_string()) {
            std::collections::hash_map::Entry::Vacant(entry) => {
                entry.insert(decl.clone());
            }
            std::collections::hash_map::Entry::Occupied(mut entry) if is_raw_decl => {
                entry.insert(decl.clone());
            }
            std::collections::hash_map::Entry::Occupied(_) => {}
        }
    }

    /// Find the single Int-model declaration used by the standard Option/Result axioms.
    ///
    /// Placeholder registration keeps sort-specific declarations under
    /// `logic_Foo__placeholder_*` keys. The standard axiom layer remains Int-based,
    /// so it must recover the compatible declaration without reintroducing raw-name
    /// aliases into the registry. (#2274)
    fn find_standard_int_constructor_decl(
        &self,
        rust_name: &str,
        arity: usize,
    ) -> Option<FuncDecl> {
        let smt_name = trust_wp_core::logic::logic_fn_smt_name(rust_name);
        if let Some(raw_decl) = self.logic_func_decl_cloned(&smt_name) {
            if Self::is_int_model_constructor_decl(&raw_decl, arity) {
                return Some(raw_decl);
            }
        }

        let placeholder_prefix = format!("{smt_name}__placeholder_");
        self.logic_funcs_iter().find_map(|(name, decl)| {
            (name.starts_with(&placeholder_prefix)
                && Self::is_int_model_constructor_decl(decl, arity))
            .then(|| decl.clone())
        })
    }

    fn find_or_declare_standard_int_constructor_decl(
        &mut self,
        rust_name: &str,
        arity: usize,
    ) -> FuncDecl {
        if let Some(decl) = self.find_standard_int_constructor_decl(rust_name, arity) {
            return decl;
        }
        let smt_name = trust_wp_core::logic::logic_fn_smt_name(rust_name);
        let domain = vec![Sort::Int; arity];
        self.get_or_declare_logic_func(&smt_name, &domain, Sort::Int)
    }
}
