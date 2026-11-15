// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Scrutinee sort conflict detection for native match encoding.

use ay_dpll::api::{DatatypeSort, Sort};
use trust_wp_core::formula::PureExpr;

use super::super::AYEncoder;
use crate::encoder::sort_context::{resolve_registered_non_int_sort, DerivedKind};

impl AYEncoder {
    /// Check whether the scrutinee variable is already declared with a
    /// conflicting sort.
    ///
    /// When MIR analysis simplifies a return expression (e.g., `Some(true)` →
    /// `Bool(true)`), `result` may already be declared as `Sort::Bool`. The
    /// match encoder would then try to declare it as `Sort::Datatype(OptionInt)`,
    /// causing a sort conflict (#1055). In such cases, skip native datatype
    /// encoding and fall back to ITE chains.
    ///
    /// `Sort::Uninterpreted("Option")` / `Sort::Uninterpreted("Result")`
    /// are not true conflicts. They are earlier, weaker declarations that
    /// should upgrade to the inferred native datatype sort. Treating them as
    /// hard conflicts silently discards native constructor handling for
    /// match-style postconditions like `match result { Some(..), None => .. }`,
    /// which then fall back to the Int-domain tester path and panic on
    /// `Option`-sorted scrutinees (#2209).
    pub(super) fn scrutinee_has_conflicting_sort(
        &self,
        scrutinee: &PureExpr,
        datatype: &DatatypeSort,
        prefix: Option<DerivedKind>,
    ) -> bool {
        if let Some(var_name) = Self::match_scrutinee_name(scrutinee, prefix) {
            if let Some(declared_sort) = resolve_registered_non_int_sort(self, &var_name) {
                return !Self::sort_is_compatible_with_datatype(&declared_sort, datatype);
            }
            if let Some(term) = self.var_term(&var_name) {
                let actual_sort = self.solver.get_sort(term);
                return !Self::sort_is_compatible_with_datatype(&actual_sort, datatype);
            }
        }
        false
    }

    fn sort_is_compatible_with_datatype(sort: &Sort, datatype: &DatatypeSort) -> bool {
        match sort {
            Sort::Datatype(dt) => dt.name == datatype.name,
            Sort::Uninterpreted(name) => {
                if Self::sorts_are_related(name, &datatype.name) {
                    return true;
                }
                // Synthesized Adt_ names (Adt_Leaf_Node) are derived from
                // constructor names, not the Rust type name (Tree), so
                // sorts_are_related("Tree", "Adt_Leaf_Node") fails. Accept
                // non-encoding Uninterpreted sorts as compatible with
                // synthesized Adt_ datatypes. (#2231)
                let is_encoding_name = matches!(name.as_str(), "Seq" | "FMap" | "Unit" | "Mapping")
                    || name.starts_with("__trust_wp_mutref::")
                    || name.starts_with("Tuple")
                    || name.starts_with("ClosureEnv_");
                datatype.name.starts_with("Adt_") && !is_encoding_name
            }
            _ => false,
        }
    }

    /// Retrieve the existing `DatatypeSort` for a scrutinee variable, if any.
    ///
    /// When the scrutinee variable is already declared with `Sort::Datatype(dt)`,
    /// returns `Some(dt)`. This is used when the match encoder's auto-inferred
    /// datatype conflicts with the pre-existing declaration: the existing one
    /// has the correct field names matching the already-declared SMT sort. (#1763)
    pub(super) fn scrutinee_existing_datatype(
        &self,
        scrutinee: &PureExpr,
        prefix: Option<DerivedKind>,
    ) -> Option<DatatypeSort> {
        if let Some(var_name) = Self::match_scrutinee_name(scrutinee, prefix) {
            if let Some(Sort::Datatype(dt)) = resolve_registered_non_int_sort(self, &var_name) {
                return Some(dt);
            }
        }
        None
    }
}
