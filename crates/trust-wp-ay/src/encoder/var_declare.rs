// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Variable declaration and sort upgrade logic for `AYEncoder`.
//!
//! This module handles:
//! - Declaring SMT variables with sort tracking (`get_or_declare_var`)
//! - Sort normalization from Rust type paths to canonical SMT sorts
//! - Sort upgrade/downgrade when stronger type evidence arrives
//! - Cross-name sort relatedness checks for ADT encoding

use ay_dpll::api::{Sort, Term};

use super::{sort_context, unsoundness, AYEncoder};
use crate::error::EncodingError;

impl AYEncoder {
    /// Declare the solver identity for a source-level variable.
    ///
    /// Raw source names that overlap AY's reserved namespace are escaped by
    /// the shared source-symbol boundary. The shell environment remains keyed
    /// by the original source spelling.
    pub(in crate::encoder) fn declare_source_var(&mut self, name: &str, sort: Sort) -> Term {
        let identity = crate::source_symbol::base_identity(name);
        self.solver.declare_const(identity.as_ref(), sort)
    }

    /// Declare an auxiliary identity derived from a source variable.
    ///
    /// The role is encoded separately from the source spelling, preventing
    /// collisions with both user variables and auxiliaries from other lanes.
    pub(in crate::encoder) fn declare_derived_source_var(
        &mut self,
        name: &str,
        role: &str,
        sort: Sort,
    ) -> Term {
        let serial = self.var_env.next_source_derived_id();
        let unique_role = format!("{role}:{serial}");
        let identity = crate::source_symbol::derived_identity(name, &unique_role);
        self.solver.declare_const(&identity, sort)
    }

    fn declare_upgraded_source_var(&mut self, name: &str, sort: Sort) -> Term {
        self.declare_derived_source_var(name, "upgrade", sort)
    }

    fn upgrade_var_preserving_structural_bridge(
        &mut self,
        name: &str,
        old_term: Term,
        old_sort: &Sort,
        new_sort: Sort,
    ) -> Term {
        if sort_context::same_structural_family(old_sort, &new_sort).is_some()
            && sort_context::select_structural_sort_target(old_sort, &new_sort).as_ref()
                == Some(&new_sort)
        {
            let bridged_old = self.bridge_structural_sort(old_term, old_sort, &new_sort);
            self.rebind_var(name, bridged_old, new_sort);
            return bridged_old;
        }

        let new_term = self.declare_upgraded_source_var(name, new_sort.clone());
        self.rebind_var(name, new_term, new_sort);
        new_term
    }

    pub(crate) fn is_encoding_sort(sort: &Sort) -> bool {
        match sort {
            Sort::Seq(_) => true,
            Sort::Uninterpreted(name) => {
                matches!(name.as_str(), "Seq" | "FMap" | "Mapping" | "Unit")
                    || name.starts_with("__trust_wp_mutref::")
                    || name.starts_with("Tuple")
                    || name.starts_with("ClosureEnv_")
            }
            _ => false,
        }
    }

    fn is_well_known_datatype(sort: &Sort) -> bool {
        matches!(
            sort,
            Sort::Datatype(dt) if matches!(dt.name.as_str(), "OptionInt" | "ResultIntInt")
        )
    }

    /// Encoding-sort subset used as a speculative placeholder during body
    /// encoding. Excludes ClosureEnv and __trust_wp_mutref carriers because the
    /// well-known Option/Result suppression below only applies to collection/
    /// tuple placeholders. (#2699)
    fn is_speculative_encoding_sort(sort: &Sort) -> bool {
        match sort {
            Sort::Seq(_) => true,
            Sort::Uninterpreted(name) => {
                matches!(name.as_str(), "Seq" | "FMap" | "Mapping" | "Unit")
                    || name.starts_with("Tuple")
            }
            _ => false,
        }
    }

    /// Classify an encoding sort into its canonical family for cross-family
    /// conflict suppression. Returns `None` for non-encoding sorts.
    ///
    /// Family classification:
    /// - `Sort::Seq(_)` or `Uninterpreted("Seq")` → "seq"
    /// - `Uninterpreted("FMap")` → "fmap"
    /// - `Uninterpreted("Unit")` → "unit"
    /// - `Uninterpreted("Mapping")` → "mapping"
    /// - `Uninterpreted("Tuple<N>")` → "tuple" (all arities share one family)
    /// - `Uninterpreted("ClosureEnv_*")` → "closure"
    /// - `Uninterpreted("__trust_wp_mutref::*")` → "mutref"
    ///
    /// This ensures cross-family suppression only fires between truly distinct
    /// families (e.g., Seq vs FMap) and not between variants within the same
    /// family (e.g., Tuple2 vs Tuple2Int). (#2231)
    fn encoding_sort_family(sort: &Sort) -> Option<&'static str> {
        match sort {
            Sort::Seq(_) => Some("seq"),
            Sort::Uninterpreted(name) => match name.as_str() {
                "Seq" => Some("seq"),
                "FMap" => Some("fmap"),
                "Unit" => Some("unit"),
                "Mapping" => Some("mapping"),
                _ if name.starts_with("Tuple") => Some("tuple"),
                _ if name.starts_with("ClosureEnv_") => Some("closure"),
                _ if name.starts_with("__trust_wp_mutref::") => Some("mutref"),
                _ => None,
            },
            _ => None,
        }
    }

    /// Check whether an Uninterpreted sort name and a Datatype name plausibly
    /// refer to the same Rust type. This prevents unsound cross-name suppression
    /// where unrelated types (e.g., String vs OptionInt) are silently merged.
    ///
    /// Returns `true` when:
    /// - The names match exactly (after stripping Rust module paths)
    /// - The Rust type name (last path segment) appears as a case-insensitive
    ///   prefix of the Datatype name (e.g., "Result" matches "ResultIntInt")
    /// - The Datatype name starts with "Adt_" (synthesized from constructors)
    ///   and the Rust type name appears in the constructor list
    ///
    /// Sound default: `false` (reject unrecognized cross-name pairings). (#1965)
    pub(in crate::encoder) fn sorts_are_related(
        uninterpreted_name: &str,
        datatype_name: &str,
    ) -> bool {
        // Strip Rust module path to get the bare type name
        let rust_type = uninterpreted_name
            .rsplit("::")
            .next()
            .unwrap_or(uninterpreted_name);

        // Guard: empty type names (from trailing "::") would match everything
        // via starts_with(""). Reject as unrelated. (#1965, P1-73)
        if rust_type.is_empty() {
            return false;
        }

        // Exact match after path stripping
        if rust_type == datatype_name {
            return true;
        }

        // Rust type name is a prefix of the ADT name (e.g., "Result" -> "ResultIntInt",
        // "Option" -> "OptionInt"). Case-sensitive because Rust types are PascalCase.
        if datatype_name.starts_with(rust_type) {
            return true;
        }

        // Synthesized ADT names like "Adt_Cons_Nil" — check if the Rust type
        // name appears in the constructor-derived segments
        if let Some(suffix) = datatype_name.strip_prefix("Adt_") {
            // The Rust type name won't appear in "Adt_Cons_Nil" directly,
            // so this is only a match if the user explicitly named their
            // constructors with the type name prefix
            let segments: Vec<&str> = suffix.split('_').collect();
            if segments.iter().any(|s| s.eq_ignore_ascii_case(rust_type)) {
                return true;
            }
        }

        false
    }

    /// Get an existing variable or declare a new one.
    ///
    /// On cache hit, verifies that the requested `sort` matches the sort used
    /// at first declaration. Returns `EncodingError` on sort conflict (#835).
    ///
    /// Normalize Uninterpreted sort names from Rust type paths to their
    /// canonical SMT encoding sorts. Without this, variables may be declared
    /// as `Uninterpreted("std::vec::Vec")` instead of `Sort::Seq(Int)`,
    /// causing sort mismatches when Seq/FMap operations are applied. (#1965, #2080)
    fn normalize_sort(&mut self, sort: Sort) -> Sort {
        if let Sort::Seq(_) = sort {
            if let Some(seq_sort) = self.seq_state.sort() {
                if matches!(seq_sort, Sort::Uninterpreted(name) if name == "Seq") {
                    return seq_sort.clone();
                }
            }
        }
        if let Sort::Uninterpreted(ref name) = sort {
            // AY 0.4 deliberately rejects upgrading an already-declared
            // uninterpreted sort into a datatype with the same name. OptionInt
            // and ResultIntInt are reserved native encoding sorts, so
            // canonicalize them before the first variable declaration can
            // register the legacy uninterpreted spelling in the solver.
            let well_known_datatype = match name.as_str() {
                "OptionInt" => Some(crate::encoder::match_enc::SwitchTarget::OptionInt.datatype()),
                "ResultIntInt" => {
                    Some(crate::encoder::match_enc::SwitchTarget::ResultIntInt.datatype())
                }
                _ => None,
            };
            if let Some(datatype) = well_known_datatype {
                let datatype = self.get_datatype_decl(name).cloned().unwrap_or(datatype);
                self.ensure_datatype_declared(&datatype);
                return Sort::Datatype(datatype);
            }
            if name.starts_with("__trust_wp_mutref::") {
                return sort;
            }
            if name == "Seq" {
                return sort;
            }
            use sort_context::sort_inference::{canonical_sort, CanonicalSort};
            match canonical_sort(name) {
                CanonicalSort::Seq => {
                    return self
                        .seq_state
                        .sort()
                        .cloned()
                        .unwrap_or_else(|| Sort::seq(Sort::Int));
                }
                CanonicalSort::FMap => {
                    return sort_context::sort_inference::fmap_sort();
                }
                CanonicalSort::Mapping => {
                    return sort_context::sort_inference::mapping_sort();
                }
                CanonicalSort::Int => return Sort::Int,
                CanonicalSort::Uninterpreted(bare) => {
                    if name.contains("::") {
                        return Sort::Uninterpreted(bare);
                    }
                }
            }
        }
        sort
    }

    /// **Sort upgrade (#1965, Lane 4):** When the existing sort is `Int` (the
    /// universal fallback from `infer_expr_sort`) and the requested sort is
    /// non-Int, the variable is redeclared with the correct sort. This breaks
    /// the "first-declaration-wins" invariant only for Int→non-Int upgrades,
    /// which are always speculative defaults being corrected by stronger type
    /// evidence. Genuine conflicts (non-Int vs different non-Int) still error.
    ///
    /// The old ay term remains in the solver but is no longer referenced by
    /// the active shell binding. Assertions already made about it constrain a
    /// constant no later read sees: an UNSAT over them is still a proof, since
    /// they only weaken the query, but a model need not be an execution, so
    /// the abandoned term is recorded and a refutation that reads it is
    /// withheld (D-218).
    pub(crate) fn get_or_declare_var(
        &mut self,
        name: &str,
        sort: Sort,
    ) -> Result<Term, EncodingError> {
        let prior = self.var_term(name);
        let term = self.get_or_declare_var_at_sort(name, sort)?;
        // An upgrade that rebinds the name to a fresh constant splits it: the
        // facts already asserted about the prior constant are not facts about
        // the new one. The structural bridge rebinds to a term built over the
        // prior constant, which keeps the two related, and is not counted.
        if let Some(prior) = prior {
            if prior != term && self.solver.var_name(term).is_some() {
                self.var_env.record_split_source(name, prior);
            }
        }
        Ok(term)
    }

    #[allow(clippy::too_many_lines)]
    fn get_or_declare_var_at_sort(
        &mut self,
        name: &str,
        sort: Sort,
    ) -> Result<Term, EncodingError> {
        // Normalize Uninterpreted sorts from Rust type paths to canonical
        // SMT encoding sorts (e.g., "std::vec::Vec" → Sort::Seq(Int)). (#1965, #2080)
        let sort = self.normalize_sort(sort);
        if let Some(term) = self.var_term(name) {
            if let Some(declared_sort) = self.var_sort(name).cloned() {
                if declared_sort != sort {
                    // Int→non-Int upgrade: the Int was a speculative default.
                    // Redeclare with the correct sort. (#1965)
                    if declared_sort == Sort::Int && sort != Sort::Int {
                        tracing::debug!(
                            var = name,
                            from = ?declared_sort,
                            to = ?sort,
                            "sort upgrade: redeclaring variable with stronger type evidence"
                        );
                        unsoundness::increment(
                            unsoundness::UnsoundnessCategory::PhantomVariableUpgrade,
                        );
                        let new_term = self.declare_upgraded_source_var(name, sort.clone());
                        self.rebind_var(name, new_term, sort);
                        return Ok(new_term);
                    }
                    // Bool→Int coercion: the variable was declared as Bool
                    // (e.g., from a boolean closure capture) but later used in
                    // an Int context (e.g., arithmetic or comparison). Redeclare
                    // with Int sort. Bool→Int is lossless via ite(b, 1, 0) but
                    // the variable rebinding discards the old Bool term, which
                    // is sound since the value semantics are preserved. (#2696)
                    if declared_sort == Sort::Bool && sort == Sort::Int {
                        tracing::debug!(
                            var = name,
                            from = ?declared_sort,
                            to = ?sort,
                            "sort upgrade: Bool → Int (Bool-valued variable used in Int context)"
                        );
                        unsoundness::increment(
                            unsoundness::UnsoundnessCategory::PhantomVariableUpgrade,
                        );
                        let new_term = self.declare_upgraded_source_var(name, sort.clone());
                        self.rebind_var(name, new_term, sort);
                        return Ok(new_term);
                    }
                    // Non-Int→Int downgrade: the variable was declared with an
                    // Uninterpreted Datatype sort (e.g., "std::time::Duration")
                    // but the correct sort is Int (Duration models as integer).
                    // This happens when a code path declares the variable before
                    // sort resolution runs. Only applies to Uninterpreted sorts
                    // that are NOT well-known encoding sorts (Seq, FMap, Unit,
                    // Tuple*, ClosureEnv_*). (#1965)
                    if sort == Sort::Int
                        && matches!(&declared_sort, Sort::Uninterpreted(s)
                            if !matches!(s.as_str(),
                                "Seq" | "FMap" | "Unit"
                            ) && !s.starts_with("Tuple") && !s.starts_with("ClosureEnv_"))
                    {
                        tracing::debug!(
                            var = name,
                            from = ?declared_sort,
                            to = ?sort,
                            "sort downgrade: Uninterpreted → Int for Int-model type"
                        );
                        unsoundness::increment(
                            unsoundness::UnsoundnessCategory::PhantomVariableUpgrade,
                        );
                        let new_term = self.declare_upgraded_source_var(name, sort.clone());
                        self.rebind_var(name, new_term, sort);
                        return Ok(new_term);
                    }
                    // Datatype→Datatype with same ADT name: user-defined ADTs
                    // (e.g., List = Cons | Nil) may produce structurally different
                    // DatatypeSort objects from different encoding paths (match
                    // patterns vs pre-declaration vs closure sorts). Since both
                    // represent the same ADT, keep the existing declaration.
                    // (#1965, #2189)
                    if let (Sort::Datatype(existing_dt), Sort::Datatype(new_dt)) =
                        (&declared_sort, &sort)
                    {
                        if sort_context::same_structural_family(&declared_sort, &sort).as_deref()
                            == Some("Option")
                        {
                            if existing_dt.name == "OptionInt" && new_dt.name != "OptionInt" {
                                tracing::debug!(
                                    var = name,
                                    from = ?declared_sort,
                                    to = ?sort,
                                    "sort upgrade: generic OptionInt datatype -> specialized Option datatype"
                                );
                                unsoundness::increment(
                                    unsoundness::UnsoundnessCategory::PhantomVariableUpgrade,
                                );
                                let new_term = self.declare_upgraded_source_var(name, sort.clone());
                                self.rebind_var(name, new_term, sort);
                                return Ok(new_term);
                            }
                            tracing::debug!(
                                var = name,
                                existing = ?declared_sort,
                                requested = ?sort,
                                "sort conflict suppressed: keeping existing Option-family datatype"
                            );
                            return Ok(term);
                        }
                        if existing_dt.name == new_dt.name {
                            tracing::debug!(
                                var = name,
                                dt_name = existing_dt.name,
                                "sort conflict suppressed: same-name Datatype re-resolution"
                            );
                            return Ok(term);
                        }
                    }
                    // Uninterpreted↔Datatype with same ClosureEnv name: closure
                    // sorts are now declared as Datatype (#2151) but axiom code
                    // may reconstruct them as Uninterpreted from sort tags. Since
                    // ay maps Datatype→Uninterpreted internally via as_term_sort(),
                    // these are equivalent. Keep the existing declaration.
                    if let (Sort::Uninterpreted(s), Sort::Datatype(dt))
                    | (Sort::Datatype(dt), Sort::Uninterpreted(s)) = (&declared_sort, &sort)
                    {
                        if s.starts_with("ClosureEnv_") && dt.name == *s {
                            tracing::debug!(
                                var = name,
                                sort_name = s,
                                "sort conflict suppressed: ClosureEnv Uninterpreted/Datatype equivalence"
                            );
                            return Ok(term);
                        }
                    }
                    // MutRef nesting conflict: both sorts are __trust_wp_mutref::*
                    // but with different nesting depths. This happens when the
                    // postcondition annotation has an over-nested MutRef type
                    // (e.g., MutRef(MutRef(Int)) for a result that's actually
                    // MutRef(Int)). Keep the existing declaration — the first
                    // declaration comes from infer_result_sort which correctly
                    // peels reference layers. (#2583)
                    if let (Sort::Uninterpreted(existing_name), Sort::Uninterpreted(new_name)) =
                        (&declared_sort, &sort)
                    {
                        if existing_name.starts_with("__trust_wp_mutref::")
                            && new_name.starts_with("__trust_wp_mutref::")
                        {
                            tracing::debug!(
                                var = name,
                                existing = ?declared_sort,
                                requested = ?sort,
                                "sort conflict suppressed: __trust_wp_mutref nesting mismatch"
                            );
                            return Ok(term);
                        }
                    }
                    // Uninterpreted→Uninterpreted upgrade for related type names:
                    // the variable was declared with a generic Uninterpreted sort
                    // (e.g., "Option") but the body encoding later produces a
                    // monomorphized Uninterpreted sort (e.g., "OptionInt").
                    // Upgrade to the more specific (longer) name.
                    //
                    // Only applies to non-encoding Uninterpreted sorts
                    // (not Seq, FMap, Unit, Tuple*, ClosureEnv_*, __trust_wp_mutref::*).
                    // The __trust_wp_mutref case is handled above. (#761)
                    if let (
                        Sort::Uninterpreted(ref existing_name),
                        Sort::Uninterpreted(ref new_name),
                    ) = (&declared_sort, &sort)
                    {
                        if !Self::is_encoding_sort(&declared_sort)
                            && !Self::is_encoding_sort(&sort)
                            && !existing_name.starts_with("__trust_wp_mutref::")
                            && !new_name.starts_with("__trust_wp_mutref::")
                        {
                            // Check both directions: the shorter name is the
                            // generic one, the longer name is monomorphized.
                            let related = Self::sorts_are_related(existing_name, new_name)
                                || Self::sorts_are_related(new_name, existing_name);
                            if related {
                                // Pick the more specific (longer) name as the
                                // upgrade target.
                                let upgrade_sort = if new_name.len() >= existing_name.len() {
                                    sort.clone()
                                } else {
                                    declared_sort.clone()
                                };
                                if upgrade_sort == declared_sort {
                                    // Existing sort is already more specific —
                                    // suppress without redeclaration.
                                    tracing::debug!(
                                        var = name,
                                        existing = ?declared_sort,
                                        requested = ?sort,
                                        "sort conflict suppressed: Uninterpreted already \
                                         more specific than requested"
                                    );
                                    return Ok(term);
                                }
                                tracing::debug!(
                                    var = name,
                                    from = ?declared_sort,
                                    to = ?upgrade_sort,
                                    "sort upgrade: Uninterpreted → Uninterpreted \
                                     (related monomorphized name)"
                                );
                                unsoundness::increment(
                                    unsoundness::UnsoundnessCategory::PhantomVariableUpgrade,
                                );
                                let new_term =
                                    self.declare_upgraded_source_var(name, upgrade_sort.clone());
                                self.rebind_var(name, new_term, upgrade_sort);
                                return Ok(new_term);
                            }
                        }
                    }
                    // Datatype(collection_model)→canonical sort downgrade: the
                    // variable was declared with a native ay Datatype sort for
                    // a type that trust-wp models as a collection sort (e.g.,
                    // Vec → Seq, HashMap → FMap). The driver's struct layout
                    // extraction creates Datatype sorts from the actual Rust
                    // representation (Vec { buf: RawVec, len: usize }), but
                    // the verification encoding models these as Seq/FMap.
                    // Only fire when the requested sort is the canonical target
                    // or Int (the universal fallback). Incompatible requests
                    // (e.g., Bool) fall through to the conflict path. (#2557)
                    if let Sort::Datatype(ref existing_dt) = &declared_sort {
                        use sort_context::sort_inference::{
                            canonical_sort, fmap_sort, mapping_sort, CanonicalSort,
                        };
                        let canonical = canonical_sort(&existing_dt.name);
                        if !matches!(canonical, CanonicalSort::Uninterpreted(_)) {
                            let target_sort = match canonical {
                                CanonicalSort::Seq => self.get_seq_sort(),
                                CanonicalSort::FMap => fmap_sort(),
                                CanonicalSort::Mapping => mapping_sort(),
                                CanonicalSort::Int => Sort::Int,
                                CanonicalSort::Uninterpreted(_) => unreachable!(),
                            };
                            if sort == target_sort || sort == Sort::Int {
                                tracing::debug!(
                                    var = name,
                                    from = ?declared_sort,
                                    to = ?target_sort,
                                    "sort downgrade: Datatype(collection) → canonical sort (#2557)"
                                );
                                unsoundness::increment(
                                    unsoundness::UnsoundnessCategory::PhantomVariableUpgrade,
                                );
                                let new_term =
                                    self.declare_upgraded_source_var(name, target_sort.clone());
                                self.rebind_var(name, new_term, target_sort);
                                return Ok(new_term);
                            }
                        }
                    }
                    // Encoding-sort→Datatype upgrade: the variable was
                    // speculatively declared as Sort::Seq(Int) or
                    // Uninterpreted("FMap") by prescan, but the match encoding
                    // later determined the correct sort is a Datatype.
                    //
                    // This covers two cases:
                    // (a) Well-known Datatypes (OptionInt, ResultIntInt) —
                    //     postcondition prescan misattributes Seq evidence to
                    //     `result` while the actual return type is Option/Result.
                    //     (#2155)
                    // (b) User-defined ADTs with synthesized names (Adt_Cons_Nil,
                    //     etc.) — the type name matched a collection model name
                    //     (e.g., "List" matched is_seq_model_type) but the match
                    //     encoding revealed it is actually a recursive user enum.
                    //     (#2231)
                    //
                    // The Datatype sort from match encoding is definitively more
                    // precise than the speculative encoding sort.
                    if let Sort::Datatype(ref new_dt) = &sort {
                        let is_well_known_dt = Self::is_well_known_datatype(&sort);
                        let is_synthesized_adt = new_dt.name.starts_with("Adt_");
                        if Self::is_encoding_sort(&declared_sort)
                            && (is_well_known_dt || is_synthesized_adt)
                        {
                            tracing::debug!(
                                var = name,
                                from = ?declared_sort,
                                to = ?sort,
                                "sort upgrade: encoding sort → Datatype (#2155, #2231)"
                            );
                            unsoundness::increment(
                                unsoundness::UnsoundnessCategory::PhantomVariableUpgrade,
                            );
                            let new_term = self.declare_upgraded_source_var(name, sort.clone());
                            self.rebind_var(name, new_term, sort);
                            return Ok(new_term);
                        }
                    }
                    // Uninterpreted→Datatype upgrade: the variable was declared
                    // with Sort::Uninterpreted("TypeName") before the actual
                    // Datatype declaration was available. Upgrade to the more
                    // precise Datatype sort.
                    //
                    // Safety: requires `sorts_are_related` to verify that the
                    // Uninterpreted name and Datatype name plausibly refer to
                    // the same Rust type. Without this check, unrelated types
                    // (e.g., Uninterpreted("String") vs Datatype(OptionInt))
                    // would be silently merged — an unsoundness. (#1965, P1-72)
                    //
                    // Exception: synthesized Adt_ names (Adt_Leaf_Node, etc.)
                    // are derived from constructor names and never contain the
                    // Rust type name (e.g., Tree -> Adt_Leaf_Node). For these,
                    // the name-based check cannot succeed, so we accept any
                    // non-encoding Uninterpreted sort. This mirrors the
                    // Datatype->Uninterpreted is_synthesized_adt bypass below.
                    // (#2231)
                    //
                    // Exception 2: TupleN encoding sorts (Tuple2, Tuple3, etc.)
                    // where the Datatype has exactly N fields. The driver emitted
                    // TupleN as a positional placeholder; the Datatype carries the
                    // actual struct layout with named fields and accessors. (#2699)
                    //
                    // Only applies to non-encoding Uninterpreted sorts for the
                    // name-related and synthesized Adt paths.
                    // (not Seq, FMap, Unit, Tuple*, ClosureEnv_*).
                    if let Sort::Datatype(ref new_dt) = &sort {
                        if let Sort::Uninterpreted(ref s) = &declared_sort {
                            if sort_context::same_structural_family(&declared_sort, &sort)
                                .as_deref()
                                == Some("Option")
                            {
                                tracing::debug!(
                                    var = name,
                                    from = ?declared_sort,
                                    to = ?sort,
                                    "sort upgrade: Option-family Uninterpreted -> Datatype"
                                );
                                unsoundness::increment(
                                    unsoundness::UnsoundnessCategory::PhantomVariableUpgrade,
                                );
                                let new_term = self.declare_upgraded_source_var(name, sort.clone());
                                self.rebind_var(name, new_term, sort);
                                return Ok(new_term);
                            }
                            let is_synthesized_adt = new_dt.name.starts_with("Adt_");
                            // TupleN→Datatype upgrade: the variable was speculatively
                            // declared as Uninterpreted("TupleN") but the match encoding
                            // or struct layout extraction later produced a proper Datatype
                            // with N fields. Upgrade to the Datatype for named selector
                            // access. (#2699)
                            let is_tuple_arity_match = s.starts_with("Tuple")
                                && s.len() > 5
                                && s[5..].chars().all(|c| c.is_ascii_digit())
                                && new_dt.constructors.len() == 1
                                && s[5..]
                                    .parse::<usize>()
                                    .is_ok_and(|n| new_dt.constructors[0].fields.len() == n);
                            if is_tuple_arity_match {
                                tracing::debug!(
                                    var = name,
                                    from = ?declared_sort,
                                    to = ?sort,
                                    "sort upgrade: TupleN → Datatype with matching arity (#2699)"
                                );
                                unsoundness::increment(
                                    unsoundness::UnsoundnessCategory::PhantomVariableUpgrade,
                                );
                                let new_term = self.declare_upgraded_source_var(name, sort.clone());
                                self.rebind_var(name, new_term, sort);
                                return Ok(new_term);
                            }
                            if !Self::is_encoding_sort(&declared_sort)
                                && (Self::sorts_are_related(s, &new_dt.name) || is_synthesized_adt)
                            {
                                tracing::debug!(
                                    var = name,
                                    from = ?declared_sort,
                                    to = ?sort,
                                    synthesized = is_synthesized_adt,
                                    "sort upgrade: Uninterpreted -> Datatype (name-related or synthesized Adt)"
                                );
                                unsoundness::increment(
                                    unsoundness::UnsoundnessCategory::PhantomVariableUpgrade,
                                );
                                let new_term = self.upgrade_var_preserving_structural_bridge(
                                    name,
                                    term,
                                    &declared_sort,
                                    sort,
                                );
                                return Ok(new_term);
                            }
                            // User-defined Uninterpreted → user-defined Datatype
                            // upgrade: when the Uninterpreted sort is a non-encoding
                            // user type name (e.g., "Fragment") and the Datatype is
                            // also a non-encoding user ADT (e.g., "Authority"), allow
                            // the upgrade when they share the same structural family
                            // via `same_structural_family`, OR when both are plain
                            // user types (neither is encoding nor __trust_wp_*). This
                            // handles ghost resource types where the driver's initial
                            // sort inference picks the wrong representation. (#2699)
                            if !Self::is_encoding_sort(&declared_sort)
                                && !s.starts_with("__trust_wp_")
                                && !new_dt.name.starts_with("__trust_wp_")
                            {
                                let same_family =
                                    sort_context::same_structural_family(&declared_sort, &sort)
                                        .is_some();
                                // Also allow upgrade for user ADTs that have a single
                                // constructor matching the type name — these are Rust
                                // structs represented as single-variant Datatypes where
                                // the Uninterpreted was a placeholder. (#2699)
                                let is_single_ctor_struct = new_dt.constructors.len() == 1
                                    && new_dt.constructors[0].name == new_dt.name;
                                if same_family || is_single_ctor_struct {
                                    tracing::debug!(
                                        var = name,
                                        from = ?declared_sort,
                                        to = ?sort,
                                        same_family,
                                        is_single_ctor_struct,
                                        "sort upgrade: Uninterpreted → Datatype \
                                         (user-defined type family or struct) (#2699)"
                                    );
                                    unsoundness::increment(
                                        unsoundness::UnsoundnessCategory::PhantomVariableUpgrade,
                                    );
                                    let new_term =
                                        self.declare_upgraded_source_var(name, sort.clone());
                                    self.rebind_var(name, new_term, sort);
                                    return Ok(new_term);
                                }
                            }
                        }
                    }
                    // Datatype→Uninterpreted: keep existing Datatype (more
                    // precise). This happens when a later code path uses
                    // Sort::Uninterpreted("TypeName") for an ADT that was
                    // already declared with Sort::Datatype.
                    //
                    // This is the CONSERVATIVE direction: we keep the existing
                    // sort unchanged. More permissive than the Uninterpreted→
                    // Datatype upgrade because no sort change occurs.
                    //
                    // Allowed when:
                    // (a) names are related (prefix/exact match), OR
                    // (b) the existing Datatype has a synthesized name ("Adt_*")
                    //     — these are always user ADTs from match encoding where
                    //     the name mismatch with Rust types is expected.
                    // (c) the requested sort is a TupleN encoding sort and the
                    //     existing Datatype has exactly N fields in its (single)
                    //     constructor — the driver emitted TupleN as a positional
                    //     placeholder for a named struct that was already declared
                    //     with its proper Datatype sort. (#2699)
                    //
                    // Only applies to non-encoding Uninterpreted sorts for (a/b).
                    // (not Seq, FMap, Unit, Tuple*, ClosureEnv_*). (#1965, P1-72)
                    if let Sort::Datatype(ref existing_dt) = &declared_sort {
                        if let Sort::Uninterpreted(ref s) = &sort {
                            if sort_context::same_structural_family(&declared_sort, &sort)
                                .as_deref()
                                == Some("Option")
                            {
                                tracing::debug!(
                                    var = name,
                                    existing = ?declared_sort,
                                    requested = ?sort,
                                    "sort conflict suppressed: keeping Option-family datatype over generic request"
                                );
                                return Ok(term);
                            }
                            let is_synthesized_adt = existing_dt.name.starts_with("Adt_");
                            // Case (c): TupleN encoding sort vs Datatype with
                            // matching arity. The Datatype carries the real
                            // struct layout (named fields, accessors); TupleN is
                            // just a positional placeholder. Keep the Datatype.
                            let is_tuple_arity_match = s.starts_with("Tuple")
                                && s.len() > 5
                                && s[5..].chars().all(|c| c.is_ascii_digit())
                                && existing_dt.constructors.len() == 1
                                && s[5..]
                                    .parse::<usize>()
                                    .is_ok_and(|n| existing_dt.constructors[0].fields.len() == n);
                            if is_tuple_arity_match {
                                tracing::debug!(
                                    var = name,
                                    existing = ?declared_sort,
                                    requested = ?sort,
                                    "sort conflict suppressed: Datatype already declared, \
                                     TupleN encoding sort with matching arity ignored (#2699)"
                                );
                                return Ok(term);
                            }
                            // Case (c2): TupleN encoding sort vs multi-variant
                            // user enum Datatype. A multi-constructor ADT (e.g.,
                            // `OwnResult = Ok | Err`) cannot be a tuple — the
                            // TupleN request is a speculative placeholder from
                            // MIR-side newtype-wrapping rewrites (e.g., the
                            // `tuple1(deref_val)` wrap for whole-`&mut self`
                            // final values) that leaked onto an enum carrier.
                            // Keep the authoritative Datatype declaration.
                            // (#5, result/own::as_mut)
                            let is_tuple_vs_multi_ctor_enum = s.starts_with("Tuple")
                                && s.len() > 5
                                && s[5..].chars().all(|c| c.is_ascii_digit())
                                && existing_dt.constructors.len() >= 2;
                            if is_tuple_vs_multi_ctor_enum {
                                tracing::debug!(
                                    var = name,
                                    existing = ?declared_sort,
                                    requested = ?sort,
                                    "sort conflict suppressed: Datatype (multi-ctor enum) \
                                     already declared, TupleN encoding sort ignored (#5)"
                                );
                                return Ok(term);
                            }
                            if !Self::is_encoding_sort(&sort)
                                && (Self::sorts_are_related(s, &existing_dt.name)
                                    || is_synthesized_adt)
                            {
                                tracing::debug!(
                                    var = name,
                                    existing = ?declared_sort,
                                    requested = ?sort,
                                    synthesized = is_synthesized_adt,
                                    "sort conflict suppressed: Datatype already declared, \
                                     Uninterpreted request ignored"
                                );
                                return Ok(term);
                            }
                            // User-defined Datatype→user-defined Uninterpreted
                            // suppression: when the existing Datatype is a user
                            // struct (single constructor matching type name) and the
                            // requested Uninterpreted is a non-encoding user type,
                            // keep the Datatype. This mirrors the Uninterpreted→
                            // Datatype single-ctor-struct upgrade path above. (#2699)
                            if !Self::is_encoding_sort(&sort)
                                && !s.starts_with("__trust_wp_")
                                && (existing_dt.constructors.len() == 1
                                    && existing_dt.constructors[0].name == existing_dt.name)
                            {
                                tracing::debug!(
                                    var = name,
                                    existing = ?declared_sort,
                                    requested = ?sort,
                                    "sort conflict suppressed: Datatype(struct) already \
                                     declared, Uninterpreted user type request ignored (#2699)"
                                );
                                return Ok(term);
                            }
                        }
                    }
                    // Encoding-sort cross-family conflict suppression:
                    // When both the declared and requested sorts are from
                    // different recognized encoding families (Seq vs FMap,
                    // FMap vs Seq, etc.), keep the existing sort and suppress
                    // the conflict. This happens when prescan infers one
                    // collection family (e.g., FMap) but a later code path
                    // uses a different family (e.g., Seq). Both are encoding-
                    // level approximations; keeping the first declaration is
                    // conservative because the variable's constraints are
                    // already expressed in the first sort's theory.
                    //
                    // Only suppresses conflicts between distinct canonical
                    // families (Seq, FMap, Mapping), not between variants
                    // within the same family (e.g., Tuple2 vs Tuple2Int are
                    // both Tuple-prefixed but not cross-family). (#2231)
                    if Self::encoding_sort_family(&declared_sort).is_some_and(|d_family| {
                        Self::encoding_sort_family(&sort)
                            .is_some_and(|s_family| d_family != s_family)
                    }) {
                        tracing::debug!(
                            var = name,
                            existing = ?declared_sort,
                            requested = ?sort,
                            "sort conflict suppressed: cross-family encoding sort conflict"
                        );
                        return Ok(term);
                    }
                    // Datatype→Datatype with related names: the same Rust type
                    // may produce different DatatypeSort objects from different
                    // encoding paths (e.g., one with more fields from a richer
                    // declaration site). Prefer the existing declaration since
                    // it was used for earlier assertions. (#2231)
                    if let (Sort::Datatype(ref existing_dt), Sort::Datatype(ref new_dt)) =
                        (&declared_sort, &sort)
                    {
                        // Check if the Datatype names are related via the
                        // same relatedness test used for Uninterpreted sorts.
                        if Self::sorts_are_related(&existing_dt.name, &new_dt.name)
                            || Self::sorts_are_related(&new_dt.name, &existing_dt.name)
                            || existing_dt.name.starts_with("Adt_")
                            || new_dt.name.starts_with("Adt_")
                        {
                            tracing::debug!(
                                var = name,
                                existing = ?declared_sort,
                                requested = ?sort,
                                "sort conflict suppressed: Datatype related-name or Adt_ synthesis"
                            );
                            return Ok(term);
                        }
                    }
                    // Well-known Datatype vs speculative encoding placeholder:
                    // result type inference may have already fixed the variable
                    // to a precise Option/Result Datatype while body encoding
                    // later requests a placeholder Seq/FMap/Mapping/Unit/Tuple
                    // carrier. Keep the existing Datatype. (#2699)
                    if Self::is_well_known_datatype(&declared_sort)
                        && Self::is_speculative_encoding_sort(&sort)
                    {
                        tracing::debug!(
                            var = name,
                            existing = ?declared_sort,
                            requested = ?sort,
                            "sort conflict suppressed: keeping inferred well-known Datatype over speculative encoding sort (#2699)"
                        );
                        unsoundness::increment(
                            unsoundness::UnsoundnessCategory::PhantomVariableUpgrade,
                        );
                        return Ok(term);
                    }
                    // Reverse of the above: if the existing declaration is a
                    // speculative encoding placeholder and stronger result type
                    // inference later resolves the variable to Option/Result,
                    // upgrade to the well-known Datatype. (#2699)
                    if Self::is_encoding_sort(&declared_sort)
                        && Self::is_speculative_encoding_sort(&declared_sort)
                        && Self::is_well_known_datatype(&sort)
                    {
                        tracing::debug!(
                            var = name,
                            from = ?declared_sort,
                            to = ?sort,
                            "sort upgrade: speculative encoding sort -> inferred well-known Datatype (#2699)"
                        );
                        unsoundness::increment(
                            unsoundness::UnsoundnessCategory::PhantomVariableUpgrade,
                        );
                        let new_term = self.declare_upgraded_source_var(name, sort.clone());
                        self.rebind_var(name, new_term, sort);
                        return Ok(new_term);
                    }
                    if name == "self_current"
                        && hashmap_list_receiver_sort_collision(&declared_sort, &sort)
                    {
                        tracing::debug!(
                            var = name,
                            from = ?declared_sort,
                            to = ?sort,
                            "sort upgrade: hashmap-list proof-assert receiver shadowing"
                        );
                        unsoundness::increment(
                            unsoundness::UnsoundnessCategory::PhantomVariableUpgrade,
                        );
                        let new_term = self.declare_derived_source_var(
                            name,
                            "hashmap_list_receiver",
                            sort.clone(),
                        );
                        self.rebind_var(name, new_term, sort);
                        return Ok(new_term);
                    }
                    return Err(EncodingError::sort_conflict(
                        format!("variable '{name}'"),
                        format!("{declared_sort:?}"),
                        format!("{sort:?}"),
                    ));
                }
            }
            return Ok(term);
        }
        let term = self.declare_source_var(name, sort.clone());
        self.rebind_var(name, term, sort);
        let declared_sort = self
            .var_sort(name)
            .cloned()
            .expect("newly declared variable sort should be tracked");
        self.maybe_assert_declared_seq_view_identity(name, term, &declared_sort);
        Ok(term)
    }
}

fn hashmap_list_receiver_sort_collision(existing: &Sort, requested: &Sort) -> bool {
    (sort_mentions_hashmap(existing) && sort_mentions_list(requested))
        || (sort_mentions_list(existing) && sort_mentions_hashmap(requested))
}

fn sort_mentions_hashmap(sort: &Sort) -> bool {
    match sort {
        Sort::Uninterpreted(name) => name.contains("MyHashMap"),
        Sort::Datatype(datatype) => datatype.name.contains("MyHashMap"),
        _ => false,
    }
}

fn sort_mentions_list(sort: &Sort) -> bool {
    match sort {
        Sort::Uninterpreted(name) => name.contains("List"),
        Sort::Datatype(datatype) => datatype.name.contains("List"),
        _ => false,
    }
}
