// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Generalized ground-term pool for E-matching workaround.
//!
//! ay-dpll's single-round E-matching cannot chain quantifier instantiations.
//! This module collects ground function applications observed during encoding
//! and makes them available for targeted ground-instance assertion before
//! `check_sat()`.
//!
//! # Architecture
//!
//! The pool operates at two levels:
//!
//! 1. **SMT level**: tracks `(symbol, Term, Vec<Term>)` tuples for ground UF
//!    applications. Used for matching against trigger patterns.
//!
//! 2. **Encoding level**: tracks `(symbol, Vec<PureExpr>)` for ground function
//!    calls. Used for re-encoding axiom bodies with ground arguments (since
//!    ay-dpll doesn't support SMT-level substitution).
//!
//! # Migration path (from design doc)
//!
//! - Phase 1: Infrastructure + collection wiring (done)
//! - Phase 2: Register existing axioms (done — `register_axiom` + `assert_ground_pool_instances`)
//! - Phase 3: Extend to new axiom families (Seq, type invariants, FSet)
//! - Phase 4: Multi-trigger and cross-axiom chaining
//!
//! Design: `designs/2026-02-15-generalized-ground-term-seeding.md`
//! Issues: #994, #1296, #1603

use std::collections::{HashMap, HashSet};

use ay_dpll::api::{FuncDecl, Sort, Term};
use trust_wp_core::formula::PureExpr;

/// A ground function application observed during encoding.
#[derive(Clone, Debug)]
pub(crate) struct GroundEntry {
    /// The SMT term for the full application `f(a1, ..., an)`.
    pub(crate) application: Term,
    /// The SMT terms for each argument.
    pub(crate) arg_terms: Vec<Term>,
    /// The source-level argument expressions (for re-encoding instantiations).
    pub(crate) arg_exprs: Vec<PureExpr>,
    /// The active branch guards when this application was observed.
    pub(crate) path_conditions: Vec<Term>,
}

/// Distinguishes defining axioms from spec (ensures) axioms for ground
/// instantiation (#1965, Lane 5).
///
/// - `Defining`: produces `f(ground_args) = body_encoded` (equality)
/// - `Spec`: produces `requires(ground_args) =>
///   ensures[params:=ground_args, result:=f(ground_args)]`
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum AxiomKind {
    /// Defining axiom: `∀params. requires => f(params) = body`
    Defining,
    /// Spec axiom (ensures clause): `∀params. requires => ensures[result:=f(params)]`
    Spec,
}

/// A registered quantified axiom whose body can be re-encoded with ground
/// arguments to produce ground instances.
///
/// For a defining axiom `∀params. requires => f(params) = body`:
/// - Re-encodes as `f(ground_args) = body_encoded`, guarded by requires
///
/// For a spec axiom `∀params. requires => ensures[result:=f(params)]`:
/// - Re-encodes as `requires[params:=ground_args] =>
///   ensures[params:=ground_args, result:=f(ground_args)]`
///
/// In both cases:
/// - `fn_symbol` matches against ground entries in the pool
/// - `params` + ground `arg_terms`/`arg_exprs` bind variables for re-encoding
/// - `body` and `requires` are re-encoded via `encode_pure` with ground bindings
#[derive(Clone)]
pub(crate) struct AxiomEntry {
    /// SMT function name (e.g., `"logic_fn_my_fn"`)
    pub(crate) fn_symbol: String,
    /// Parameter names in declaration order (for binding ground args)
    pub(crate) params: Vec<String>,
    /// The PureExpr body of the axiom (to re-encode with ground args)
    pub(crate) body: PureExpr,
    /// Requires clauses (guards for the defining axiom)
    pub(crate) requires: Vec<PureExpr>,
    /// The declared FuncDecl (for `solver.apply` when building `f(ground_args)`)
    pub(crate) func_decl: FuncDecl,
    /// Return sort (for choosing `eq` vs `iff` encoding)
    pub(crate) return_sort: Sort,
    /// Whether this is a defining axiom or a spec (ensures) axiom (#1965)
    pub(crate) kind: AxiomKind,
}

/// Central pool of ground terms observed during encoding, indexed by function
/// symbol for O(1) trigger matching.
///
/// # Usage
///
/// 1. During encoding: call [`register()`](Self::register) for each
///    `MethodCall`/`LogicFnCall`
/// 2. After encoding: call [`register_axiom()`](Self::register_axiom) for each
///    quantified axiom that should be ground-instantiated
/// 3. Query: call [`entries_for()`](Self::entries_for) to get ground terms
///    matching a function symbol
/// 4. Before `check_sat()`: the verification layer uses the pool to assert
///    ground instances of quantified axioms
#[derive(Clone)]
pub(crate) struct GroundTermPool {
    /// fn_symbol -> Vec<GroundEntry>
    by_symbol: HashMap<String, Vec<GroundEntry>>,
    /// Registered axioms awaiting ground instantiation
    axioms: Vec<AxiomEntry>,
    /// Monotonically increasing revision — bumped on every register/register_axiom
    /// and when ground-instantiation policy changes. Used for idempotent
    /// `assert_ground_pool_instances` calls: if the revision hasn't changed
    /// since the last flush, the function is a no-op.
    revision: u64,
    /// The revision at which instances were last asserted. When
    /// `last_asserted_revision == revision`, a flush is a no-op.
    last_asserted_revision: u64,
    /// SMT function symbols that appear in contracts (ensures + requires) (#1296).
    ///
    /// Axioms whose `fn_symbol` is in this set are "critical" — they are
    /// exempted from the `TRUST_WP_MAX_AXIOM_PARAMS_FOR_GROUND` gate and receive
    /// highest priority in the global budget. Without this, contract-
    /// referenced logic functions with >4 parameters or low priority scores
    /// may have their ground instances dropped, causing solver Unknown results.
    ///
    /// The field retains the `postcondition_` prefix for historical reasons
    /// (originally only ensures clauses were scanned). Since #1296, both
    /// ensures and requires clauses contribute to this set.
    postcondition_symbols: HashSet<String>,
    /// Optional obligation-local axiom relevance filter (#2674).
    relevance_symbols: Option<HashSet<String>>,
    /// Optional per-slice override for the total instance budget (#2674).
    per_slice_budget_override: Option<usize>,
}

/// Maximum ground entries per function symbol.
const TRUST_WP_CAP_PER_SYMBOL: usize = 50;

impl Default for GroundTermPool {
    fn default() -> Self {
        Self::new()
    }
}

impl GroundTermPool {
    pub(crate) fn new() -> Self {
        Self {
            by_symbol: HashMap::new(),
            axioms: Vec::new(),
            revision: 0,
            last_asserted_revision: 0,
            postcondition_symbols: HashSet::new(),
            relevance_symbols: None,
            per_slice_budget_override: None,
        }
    }

    /// Register a ground function application observed during encoding.
    ///
    /// `symbol` is the function name (e.g., `"seq_len"`, `"my_logic_fn"`).
    /// `application` is the full SMT term `f(a1, ..., an)`.
    /// `arg_terms` are the individual SMT argument terms.
    /// `arg_exprs` are the source-level argument expressions.
    pub(crate) fn register(
        &mut self,
        symbol: &str,
        application: Term,
        arg_terms: Vec<Term>,
        arg_exprs: Vec<PureExpr>,
    ) {
        self.register_with_path_conditions(symbol, application, arg_terms, arg_exprs, Vec::new());
    }

    pub(crate) fn register_with_path_conditions(
        &mut self,
        symbol: &str,
        application: Term,
        arg_terms: Vec<Term>,
        arg_exprs: Vec<PureExpr>,
        path_conditions: Vec<Term>,
    ) {
        let entries = self.by_symbol.entry(symbol.to_string()).or_default();
        if entries.len() >= TRUST_WP_CAP_PER_SYMBOL {
            return;
        }
        // Deduplicate: skip entries with identical application terms.
        // The same ground application `f(a1, ..., an)` can be registered
        // multiple times from different encoding paths (e.g., once from the
        // precondition and once from the body). Asserting duplicate ground
        // instances wastes solver time without adding information. (#2674)
        if entries.iter().any(|e| e.application == application) {
            return;
        }
        entries.push(GroundEntry {
            application,
            arg_terms,
            arg_exprs,
            path_conditions,
        });
        self.revision = self.revision.saturating_add(1);
    }

    /// Register a term-only ground application (no source-level arg_exprs).
    ///
    /// Used for standard-library UF calls (Seq/FMap/FSet) where the ground
    /// instantiation pass operates at SMT Term level, not PureExpr level.
    /// Term-only entries have empty `arg_exprs` and will not match the
    /// logic-function `assert_ground_pool_instances` path (which filters on
    /// `arg_exprs.len() == axiom.params.len()`). (#2288)
    #[cfg(test)]
    pub(crate) fn register_term_application(
        &mut self,
        symbol: &str,
        application: Term,
        arg_terms: Vec<Term>,
    ) {
        self.register_term_application_with_path_conditions(
            symbol,
            application,
            arg_terms,
            Vec::new(),
        );
    }

    pub(crate) fn register_term_application_with_path_conditions(
        &mut self,
        symbol: &str,
        application: Term,
        arg_terms: Vec<Term>,
        path_conditions: Vec<Term>,
    ) {
        self.register_with_path_conditions(
            symbol,
            application,
            arg_terms,
            Vec::new(),
            path_conditions,
        );
    }

    /// Get ground entries for a given function symbol.
    ///
    /// Returns `None` if no ground terms have been registered for this symbol.
    pub(crate) fn entries_for(&self, symbol: &str) -> Option<&[GroundEntry]> {
        self.by_symbol.get(symbol).map(Vec::as_slice)
    }

    /// Number of registered ground terms across all symbols.
    #[cfg(test)]
    pub(crate) fn ground_term_count(&self) -> usize {
        self.by_symbol.values().map(Vec::len).sum()
    }

    /// Number of distinct function symbols with registered ground terms.
    #[cfg(test)]
    pub(crate) fn symbol_count(&self) -> usize {
        self.by_symbol.len()
    }

    /// Register a quantified axiom for ground instantiation.
    ///
    /// The axiom's `fn_symbol` is matched against ground entries in the pool.
    /// During instantiation (before `check_sat`), matching ground entries are
    /// used to re-encode the axiom body with concrete arguments.
    pub(crate) fn register_axiom(&mut self, axiom: AxiomEntry) {
        self.axioms.push(axiom);
        self.revision = self.revision.saturating_add(1);
    }

    /// Get all registered axioms for ground instantiation.
    ///
    /// Used by invariant body inlining (#726) and test inspection.
    pub(crate) fn axioms(&self) -> &[AxiomEntry] {
        &self.axioms
    }

    /// Number of registered axioms.
    ///
    /// Non-test callers use this for profile instrumentation (#2674 Phase 1).
    pub(crate) fn axiom_count(&self) -> usize {
        self.axioms.len()
    }

    /// Returns `true` if the pool has changed since the last successful flush.
    /// Used to make `assert_ground_pool_instances` idempotent: if no new
    /// entries or axioms have been added, re-flushing is a no-op.
    pub(crate) fn needs_flush(&self) -> bool {
        self.revision != self.last_asserted_revision
    }

    /// Mark the pool as flushed up to the current revision.
    pub(crate) fn mark_flushed(&mut self) {
        self.last_asserted_revision = self.revision;
    }

    /// All registered function symbols.
    #[cfg(test)]
    fn symbols(&self) -> Vec<&str> {
        self.by_symbol.keys().map(String::as_str).collect()
    }

    /// Mark an SMT function symbol as contract-critical (#1296).
    ///
    /// Axioms with this symbol are exempted from the parameter complexity gate
    /// (`TRUST_WP_MAX_AXIOM_PARAMS_FOR_GROUND`) and receive highest priority in the
    /// global instantiation budget. This ensures that logic functions referenced
    /// in contracts (ensures or requires) always get ground instances, even when
    /// they have many parameters or would otherwise be deprioritized by the
    /// budget scoring.
    pub(crate) fn mark_postcondition_symbol(&mut self, symbol: String) {
        if self.postcondition_symbols.insert(symbol) {
            self.revision = self.revision.saturating_add(1);
        }
    }

    /// Check whether a function symbol has been marked as contract-critical.
    pub(crate) fn is_postcondition_symbol(&self, symbol: &str) -> bool {
        self.postcondition_symbols.contains(symbol)
    }

    /// Set or clear the obligation-local axiom relevance filter (#2674).
    pub(crate) fn set_relevance_filter(&mut self, symbols: Option<HashSet<String>>) {
        self.relevance_symbols = symbols;
    }

    /// Clear the obligation-local axiom relevance filter (#2674).
    pub(crate) fn clear_relevance_filter(&mut self) {
        self.relevance_symbols = None;
    }

    /// Override the total ground-instance budget for the current slice (#2674).
    pub(crate) fn set_per_slice_budget(&mut self, budget: Option<usize>) {
        self.per_slice_budget_override = budget;
    }

    /// Return the current per-slice budget override, if any. (#2674)
    pub(crate) fn per_slice_budget(&self) -> Option<usize> {
        self.per_slice_budget_override
    }
}

mod fmap_instances;
mod fset_instances;
mod instantiation;
mod mapping_instances;
pub(crate) mod retirement;
mod seq_instances;

pub(crate) use self::instantiation::TRUST_WP_MAX_CROSS_PRODUCT_INSTANCES;

#[cfg(test)]
mod standard_ground_tests;
#[cfg(test)]
mod tests;
