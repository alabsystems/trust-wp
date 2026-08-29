// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{collections::HashMap, rc::Rc};

use ay_dpll::api::{FuncDecl, Term};
use trust_wp_core::formula::Formula;

/// Cached footprints and domain predicates for `SepConj` encoding (#668, #840).
///
/// Extracted from `AYEncoder` to encapsulate the three caching fields used
/// exclusively by `sep_logic.rs`.
///
/// The caches are keyed by a content-derived `FormulaCacheKey` to avoid relying
/// on Formula pointer stability across ownership/refactor changes.
pub(crate) struct SepConjCache {
    /// Cached footprints from `sep_conj` encoding to avoid re-traversal.
    ///
    /// Private; access through `get_footprint()`, `insert_footprint()`. (#1584)
    footprint_cache: HashMap<FormulaCacheKey, Rc<Vec<String>>>,
    /// Counter for generating unique domain predicate names in quantified `sep_conj` encoding.
    ///
    /// Private; access through `next_domain_id()`. (#1584)
    domain_counter: usize,
    /// Cache mapping SepConj formulas to their combined domain predicate + terms.
    ///
    /// Private; access through `get_combined_domain()`, `insert_combined_domain()`. (#1584)
    combined_domain_cache: HashMap<FormulaCacheKey, (FuncDecl, Rc<Vec<Term>>)>,
}

impl SepConjCache {
    pub(crate) fn new() -> Self {
        Self {
            footprint_cache: HashMap::new(),
            domain_counter: 0,
            combined_domain_cache: HashMap::new(),
        }
    }

    /// Look up a cached footprint by formula key, returning an Rc clone (O(1)).
    #[allow(clippy::trivially_copy_pass_by_ref)] // API consistency: callers pass by reference
    pub(in crate::encoder) fn get_footprint(
        &self,
        key: &FormulaCacheKey,
    ) -> Option<Rc<Vec<String>>> {
        self.footprint_cache.get(key).map(Rc::clone)
    }

    /// Cache a footprint for a formula key.
    pub(in crate::encoder) fn insert_footprint(
        &mut self,
        key: FormulaCacheKey,
        footprint: Rc<Vec<String>>,
    ) {
        self.footprint_cache.insert(key, footprint);
    }

    /// Look up a cached combined domain predicate and terms by formula key.
    #[allow(clippy::trivially_copy_pass_by_ref)] // API consistency: callers pass by reference
    pub(in crate::encoder) fn get_combined_domain(
        &self,
        key: &FormulaCacheKey,
    ) -> Option<(FuncDecl, Rc<Vec<Term>>)> {
        self.combined_domain_cache.get(key).cloned()
    }

    /// Cache a combined domain predicate and terms for a formula key.
    pub(in crate::encoder) fn insert_combined_domain(
        &mut self,
        key: FormulaCacheKey,
        value: (FuncDecl, Rc<Vec<Term>>),
    ) {
        self.combined_domain_cache.insert(key, value);
    }

    /// Allocate the next unique domain predicate ID.
    ///
    /// Returns the current counter value and increments it.
    pub(in crate::encoder) fn next_domain_id(&mut self) -> usize {
        let id = self.domain_counter;
        self.domain_counter += 1;
        id
    }
}

/// Stable cache key for Formula-based memoization in separation-logic encoding.
///
/// Uses a structural `u64` hash of the formula's content, eliminating O(N)
/// string allocation per key. Hash collisions are theoretically possible but
/// cryptographically unlikely with `DefaultHasher` (SipHash-1-3).
///
/// Previously used `format!("{formula:?}")` which caused O(N^2) cumulative
/// allocation for left-recursive SepConj chains (#1294).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub(crate) struct FormulaCacheKey(u64);

impl FormulaCacheKey {
    pub(crate) fn for_formula(formula: &Formula) -> Self {
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        formula.hash(&mut hasher);
        Self(hasher.finish())
    }
}
