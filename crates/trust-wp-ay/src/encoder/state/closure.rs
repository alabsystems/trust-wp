// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Closure body inlining state (#1584).
//!
//! Groups the two hash maps used exclusively by `closure_inline.rs`
//! for matching closure receivers to registered body expressions.

use std::collections::HashMap;

use super::super::closure_inline::ClosureBodyInfo;

/// Closure body registration and lookup state (#1584, #2655).
///
/// Stores registered closure bodies (keyed by `def_id`), parameter
/// name → `def_id` mappings for multi-closure disambiguation, and the
/// `closure_mapping_context` flag for Mapping-sorted closure encoding.
///
/// All fields private; access through typed methods.
pub(crate) struct ClosureState {
    /// Registered closure body expressions keyed by def_id (#2151 Phase 2).
    bodies: HashMap<String, ClosureBodyInfo>,
    /// Map from closure parameter names to def_id for body lookup (#2151 Phase 2).
    param_name_map: HashMap<String, String>,
    /// When true, single-parameter closures are encoded as Mapping-sorted
    /// constants with defining axioms instead of unconstrained Bool constants.
    /// Set during logic function body encoding when the function's return sort
    /// is Mapping (Creusot prophetic logic pattern). (#2683, #2655)
    mapping_context: bool,
}

impl ClosureState {
    pub(crate) fn new() -> Self {
        Self {
            bodies: HashMap::new(),
            param_name_map: HashMap::new(),
            mapping_context: false,
        }
    }

    /// Register a param_name → def_id mapping.
    pub(crate) fn insert_param_mapping(&mut self, param_name: String, def_id: String) {
        self.param_name_map.insert(param_name, def_id);
    }

    /// Register a closure body by def_id.
    pub(crate) fn insert_body(&mut self, def_id: String, info: ClosureBodyInfo) {
        self.bodies.insert(def_id, info);
    }

    /// Whether any bodies are registered.
    pub(crate) fn is_empty(&self) -> bool {
        self.bodies.is_empty()
    }

    /// Look up the def_id for a parameter name.
    pub(crate) fn def_id_for_param(&self, param_name: &str) -> Option<&String> {
        self.param_name_map.get(param_name)
    }

    /// Look up a body by def_id.
    pub(crate) fn get_body(&self, def_id: &str) -> Option<&ClosureBodyInfo> {
        self.bodies.get(def_id)
    }

    /// Return the single registered body (when exactly one exists).
    pub(crate) fn single_body(&self) -> Option<&ClosureBodyInfo> {
        if self.bodies.len() == 1 {
            self.bodies.values().next()
        } else {
            None
        }
    }

    /// Iterate over all registered bodies with their def_id keys.
    ///
    /// Used by axiom builders that need to correlate closure bodies with
    /// registered closure struct sorts (keyed by the same def_id). (#2668)
    pub(crate) fn bodies_with_def_ids(&self) -> impl Iterator<Item = (&str, &ClosureBodyInfo)> {
        self.bodies.iter().map(|(k, v)| (k.as_str(), v))
    }

    /// Return the unique closure body that has ensures expressions.
    ///
    /// When multiple closures are registered (e.g., a "real" closure with
    /// user-annotated ensures + a proof_assert lambda), `single_body()`
    /// returns `None` because there are >1 entries. This method filters to
    /// bodies with `ensures_exprs.is_some()` and returns the unique match.
    ///
    /// This enables closure body inlining for Skolem constants from
    /// `postcondition_mut` existentials when proof_assert lambdas are present.
    /// (#2668)
    pub(crate) fn unique_body_with_ensures(&self) -> Option<&ClosureBodyInfo> {
        let mut candidate = None;
        for body in self.bodies.values() {
            if body.ensures_exprs.is_some() {
                if candidate.is_some() {
                    // Ambiguous: more than one closure with ensures
                    return None;
                }
                candidate = Some(body);
            }
        }
        candidate
    }

    // ── Mapping context (#2655, #2683) ────────────────────────────────

    /// Whether closure encoding is in Mapping-sorted context.
    pub(in crate::encoder) fn mapping_context(&self) -> bool {
        self.mapping_context
    }

    /// Set the mapping context flag. Returns the previous value for
    /// save/restore patterns.
    pub(in crate::encoder) fn set_mapping_context(&mut self, enabled: bool) -> bool {
        let prev = self.mapping_context;
        self.mapping_context = enabled;
        prev
    }
}
