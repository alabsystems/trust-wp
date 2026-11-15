// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! ADT declaration and field range constraint state (#1584).
//!
//! Groups the two hash maps used by `match_enc/` for native datatype
//! encoding and field range axiom assertion.

use trust_wp_core::logic::{AdtCtorFieldRanges, AdtDecl, AdtDecls, AdtFieldRanges};

/// ADT declaration and field range state (#1584).
///
/// Stores rustc-backed ADT declarations and per-field range constraints
/// used by the match encoder for native datatype handling.
///
/// All fields private; access through typed methods.
pub(crate) struct AdtState {
    /// Per-ADT field range constraints from Rust type information (#2097).
    field_ranges: AdtFieldRanges,
    /// Rustc-backed ADT declarations (#1982).
    decls: AdtDecls,
}

impl AdtState {
    pub(crate) fn new() -> Self {
        Self {
            field_ranges: AdtFieldRanges::new(),
            decls: AdtDecls::new(),
        }
    }

    /// Set ADT field range constraints (called during verification setup).
    pub(crate) fn set_field_ranges(&mut self, ranges: AdtFieldRanges) {
        self.field_ranges = ranges;
    }

    /// Look up field range constraints for a datatype by name.
    pub(crate) fn field_ranges_for(&self, name: &str) -> Option<&AdtCtorFieldRanges> {
        self.field_ranges.get(name)
    }

    /// Look up an ADT declaration by name (tries full path then bare name).
    pub(crate) fn decl_for_name(&self, name: &str) -> Option<&AdtDecl> {
        let bare = name.rsplit("::").next().unwrap_or(name);
        self.decls
            .get(name)
            .or_else(|| self.decls.get(bare))
            .or_else(|| {
                self.decls.values().find(|decl| {
                    decl.adt_name == name
                        || decl.rust_path == name
                        || decl.adt_name.rsplit("::").next() == Some(bare)
                        || decl.rust_path.rsplit("::").next() == Some(bare)
                })
            })
    }

    /// Insert an ADT declaration if not already present.
    /// The first declaration registered under `name` is kept; a later one
    /// can only mark it as possibly holding a `&mut` (D-126).
    pub(crate) fn insert_decl_if_absent(&mut self, name: String, decl: AdtDecl) {
        let may_hold_a_borrow = decl.may_hold_a_borrow;
        self.decls
            .entry(name)
            .and_modify(|kept| kept.may_hold_a_borrow |= may_hold_a_borrow)
            .or_insert(decl);
    }

    pub(crate) fn decls_iter(&self) -> impl Iterator<Item = &AdtDecl> {
        self.decls.values()
    }
}
