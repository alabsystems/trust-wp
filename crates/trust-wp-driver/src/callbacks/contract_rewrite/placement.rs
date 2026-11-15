// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The one place a named-field pattern's DECLARATION indices are produced.
//!
//! This module is a kernel, and it is small on purpose. Everything in
//! `named_fields` that decides whether a pattern can be placed produces an
//! `Err`; the only thing that can produce a placement is here, and it cannot
//! be called without a [`DeclaredFields`] — a field list rustc copied out of a
//! `VariantDef`.
//!
//! That is the D-31 shape. A code path that GUESSES a field's position when
//! the lookup misses is a false accept, and a doc comment asserting that no
//! such path exists cannot hold that line. Privacy can: [`FieldPlacement`]'s
//! fields are private to this module, so an edit in the rewriting code
//! physically cannot assemble one from a flat field-name map, from source
//! order, or from anything else it has to hand — it must come here and
//! produce a declaration first.

use super::super::struct_field_map::DeclaredFields;

/// Where each source-order field of a named-field constructor belongs.
///
/// There is exactly ONE constructor, [`FieldPlacement::from_declaration`], and
/// it needs a declaration. There is deliberately no second one for `C { .. }`
/// — a pattern that names no field: the parser emits a BARE constructor name
/// with no field list for `C { .. }` (`contract_parser/helpers/patterns.rs`),
/// so such a pattern never carries metadata and never arrives here at all. An
/// exit nothing reaches, in a kernel whose whole value is that its exits are
/// enumerable, is a liability, so the empty case is a refusal instead — see
/// [`Self::from_declaration`].
///
/// The test `placement_kernel_has_exactly_one_placing_constructor` fails if a
/// second constructor appears in this file.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct FieldPlacement {
    /// `indices[i]` is the DECLARATION index of the i-th source-order field.
    indices: Vec<usize>,
    /// The constructor's declared field count.
    arity: usize,
}

impl FieldPlacement {
    /// Place every field a pattern or literal writes at the index `declared`
    /// gives it, or say why this declaration cannot be the one the contract
    /// meant.
    ///
    /// `named` is in SOURCE order and carries no rest marker; `has_rest` says
    /// whether the pattern ended in `..`.
    ///
    /// The returned `Err` is a statement about THIS candidate, not a verdict:
    /// several constructors may answer to one spelling, and the caller tries
    /// each. The caller refuses when none place the fields, or when two place
    /// them differently.
    pub(super) fn from_declaration(
        declared: &DeclaredFields,
        named: &[&str],
        has_rest: bool,
    ) -> Result<Self, String> {
        let names = declared.names();
        if named.is_empty() {
            // Unreachable from the parser: a pattern or literal that names no
            // field is encoded as a BARE constructor name, carries no
            // metadata, and is never placed. Refusing rather than returning an
            // empty placement keeps this function the kernel's only exit that
            // can produce indices, and keeps that exit dependent on a
            // declaration.
            return Err("is written with no field names to place".to_string());
        }
        if !has_rest && names.len() != named.len() {
            // A brace pattern with no `..` binds every declared field.
            return Err(format!(
                "declares {} field(s) where the pattern writes {} and has no `..`",
                names.len(),
                named.len()
            ));
        }
        let mut indices = Vec::with_capacity(named.len());
        for name in named {
            let Some(idx) = names.iter().position(|d| d == name) else {
                return Err(format!("declares no field `{name}`"));
            };
            indices.push(idx);
        }
        // Two source fields at one declaration index would silently drop one
        // of them. `position` cannot return an out-of-range index, so only
        // the duplicate is reachable — from a repeated field name in the
        // contract text, which rustc rejects in any clause it type-checks but
        // which reaches here when the clause was not type-checkable as Rust.
        let mut seen = vec![false; names.len()];
        for &idx in &indices {
            let Some(slot) = seen.get_mut(idx) else {
                return Err("places a field outside its own declared arity".to_string());
            };
            if *slot {
                return Err("is written with two fields in one declared position".to_string());
            }
            *slot = true;
        }
        Ok(Self {
            indices,
            arity: names.len(),
        })
    }

    /// `indices[i]` is the DECLARATION index of the i-th source-order field.
    pub(super) fn indices(&self) -> &[usize] {
        &self.indices
    }

    /// The constructor's declared field count.
    pub(super) fn arity(&self) -> usize {
        self.arity
    }
}
