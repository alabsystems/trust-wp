// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Contract attribute extraction helpers for logic functions.
//!
//! Extracts `#[requires(...)]`, `#[ensures(...)]`, and `#[variant(...)]` values
//! from both doc-marker and proc-macro attribute representations.

use rustc_hir::Attribute;

use crate::attr_utils::{get_contract_attrs_from_doc, get_contract_attrs_from_proc_macro};

pub(crate) fn extract_requires(attrs: &[Attribute]) -> Vec<String> {
    let mut requires = get_contract_attrs_from_doc(attrs, "requires");
    let proc_requires = get_contract_attrs_from_proc_macro(attrs, "requires");
    if !proc_requires.is_empty() {
        requires.extend(proc_requires);
    }
    requires
}

pub(crate) fn extract_ensures(attrs: &[Attribute]) -> Vec<String> {
    let mut ensures = get_contract_attrs_from_doc(attrs, "ensures");
    let proc_ensures = get_contract_attrs_from_proc_macro(attrs, "ensures");
    if !proc_ensures.is_empty() {
        ensures.extend(proc_ensures);
    }
    ensures
}

pub(crate) fn extract_variants(attrs: &[Attribute]) -> Vec<String> {
    let mut variants = get_contract_attrs_from_doc(attrs, "variant");
    let proc_variants = get_contract_attrs_from_proc_macro(attrs, "variant");
    if !proc_variants.is_empty() {
        variants.extend(proc_variants);
    }
    variants
}

pub(super) fn append_opaque_guard_if_needed(
    requires: &mut Vec<trust_wp_core::formula::PureExpr>,
    is_opaque: bool,
) {
    if is_opaque {
        requires.push(trust_wp_core::formula::PureExpr::Bool(false));
    }
}
