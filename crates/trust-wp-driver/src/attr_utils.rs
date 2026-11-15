// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Contract attribute extraction utilities
//!
//! Shared functions for extracting contract expressions from HIR attributes.
//! Used by both `callbacks.rs` (contract verification) and `logic.rs` (logic functions).

#![allow(clippy::doc_markdown)]

use rustc_ast::attr::AttributeExt;
use rustc_attr_ir::{Attribute, AttributeKind};
use rustc_span::{Span, Symbol};

/// The span of the whole attribute, for the two shapes a marker takes: a
/// parsed `#[doc = "..."]` and an unparsed tool attribute. rustc keeps no
/// span for every parsed attribute kind, so any other kind has none here.
pub(crate) fn attr_span(attr: &Attribute) -> Option<Span> {
    match attr {
        Attribute::Tool(item) | Attribute::DeriveHelper(item) => Some(item.span),
        Attribute::Parsed(AttributeKind::DocComment { span, .. }) => Some(*span),
        Attribute::Parsed(_) => None,
    }
}

/// Read the string payload of a `#[doc = "..."]` marker.
///
/// The Trust toolchain parses `#[doc = "..."]` into
/// `Attribute::Parsed(AttributeKind::DocComment { .. })`, for which
/// `value_str()` returns `None` (it only reads `Attribute::Tool` and `Attribute::DeriveHelper`
/// key-value attrs) — only `doc_str()` returns the comment. Older / unparsed
/// representations expose it via `value_str()`. Trying `doc_str()` first then
/// `value_str()` makes the contract-marker extraction robust across both, which
/// is what lets `#[doc = "trust-wp:{name}:{contract}"]` markers be found at all
/// on the current toolchain (otherwise every contract silently vanishes →
/// vacuous tier1 passes).
pub(crate) fn doc_marker_str(attr: &Attribute) -> Option<Symbol> {
    attr.doc_str().or_else(|| attr.value_str())
}

/// Get contract expressions embedded in doc attributes.
///
/// Proc-macros embed contracts as `#[doc = "trust-wp:{name}:{contract}"]` to avoid
/// key-value attribute syntax issues with recent Rust nightlies.
pub(crate) fn get_contract_attrs_from_doc(attrs: &[Attribute], name: &str) -> Vec<String> {
    let prefix = format!("trust-wp:{name}:");
    let mut values = Vec::new();

    for attr in attrs {
        // Only check doc attributes (not doc comments)
        if let Some(value) = doc_marker_str(attr) {
            let value_str = value.as_str();
            if value_str.starts_with(&prefix) {
                let contract = &value_str[prefix.len()..];
                if !contract.is_empty() {
                    values.push(contract.to_string());
                }
            }
        }
    }

    values
}

/// Get contract expressions from proc macro attributes.
///
/// When using pass-through proc macros like `#[requires(x > 0)]`, the attribute
/// appears as a parsed attribute with tokenstream arguments. This function
/// extracts the contract text from those attributes.
pub(crate) fn get_contract_attrs_from_proc_macro(attrs: &[Attribute], name: &str) -> Vec<String> {
    use rustc_ast_pretty::pprust;
    use rustc_attr_ir::AttrArgs;

    let mut values = Vec::new();

    for attr in attrs {
        // Skip doc comments
        if attr.is_doc_comment().is_some() {
            continue;
        }

        // Check if this is an unparsed (custom) attribute
        let (Attribute::Tool(item) | Attribute::DeriveHelper(item)) = attr else {
            continue;
        };

        // Check if path matches (single segment like "requires")
        if item.path.segments.len() != 1 {
            continue;
        }

        // Trust: AttrPath.segments is now Box<[Symbol]>; segment is a Symbol directly.
        let seg_name = item.path.segments[0].as_str();
        if seg_name != name {
            continue;
        }

        // Extract the tokenstream content as a string
        if let AttrArgs::Delimited(delim) = &item.args {
            // Use pprust to convert tokens to string
            let contract_text = pprust::tts_to_string(&delim.tokens);
            if !contract_text.is_empty() {
                values.push(contract_text);
            }
        }
    }

    values
}

/// Returns true if `#[check(<mode>)]` is present for the given mode.
///
/// Supports both:
/// - proc-macro doc markers: `#[doc = "trust-wp:check:<mode>"]`
/// - direct proc-macro attributes: `#[check(<mode>)]`
pub(crate) fn has_check_mode(attrs: &[Attribute], mode: &str) -> bool {
    let doc_marker = format!("trust-wp:check:{mode}");
    for attr in attrs {
        if let Some(value) = doc_marker_str(attr) {
            if value.as_str() == doc_marker {
                return true;
            }
        }
    }

    use rustc_ast_pretty::pprust;
    use rustc_attr_ir::AttrArgs;

    for attr in attrs {
        if attr.is_doc_comment().is_some() {
            continue;
        }

        let (Attribute::Tool(item) | Attribute::DeriveHelper(item)) = attr else {
            continue;
        };

        // Trust: AttrPath.segments is now Box<[Symbol]>; segment is a Symbol directly.
        if item.path.segments.len() != 1 || item.path.segments[0].as_str() != "check" {
            continue;
        }

        if let AttrArgs::Delimited(delim) = &item.args {
            let parsed_mode = pprust::tts_to_string(&delim.tokens);
            if parsed_mode.trim() == mode {
                return true;
            }
        }
    }

    false
}

/// Returns true if `#[erasure(...)]` is present.
///
/// The proc macro embeds this as `#[doc = "trust-wp:erasure:{target}"]` so the
/// marker survives expansion and can be queried from rustc callbacks.
pub(crate) fn has_erasure_marker(attrs: &[Attribute]) -> bool {
    attrs
        .iter()
        .filter_map(doc_marker_str)
        .any(|value| value.as_str().starts_with("trust-wp:erasure:"))
}

/// Return all `#[erasure(target)]` targets embedded as doc markers.
pub(crate) fn get_erasure_targets(attrs: &[Attribute]) -> Vec<String> {
    const PREFIX: &str = "trust-wp:erasure:";
    attrs
        .iter()
        .filter_map(doc_marker_str)
        .filter_map(|value| value.as_str().strip_prefix(PREFIX).map(str::to_string))
        .collect()
}

#[cfg(test)]
mod tests {
    // Note: Testing requires rustc internals, so tests are in integration tests
    // See tests/contract_parsing.rs for comprehensive tests of these functions.
}
