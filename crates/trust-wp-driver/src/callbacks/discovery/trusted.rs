// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Trusted marker detection.
//!
//! Production detection relies on rustc's attribute API plus ancestor-module
//! propagation. The raw source scanners remain only as debug/test cross-checks
//! so future rustc regressions fail loudly instead of silently changing
//! verification behavior. (#1362)

use std::{fs, path::PathBuf};

use rustc_ast::attr::AttributeExt;
use rustc_attr_ir::{Attribute, AttributeKind};
use rustc_hir::{def::DefKind, def_id::DefId, AttrStyle, Node};
use rustc_middle::ty::TyCtxt;
use rustc_span::{sym, FileName, Span, Symbol};

/// Check if the item is marked trusted.
///
/// The `#[trusted]` proc macro embeds this doc marker because proc macro attributes
/// are consumed during expansion and not visible to tcx.get_all_attrs().
pub(crate) fn has_trusted_marker(tcx: TyCtxt<'_>, def_id: DefId, attrs: &[Attribute]) -> bool {
    let trusted = has_trusted_doc_marker(attrs);
    debug_assert_trusted_marker_consistency(tcx, def_id, trusted);

    // Walk up the module hierarchy: #[trusted] on a module propagates to all
    // child functions. The proc macro attaches `#[doc = "trust-wp:trusted:"]`
    // to the mod item itself, so we check each ancestor module's attributes.
    trusted || has_trusted_ancestor_module(tcx, def_id)
}

/// Whether a trusted item should be rejected under `deny(creusot::trusted_code)`.
///
/// This is a conservative source-level gate: if the file denies the lint and
/// the item does not locally allow it, we reject the trusted item.
pub(super) fn trusted_code_is_denied_for_item(
    tcx: TyCtxt<'_>,
    def_id: DefId,
    attrs: &[Attribute],
) -> bool {
    if !has_trusted_marker(tcx, def_id, attrs) {
        return false;
    }

    let Some(item_source) = source_header_snippet_for_def_id(tcx, def_id) else {
        return false;
    };
    if item_source_contains_allow_trusted_code(&item_source) {
        return false;
    }

    let Some(file_source) = source_text_for_def_span(tcx, tcx.def_span(def_id)) else {
        return false;
    };
    file_source_contains_deny_trusted_code(&file_source)
}

/// Check if any ancestor module of `def_id` carries the `trust-wp:trusted:` marker.
fn has_trusted_ancestor_module(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let mut current = def_id;
    // Walk up parent chain, checking each module for the trusted doc marker.
    loop {
        let Some(parent) = tcx.opt_parent(current) else {
            // Reached the crate root — no trusted ancestor found.
            return false;
        };
        current = parent;
        if tcx.def_kind(current) != DefKind::Mod {
            continue;
        }
        if has_trusted_doc_marker(tcx.get_all_attrs(current)) {
            return true;
        }
    }
}

fn has_trusted_doc_marker(attrs: &[Attribute]) -> bool {
    attrs
        .iter()
        // `get_all_attrs(def_id)` can surface inner `#![doc = "..."]`
        // attributes from trait default bodies. Only outer/header doc markers
        // define item trust.
        .filter_map(outer_doc_value)
        .any(|value| value.as_str().starts_with("trust-wp:trusted:"))
}

fn outer_doc_value(attr: &Attribute) -> Option<Symbol> {
    match attr {
        Attribute::Parsed(AttributeKind::DocComment {
            style: AttrStyle::Outer,
            comment,
            ..
        }) => Some(*comment),
        Attribute::Tool(normal) | Attribute::DeriveHelper(normal)
            if normal.style == AttrStyle::Outer && attr.has_name(sym::doc) =>
        {
            crate::attr_utils::doc_marker_str(attr)
        }
        _ => None,
    }
}

fn source_text_for_def_span(tcx: TyCtxt<'_>, span: Span) -> Option<String> {
    source_path_for_span(tcx, span).and_then(|path| fs::read_to_string(path).ok())
}

fn source_header_snippet_for_def_id(tcx: TyCtxt<'_>, def_id: DefId) -> Option<String> {
    tcx.sess
        .source_map()
        .span_to_snippet(item_source_span(tcx, def_id))
        .ok()
}

fn item_source_span(tcx: TyCtxt<'_>, def_id: DefId) -> Span {
    let Some(local_def_id) = def_id.as_local() else {
        return tcx.def_span(def_id);
    };

    match tcx.hir_node_by_def_id(local_def_id) {
        Node::Item(item) => item.span,
        Node::TraitItem(item) => item.span,
        Node::ImplItem(item) => item.span,
        Node::ForeignItem(item) => item.span,
        Node::Expr(expr) => expr.span,
        _ => tcx.def_span(def_id),
    }
}

fn source_path_for_span(tcx: TyCtxt<'_>, span: Span) -> Option<PathBuf> {
    let loc = tcx.sess.source_map().lookup_char_pos(span.lo());
    match &loc.file.name {
        FileName::Real(real) => real.local_path().map(|path| path.to_path_buf()),
        _ => None,
    }
}

fn file_source_contains_deny_trusted_code(source: &str) -> bool {
    source_contains_inner_lint_attr(source, "deny", "creusot::trusted_code")
        || source_contains_inner_lint_attr(source, "forbid", "creusot::trusted_code")
}

fn item_source_contains_allow_trusted_code(source: &str) -> bool {
    header_source_contains_lint_attr(source, "allow", "creusot::trusted_code")
}

fn source_contains_inner_lint_attr(source: &str, attr_name: &str, lint_name: &str) -> bool {
    let bytes = source.as_bytes();
    let mut i = 0;

    while i + 2 < bytes.len() {
        if bytes[i] == b'#' && bytes[i + 1] == b'!' && bytes[i + 2] == b'[' {
            let Some(attr_end) = find_attribute_end(bytes, i) else {
                return false;
            };
            if attr_text_contains_lint_attr(&source[i..attr_end], true, attr_name, lint_name) {
                return true;
            }
            i = attr_end;
            continue;
        }
        i += 1;
    }

    false
}

fn header_source_contains_lint_attr(source: &str, attr_name: &str, lint_name: &str) -> bool {
    let bytes = source.as_bytes();
    let mut i = 0;

    loop {
        i = skip_header_trivia(bytes, i);
        if i >= bytes.len() {
            return false;
        }

        if i + 1 >= bytes.len() || bytes[i] != b'#' || bytes[i + 1] != b'[' {
            return false;
        }

        let Some(attr_end) = find_attribute_end(bytes, i) else {
            return false;
        };
        if attr_text_contains_lint_attr(&source[i..attr_end], false, attr_name, lint_name) {
            return true;
        }
        i = attr_end;
    }
}

fn attr_text_contains_lint_attr(
    attr_text: &str,
    inner: bool,
    attr_name: &str,
    lint_name: &str,
) -> bool {
    let normalized: String = attr_text
        .chars()
        .filter(|c| !c.is_ascii_whitespace())
        .collect();
    let prefix = if inner {
        format!("#![{attr_name}(")
    } else {
        format!("#[{attr_name}(")
    };
    let Some(args) = normalized.strip_prefix(&prefix) else {
        return false;
    };
    let Some(args) = args.strip_suffix(")]") else {
        return false;
    };

    args.split(',').any(|arg| arg == lint_name)
}

fn find_attribute_end(bytes: &[u8], start: usize) -> Option<usize> {
    if start >= bytes.len() || bytes[start] != b'#' {
        return None;
    }

    let mut i = start + 1;
    if i < bytes.len() && bytes[i] == b'!' {
        i += 1;
    }
    if i >= bytes.len() || bytes[i] != b'[' {
        return None;
    }

    i += 1;
    let mut depth = 1usize;
    while i < bytes.len() && depth > 0 {
        match bytes[i] {
            b'[' => depth += 1,
            b']' => depth -= 1,
            b'"' => {
                i += 1;
                while i < bytes.len() {
                    if bytes[i] == b'\\' {
                        i += 2;
                        continue;
                    }
                    if i < bytes.len() && bytes[i] == b'"' {
                        break;
                    }
                    i += 1;
                }
            }
            _ => {}
        }
        i += 1;
    }

    (depth == 0).then_some(i)
}

fn skip_header_trivia(bytes: &[u8], mut i: usize) -> usize {
    loop {
        i = skip_ws(bytes, i);
        if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'/' {
            i += 2;
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }
        if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'*' {
            i += 2;
            while i + 1 < bytes.len() && !(bytes[i] == b'*' && bytes[i + 1] == b'/') {
                i += 1;
            }
            if i + 1 < bytes.len() {
                i += 2;
            }
            continue;
        }
        return i;
    }
}

#[cfg(debug_assertions)]
fn debug_assert_trusted_marker_consistency(tcx: TyCtxt<'_>, def_id: DefId, trusted: bool) {
    if trusted {
        return;
    }

    if tcx.def_kind(def_id) == DefKind::Closure {
        // Statement attributes like `#[trusted] proof_assert! { ... }` can
        // expand into closures whose source spans still include the enclosing
        // attribute. Closures do not carry item-level trusted attrs via
        // `get_all_attrs()`, so source-sniffing them as if they were item
        // headers produces false positives in this debug-only consistency check.
        return;
    }

    let mut candidates = Vec::new();
    let source_map = tcx.sess.source_map();

    // `def_span` can include outer attributes for associated trait methods in
    // cases where HIR item spans begin at `fn ...` and omit header attrs.
    if let Ok(snippet) = source_map.span_to_snippet(tcx.def_span(def_id)) {
        candidates.push(snippet);
    }

    if let Ok(snippet) = source_map.span_to_snippet(item_source_span(tcx, def_id)) {
        candidates.push(snippet);
    }

    let source_indicates_trusted = candidates.iter().any(|snippet| {
        has_attr_without_args_from_source(snippet, "trusted")
            || has_doc_marker_in_header_source(snippet, "trust-wp:trusted:")
    });

    debug_assert!(
        !source_indicates_trusted,
        "trusted marker present in source but missing from rustc attrs for {}",
        tcx.def_path_str(def_id)
    );
}

#[cfg(not(debug_assertions))]
fn debug_assert_trusted_marker_consistency(_tcx: TyCtxt<'_>, _def_id: DefId, _trusted: bool) {}

/// Scan a source snippet for a zero-argument marker attribute.
///
/// Returns true for `#[trusted]` and `#[trust_wp::trusted]`, but not for
/// argumented forms like `#[trusted(foo)]`.
#[cfg(any(test, debug_assertions))]
pub(super) fn has_attr_without_args_from_source(source: &str, attr_name: &str) -> bool {
    let bytes = source.as_bytes();
    let mut i = 0;

    loop {
        i = skip_ws(bytes, i);
        if i >= bytes.len() {
            return false;
        }

        // Skip line comments (including doc comments) while scanning the item header.
        if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'/' {
            i += 2;
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }

        // Skip block comments while scanning the item header.
        if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'*' {
            i += 2;
            while i + 1 < bytes.len() && !(bytes[i] == b'*' && bytes[i + 1] == b'/') {
                i += 1;
            }
            if i + 1 < bytes.len() {
                i += 2;
            }
            continue;
        }

        // Once we reach non-comment, non-attribute tokens (e.g., `fn`), stop.
        if i + 1 >= bytes.len() || bytes[i] != b'#' || bytes[i + 1] != b'[' {
            return false;
        }

        let mut j = skip_ws(bytes, i + 2);

        let mut last_segment = None;
        loop {
            let seg_start = j;
            while j < bytes.len() && (bytes[j].is_ascii_alphanumeric() || bytes[j] == b'_') {
                j += 1;
            }
            if seg_start == j {
                break;
            }
            last_segment = Some(&source[seg_start..j]);
            j = skip_ws(bytes, j);
            if j + 1 < bytes.len() && bytes[j] == b':' && bytes[j + 1] == b':' {
                j += 2;
                j = skip_ws(bytes, j);
                continue;
            }
            break;
        }

        let Some(last_segment) = last_segment else {
            i += 2;
            continue;
        };
        j = skip_ws(bytes, j);

        if j < bytes.len() && bytes[j] == b']' && last_segment == attr_name {
            return true;
        }

        // Skip the current attribute and continue scanning subsequent header attrs.
        while j < bytes.len() && bytes[j] != b']' {
            j += 1;
        }
        if j < bytes.len() {
            i = j + 1;
        } else {
            return false;
        }
    }
}

/// Scan source for a doc marker embedded in header attributes.
///
/// This is used as a trusted fallback when proc-macro expansion has rewritten
/// `#[trusted]` into `#[doc = "trust-wp:trusted:"]` on trait methods.
#[cfg(any(test, debug_assertions))]
pub(super) fn has_doc_marker_in_header_source(source: &str, marker: &str) -> bool {
    let bytes = source.as_bytes();
    let mut i = 0;

    loop {
        i = skip_ws(bytes, i);
        if i >= bytes.len() {
            return false;
        }

        // Skip line comments while scanning the item header.
        if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'/' {
            i += 2;
            while i < bytes.len() && bytes[i] != b'\n' {
                i += 1;
            }
            continue;
        }

        // Skip block comments while scanning the item header.
        if i + 1 < bytes.len() && bytes[i] == b'/' && bytes[i + 1] == b'*' {
            i += 2;
            while i + 1 < bytes.len() && !(bytes[i] == b'*' && bytes[i + 1] == b'/') {
                i += 1;
            }
            if i + 1 < bytes.len() {
                i += 2;
            }
            continue;
        }

        // Once we reach non-comment, non-attribute tokens (e.g., `fn`), stop.
        if i + 1 >= bytes.len() || bytes[i] != b'#' || bytes[i + 1] != b'[' {
            return false;
        }

        let attr_start = i;
        i += 2;
        let mut depth = 1usize;

        while i < bytes.len() && depth > 0 {
            match bytes[i] {
                b'[' => depth += 1,
                b']' => depth -= 1,
                b'"' => {
                    // Skip string literal content (handle escapes) so nested
                    // brackets inside strings do not affect attribute depth.
                    i += 1;
                    while i < bytes.len() {
                        if bytes[i] == b'\\' {
                            i += 2;
                            continue;
                        }
                        if bytes[i] == b'"' {
                            break;
                        }
                        i += 1;
                    }
                }
                _ => {}
            }
            i += 1;
        }

        if depth != 0 {
            return false;
        }

        if source[attr_start..i].contains(marker) {
            return true;
        }
    }
}

fn skip_ws(bytes: &[u8], mut i: usize) -> usize {
    while i < bytes.len() && bytes[i].is_ascii_whitespace() {
        i += 1;
    }
    i
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn file_source_detects_trusted_code_deny() {
        let source = "#![deny(creusot::trusted_code)]\nfn f() {}";
        assert!(file_source_contains_deny_trusted_code(source));
    }

    #[test]
    fn file_source_detects_trusted_code_deny_with_multiple_lints() {
        let source = "#![deny(unused, creusot::trusted_code)]\nfn f() {}";
        assert!(file_source_contains_deny_trusted_code(source));
    }

    #[test]
    fn file_source_detects_trusted_code_forbid() {
        let source = "#![forbid(creusot::trusted_code, unused)]\nfn f() {}";
        assert!(file_source_contains_deny_trusted_code(source));
    }

    #[test]
    fn item_source_detects_trusted_code_allow() {
        let source = "#[allow(creusot::trusted_code)]\nfn f() {}";
        assert!(item_source_contains_allow_trusted_code(source));
    }

    #[test]
    fn item_source_detects_trusted_code_allow_after_other_lints() {
        let source = "#[allow(unused, creusot::trusted_code)]\nfn f() {}";
        assert!(item_source_contains_allow_trusted_code(source));
    }

    #[test]
    fn item_source_ignores_unrelated_allows() {
        let source = "#[allow(dead_code)]\nfn f() {}";
        assert!(!item_source_contains_allow_trusted_code(source));
    }
}
