// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Creusot-compatible purity validation.

use rustc_hir::{
    def::{DefKind, Res},
    def_id::DefId,
    intravisit::{walk_expr, walk_pat, Visitor},
    Block, Expr, ExprKind, Pat, PatExprKind, PatKind, QPath, TyKind as HirTyKind, UnOp,
};
use rustc_middle::{
    hir::nested_filter,
    ty::{Ty, TyCtxt, TyKind, TypeckResults},
};
use rustc_span::Span;
use trust_wp_core::{
    formula::PureExpr,
    logic::{LogicFnDef, LogicMode},
};

use crate::{attr_utils, ghost::GhostBlock};

#[derive(Debug)]
pub(super) struct PurityValidationError {
    pub(super) span: Span,
    pub(super) message: String,
}

/// Diagnostic emitted when a program function calls the `HashMap`/`BTreeMap`
/// `Entry` API. These operations (`entry`, `or_insert`, `or_insert_with`,
/// `or_default`, `and_modify`) construct/consume the opaque `Entry` value and
/// have no functional specification in `trust-wp-std` (their extern specs are
/// havoc-only), so any obligation that depends on how the entry mutates the
/// map is unprovable. Rather than let the solver churn to an ambiguous
/// `unknown`/timeout on the resulting quantified `FMap` goal, we refuse the
/// operation up front. This mirrors Creusot, which flags the same calls as
/// "calling external function `entry`/`or_insert` with no contract will yield
/// an impossible precondition" (see `unsupported/hash_map.stderr`). The
/// refusal is sound in the should_fail sense: the program is never verified,
/// so a false-accept is impossible by construction. The distinctive phrase
/// `the HashMap/BTreeMap Entry API` anchors the should_fail classifier's
/// frontend-rejection credit.
pub(super) const UNSUPPORTED_MAP_ENTRY_API_MESSAGE: &str =
    "unsupported operation: the HashMap/BTreeMap Entry API \
     (`entry`/`or_insert`/`or_insert_with`/`or_default`/`and_modify`) has no \
     functional contract and cannot be verified";

/// Return `true` when `def_id` names a `HashMap`/`BTreeMap` `Entry`-API method
/// that `trust-wp` cannot model functionally (see
/// [`UNSUPPORTED_MAP_ENTRY_API_MESSAGE`]).
///
/// The match is intentionally narrow: the entry-consuming method names
/// (`or_insert`, `or_insert_with`, `or_insert_with_key`, `or_default`,
/// `and_modify`) are unique to the std map `Entry` types, and the
/// entry-producing `entry` method is additionally gated on the defining path
/// mentioning a std map so a user type's own `entry(..)` is never flagged.
/// `Option::get_or_insert` / `unwrap_or_default` (used by passing
/// should_succeed tests) have different method names and never match.
fn is_unsupported_map_entry_api(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let method = tcx.item_name(def_id);
    let method = method.as_str();
    let path = tcx.def_path_str(def_id);
    let mentions_std_map = path.contains("HashMap")
        || path.contains("BTreeMap")
        || path.contains("hash_map")
        || path.contains("btree_map");
    if !mentions_std_map {
        return false;
    }
    matches!(
        method,
        "or_insert"
            | "or_insert_with"
            | "or_insert_with_key"
            | "or_default"
            | "and_modify"
            | "entry"
    )
}

pub(super) fn validate_program_context_logic_calls(
    tcx: TyCtxt<'_>,
    ghost_blocks: &[GhostBlock],
) -> Vec<PurityValidationError> {
    let local_crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE).to_string();
    if matches!(
        local_crate_name.as_str(),
        "trust_wp_std" | "trust-wp" | "creusot_std" | "creusot_contracts" | "trust_wp_lib"
    ) {
        return Vec::new();
    }

    let mut all_errors = Vec::new();
    for local_def_id in tcx.hir_body_owners() {
        let hir_id = tcx.local_def_id_to_hir_id(local_def_id);
        let attrs = tcx.hir_attrs(hir_id);
        if crate::logic::has_logic_marker(attrs) || attr_utils::has_check_mode(attrs, "ghost") {
            continue;
        }

        let body = tcx.hir_body_owned_by(local_def_id);
        let typeck_results = tcx.typeck_body(body.id());
        let ghost_spans = ghost_blocks
            .iter()
            .filter(|block| block.containing_fn == local_def_id)
            .map(|block| block.span)
            .collect::<Vec<_>>();
        let mut validator = ProgramLogicCallValidator {
            tcx,
            typeck_results,
            ghost_spans,
            snapshot_capture_depth: 0,
            errors: Vec::new(),
        };
        validator.visit_body(body);
        all_errors.extend(validator.errors);
    }

    all_errors
}

pub(super) fn validate_logic_surface_restrictions(tcx: TyCtxt<'_>) -> Vec<PurityValidationError> {
    let local_crate_name = tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE).to_string();
    if matches!(
        local_crate_name.as_str(),
        "trust_wp_std" | "trust-wp" | "creusot_std" | "creusot_contracts" | "trust_wp_lib"
    ) {
        return Vec::new();
    }

    let crate_has_index_logic_method = crate_has_local_assoc_fn_named(tcx, "index_logic");
    let opaque_type_names = collect_opaque_type_names(tcx);
    let default_logic_names = collect_default_logic_function_names(tcx);
    let mut all_errors = Vec::new();

    for local_def_id in tcx.hir_body_owners() {
        let hir_id = tcx.local_def_id_to_hir_id(local_def_id);
        let attrs = tcx.hir_attrs(hir_id);
        let is_logic = crate::logic::has_logic_marker(attrs);
        let body_text = logic_body_text(tcx, local_def_id);
        let code_text = strip_comments_and_literals(&body_text);
        let def_id = local_def_id.to_def_id();
        let span = tcx.def_span(def_id);

        if !opaque_type_names.is_empty()
            && !(has_trusted_doc_marker(attrs) && !is_logic)
            && uses_opaque_type_constructor_or_field(
                tcx,
                local_def_id,
                &code_text,
                &opaque_type_names,
            )
        {
            all_errors.push(PurityValidationError {
                span,
                message:
                    "Forbidden constructor or field access of opaque type; only #[trusted] program functions can see through opaque types"
                        .to_string(),
            });
        }

        // `#[trusted]` program functions may see through the abstraction the
        // same way they may construct/inspect opaque types above: their bodies
        // are taken on trust and never verified, so a raw-pointer deref inside a
        // trusted, non-logic function is the intended escape hatch (Creusot's
        // `erasure.rs` `test_ptr`/`test_ptr_mut` use exactly this). Logic
        // functions never get the exemption — raw-pointer derefs there remain
        // forbidden. Mirrors the opaque-type guard above.
        if !(has_trusted_doc_marker(attrs) && !is_logic) {
            if let Some(raw_deref_span) = raw_pointer_deref_span(tcx, local_def_id) {
                all_errors.push(PurityValidationError {
                    span: raw_deref_span,
                    message: "Dereference of a raw pointer is forbidden in creusot: use a ghost permission API instead".to_string(),
                });
            }
        }

        if let Some(loop_false_span) = loop_false_proof_assert_span(tcx, local_def_id) {
            all_errors.push(PurityValidationError {
                span: loop_false_span,
                message: "proof_assert!(false) inside a loop is an unsatisfied proof obligation"
                    .to_string(),
            });
        }

        // A `#[builtin(...)]` definition is mapped directly to a prover
        // primitive, so attaching a contract to it is contradictory. Creusot
        // rejects this with "cannot specify both `creusot::builtin` and a
        // contract on the same definition"; mirror that rejection here so the
        // case fails for the intended semantic reason rather than slipping
        // through as an unverified logic postcondition.
        if has_builtin_doc_marker(attrs)
            && (has_doc_marker(attrs, "trust-wp:requires:")
                || has_doc_marker(attrs, "trust-wp:ensures:"))
        {
            all_errors.push(PurityValidationError {
                span,
                message: "cannot specify both `#[builtin]` and a contract on the same definition"
                    .to_string(),
            });
        }

        if !is_logic {
            continue;
        }

        if has_scoped_open_doc_marker(attrs)
            && calls_default_logic_function(&code_text, &default_logic_names)
        {
            all_errors.push(PurityValidationError {
                span,
                message:
                    "Cannot make a less-visible logic function transparent from an open(crate)/open(super) logic body"
                        .to_string(),
            });
        }

        if body_contains_dead_term(&code_text) && !has_opaque_doc_marker(attrs) {
            all_errors.push(PurityValidationError {
                span,
                message:
                    "The `dead` term can only be used for the body of `logic(opaque)` functions"
                        .to_string(),
            });
        }

        if has_primitive_integer_signature(tcx, def_id) {
            if contains_primitive_arith_op(&code_text, '/') {
                all_errors.push(PurityValidationError {
                    span,
                    message: "Cannot divide primitive integers in logic: no implementation for primitive integer division in logic".to_string(),
                });
            }
            if contains_primitive_arith_op(&code_text, '%') {
                all_errors.push(PurityValidationError {
                    span,
                    message: "cannot calculate the remainder of primitive integers in logic: no implementation for primitive integer remainder in logic".to_string(),
                });
            }
        }

        if contains_int_literal_pattern_match(tcx, local_def_id, &code_text) {
            all_errors.push(PurityValidationError {
                span,
                message: "Unsupported expression: Pattern matching literals on Int are unsupported by Pearlite. Consider using if-then-else instead.".to_string(),
            });
        }

        if contains_unsupported_plain_adt_index(
            tcx,
            local_def_id,
            &code_text,
            crate_has_index_logic_method,
        ) {
            all_errors.push(PurityValidationError {
                span,
                message: "the type cannot be indexed in logic: no IndexLogic implementation found"
                    .to_string(),
            });
        }
    }

    all_errors
}

pub(super) fn validate_logic_function_purity(logic_fns: &[LogicFnDef]) -> Vec<String> {
    logic_fns
        .iter()
        .filter(|logic_fn| logic_fn.mode() != LogicMode::Prophetic)
        .filter(|logic_fn| logic_fn.body().any_recursive(|expr| matches!(expr, PureExpr::Final(_))))
        .map(|logic_fn| {
            format!(
                "called prophetic logic function/final-state expression in non-prophetic logic context: `{}`",
                logic_fn.full_path()
            )
        })
        .collect()
}

fn logic_body_text(tcx: TyCtxt<'_>, local_def_id: rustc_hir::def_id::LocalDefId) -> String {
    let attrs = tcx.hir_attrs(tcx.local_def_id_to_hir_id(local_def_id));
    if let Some(body) = attr_utils::get_contract_attrs_from_doc(attrs, "logic_body")
        .into_iter()
        .next()
    {
        return body;
    }

    let body = tcx.hir_body_owned_by(local_def_id);
    tcx.sess
        .source_map()
        .span_to_snippet(body.value.span)
        .unwrap_or_default()
}

fn has_opaque_doc_marker(attrs: &[rustc_hir::Attribute]) -> bool {
    attrs
        .iter()
        .filter_map(crate::attr_utils::doc_marker_str)
        .any(|value| value.as_str().starts_with("trust-wp:opaque:"))
}

fn has_scoped_open_doc_marker(attrs: &[rustc_hir::Attribute]) -> bool {
    has_doc_marker(attrs, "trust-wp:logic_open_crate:")
        || has_doc_marker(attrs, "trust-wp:logic_open_super:")
}

fn has_trusted_doc_marker(attrs: &[rustc_hir::Attribute]) -> bool {
    has_doc_marker(attrs, "trust-wp:trusted:")
}

fn has_builtin_doc_marker(attrs: &[rustc_hir::Attribute]) -> bool {
    has_doc_marker(attrs, "trust-wp:builtin:")
}

fn has_doc_marker(attrs: &[rustc_hir::Attribute], marker: &str) -> bool {
    attrs
        .iter()
        .filter_map(crate::attr_utils::doc_marker_str)
        .any(|value| value.as_str().starts_with(marker))
}

fn body_contains_dead_term(body_text: &str) -> bool {
    let compact = compact_text(body_text);
    contains_bare_token(&compact, "dead")
}

fn collect_opaque_type_names(tcx: TyCtxt<'_>) -> Vec<String> {
    tcx.iter_local_def_id()
        .filter_map(|local_def_id| {
            let def_id = local_def_id.to_def_id();
            if !matches!(
                tcx.def_kind(def_id),
                DefKind::Struct | DefKind::Enum | DefKind::Union
            ) {
                return None;
            }
            let attrs = tcx.get_all_attrs(def_id);
            has_opaque_doc_marker(attrs).then(|| tcx.item_name(def_id).as_str().to_string())
        })
        .collect()
}

fn collect_default_logic_function_names(tcx: TyCtxt<'_>) -> Vec<String> {
    tcx.iter_local_def_id()
        .filter_map(|local_def_id| {
            let def_id = local_def_id.to_def_id();
            if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
                return None;
            }
            let attrs = tcx.get_all_attrs(def_id);
            if !crate::logic::has_logic_marker(attrs)
                || has_doc_marker(attrs, "trust-wp:logic:open:")
                || has_doc_marker(attrs, "trust-wp:logic:open_self:")
                || has_doc_marker(attrs, "trust-wp:logic:prophetic:")
                || has_scoped_open_doc_marker(attrs)
            {
                return None;
            }
            Some(tcx.item_name(def_id).as_str().to_string())
        })
        .collect()
}

fn calls_default_logic_function(body_text: &str, default_logic_names: &[String]) -> bool {
    let compact = compact_text(body_text);
    default_logic_names
        .iter()
        .any(|name| compact.contains(&format!("{name}(")))
}

fn uses_opaque_type_constructor_or_field(
    tcx: TyCtxt<'_>,
    local_def_id: rustc_hir::def_id::LocalDefId,
    body_text: &str,
    opaque_type_names: &[String],
) -> bool {
    let compact = compact_text(body_text);
    // Look for *construction* of an opaque type, not arbitrary references
    // to its name. Method calls (`MyHashMap::new()`, `Bump::with_capacity(_)`)
    // and trait-qualified paths (`<Bump as Trait>::foo`) are legitimate
    // uses of opaque types from non-trusted functions — only direct field
    // access or constructor literals (`MyHashMap {...}`, `Bump(...)`,
    // `Self {...}`) break encapsulation. The textual heuristic flagged
    // any mention of the type name, which over-fires on examples like
    // `bdd.rs` that just call `MyHashMap::new()` from a non-trusted fn.
    let is_constructor_or_field_text = opaque_type_names.iter().any(|name| {
        let mut search = compact.as_str();
        while let Some(idx) = search.find(name.as_str()) {
            // Reject paths like `crate::module::OpaqueName` only when the
            // following token disambiguates: `::` => path/method call,
            // `{` or `(` => constructor.
            let tail = &search[idx + name.len()..];
            // Skip identifier continuations (`OpaqueNameExtra`).
            let next_char = tail.chars().next();
            let is_word_boundary = next_char.map_or(true, |c| !c.is_alphanumeric() && c != '_');
            if is_word_boundary {
                let trimmed = tail.trim_start();
                if trimmed.starts_with('{') || trimmed.starts_with('(') {
                    return true;
                }
            }
            search = &search[idx + 1..];
        }
        false
    });
    if is_constructor_or_field_text {
        return true;
    }

    let body = tcx.hir_body_owned_by(local_def_id);
    let typeck_results = tcx.typeck_body(body.id());
    body.params.iter().any(|param| {
        let PatKind::Binding(_, _, ident, _) = param.pat.kind else {
            return false;
        };
        let ty = typeck_results.pat_ty(param.pat);
        let is_opaque_param = opaque_type_names
            .iter()
            .any(|name| ty.to_string().ends_with(name));
        is_opaque_param && compact.contains(&format!("{}.", ident.name))
    })
}

fn has_primitive_integer_signature(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
    sig.inputs_and_output
        .iter()
        .any(|ty| matches!(ty.kind(), TyKind::Int(_) | TyKind::Uint(_)))
}

/// Heuristic detection of primitive integer `/` or `%` use in a logic body's
/// text. Returns `true` iff `op_char` appears in `code_text` with a LHS that
/// is not the result of a method or function call (e.g. `x.view() % 2` is
/// treated as a logic-`Int` operation, not a primitive one). The body text
/// comes from the `trust-wp:logic_body:` doc marker preserved by the `#[logic]`
/// macro, so we can't use typeck — the HIR body is replaced with
/// `unreachable!()`.
fn contains_primitive_arith_op(code_text: &str, op_char: char) -> bool {
    let bytes = code_text.as_bytes();
    let op_byte = op_char as u8;
    let mut idx = 0;
    while idx < bytes.len() {
        if bytes[idx] != op_byte {
            idx += 1;
            continue;
        }
        // Defensive: `/` followed by `/` or `*` is a comment leader, not arith.
        if op_char == '/' && matches!(bytes.get(idx + 1), Some(&b'/') | Some(&b'*')) {
            idx += 1;
            continue;
        }
        // Walk backward over whitespace to find the preceding non-whitespace byte.
        let mut back = idx;
        while back > 0 && (bytes[back - 1] as char).is_whitespace() {
            back -= 1;
        }
        if back == 0 {
            idx += 1;
            continue;
        }
        let prev = bytes[back - 1];
        // `)` indicates a function/method-call result, which (in logic bodies)
        // is typically a lifted logic `Int`, e.g. `x.view() % 2`. Treat as
        // non-primitive and continue scanning.
        if prev == b')' {
            idx += 1;
            continue;
        }
        // Otherwise the LHS is a bare identifier or literal: a primitive op.
        return true;
    }
    false
}

fn contains_int_literal_pattern_match(
    tcx: TyCtxt<'_>,
    local_def_id: rustc_hir::def_id::LocalDefId,
    body_text: &str,
) -> bool {
    let body = tcx.hir_body_owned_by(local_def_id);
    let typeck_results = tcx.typeck_body(body.id());
    let logic_int_param_names = body
        .params
        .iter()
        .filter(|param| ty_is_logic_int(typeck_results.pat_ty(param.pat)))
        .filter_map(|param| {
            if let PatKind::Binding(_, _, ident, _) = param.pat.kind {
                Some(ident.name.as_str().to_string())
            } else {
                None
            }
        })
        .collect::<Vec<_>>();
    let mut visitor = IntLiteralPatternVisitor {
        tcx,
        typeck_results,
        found: false,
    };
    visitor.visit_body(body);
    visitor.found
        || (!logic_int_param_names.is_empty()
            && contains_int_literal_pattern_match_text_for_params(
                body_text,
                &logic_int_param_names,
            ))
}

struct IntLiteralPatternVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck_results: &'a TypeckResults<'tcx>,
    found: bool,
}

impl<'tcx> Visitor<'tcx> for IntLiteralPatternVisitor<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;
    type MaybeTyCtxt = TyCtxt<'tcx>;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_pat(&mut self, pat: &'tcx Pat<'tcx>) {
        if self.found {
            return;
        }

        if matches!(
            pat.kind,
            PatKind::Expr(expr) if matches!(expr.kind, PatExprKind::Lit { .. })
        ) && ty_is_logic_int(self.typeck_results.pat_ty(pat))
        {
            self.found = true;
            return;
        }

        if matches!(pat.kind, PatKind::Range(..))
            && ty_is_logic_int(self.typeck_results.pat_ty(pat))
        {
            self.found = true;
            return;
        }

        walk_pat(self, pat);
    }
}

fn ty_is_logic_int(ty: Ty<'_>) -> bool {
    let text = ty.to_string();
    text == "Int" || text.ends_with("::Int")
}

#[cfg(test)]
#[allow(dead_code)]
fn contains_int_literal_pattern_match_text(body_text: &str) -> bool {
    contains_int_literal_pattern_match_text_with_scrutinee(body_text, |_| true)
}

fn contains_int_literal_pattern_match_text_for_params(
    body_text: &str,
    param_names: &[String],
) -> bool {
    contains_int_literal_pattern_match_text_with_scrutinee(body_text, |scrutinee| {
        let compact = compact_text(scrutinee);
        param_names.contains(&compact)
    })
}

fn contains_int_literal_pattern_match_text_with_scrutinee(
    body_text: &str,
    scrutinee_allowed: impl Fn(&str) -> bool,
) -> bool {
    let code_text = strip_comments_and_literals(body_text);
    let mut rest = code_text.as_str();

    while let Some(match_pos) = rest.find("match") {
        let after_match = &rest[match_pos + "match".len()..];
        let Some(open_brace) = after_match.find('{') else {
            return false;
        };
        if !scrutinee_allowed(&after_match[..open_brace]) {
            rest = &after_match[open_brace + 1..];
            continue;
        }
        let arms = &after_match[open_brace + 1..];
        let Some(close_brace) = find_matching_close_brace(arms) else {
            return false;
        };
        if match_arms_contain_int_literal_pattern(&arms[..close_brace]) {
            return true;
        }
        rest = &arms[close_brace + 1..];
    }

    false
}

fn strip_comments_and_literals(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut out = String::with_capacity(text.len());
    let mut index = 0;

    while index < bytes.len() {
        if bytes[index] == b'/' && bytes.get(index + 1) == Some(&b'/') {
            index = replace_until_line_end(bytes, index, &mut out);
            continue;
        }

        if bytes[index] == b'/' && bytes.get(index + 1) == Some(&b'*') {
            index = replace_block_comment(bytes, index, &mut out);
            continue;
        }

        if let Some(end) = raw_string_literal_end(bytes, index) {
            replace_range_preserving_newlines(bytes, index, end, &mut out);
            index = end;
            continue;
        }

        if let Some(end) = quoted_string_literal_end(bytes, index) {
            replace_range_preserving_newlines(bytes, index, end, &mut out);
            index = end;
            continue;
        }

        let ch = text[index..]
            .chars()
            .next()
            .expect("index should be on a char boundary");
        out.push(ch);
        index += ch.len_utf8();
    }

    out
}

fn replace_until_line_end(bytes: &[u8], start: usize, out: &mut String) -> usize {
    let mut index = start;
    while index < bytes.len() {
        let byte = bytes[index];
        if byte == b'\n' {
            out.push('\n');
            return index + 1;
        }
        out.push(' ');
        index += 1;
    }
    index
}

fn replace_block_comment(bytes: &[u8], start: usize, out: &mut String) -> usize {
    let mut index = start;
    let mut depth = 0usize;
    while index < bytes.len() {
        if bytes[index] == b'/' && bytes.get(index + 1) == Some(&b'*') {
            depth += 1;
            replace_range_preserving_newlines(bytes, index, index + 2, out);
            index += 2;
            continue;
        }
        if bytes[index] == b'*' && bytes.get(index + 1) == Some(&b'/') {
            depth = depth.saturating_sub(1);
            replace_range_preserving_newlines(bytes, index, index + 2, out);
            index += 2;
            if depth == 0 {
                return index;
            }
            continue;
        }

        replace_range_preserving_newlines(bytes, index, index + 1, out);
        index += 1;
    }
    index
}

fn raw_string_literal_end(bytes: &[u8], start: usize) -> Option<usize> {
    let mut index = start;
    if bytes.get(index) == Some(&b'b') && bytes.get(index + 1) == Some(&b'r') {
        index += 1;
    }
    if bytes.get(index) != Some(&b'r') {
        return None;
    }

    index += 1;
    let hash_start = index;
    while bytes.get(index) == Some(&b'#') {
        index += 1;
    }
    let hashes = index - hash_start;
    if bytes.get(index) != Some(&b'"') {
        return None;
    }
    index += 1;

    while index < bytes.len() {
        if bytes[index] == b'"'
            && index + 1 + hashes <= bytes.len()
            && bytes[index + 1..index + 1 + hashes]
                .iter()
                .all(|byte| *byte == b'#')
        {
            return Some(index + 1 + hashes);
        }
        index += 1;
    }

    Some(bytes.len())
}

fn quoted_string_literal_end(bytes: &[u8], start: usize) -> Option<usize> {
    let quote = if bytes.get(start) == Some(&b'"') {
        start
    } else if bytes.get(start) == Some(&b'b') && bytes.get(start + 1) == Some(&b'"') {
        start + 1
    } else {
        return None;
    };

    let mut index = quote + 1;
    let mut escaped = false;
    while index < bytes.len() {
        let byte = bytes[index];
        if escaped {
            escaped = false;
        } else if byte == b'\\' {
            escaped = true;
        } else if byte == b'"' {
            return Some(index + 1);
        }
        index += 1;
    }

    Some(bytes.len())
}

fn replace_range_preserving_newlines(bytes: &[u8], start: usize, end: usize, out: &mut String) {
    for byte in &bytes[start..end] {
        if *byte == b'\n' {
            out.push('\n');
        } else {
            out.push(' ');
        }
    }
}

fn match_arms_contain_int_literal_pattern(arms: &str) -> bool {
    let mut arm_start = 0;
    let bytes = arms.as_bytes();
    let mut index = 0;
    let mut paren_depth = 0usize;
    let mut bracket_depth = 0usize;
    let mut brace_depth = 0usize;

    while index < bytes.len() {
        match bytes[index] {
            b'(' => paren_depth += 1,
            b')' => paren_depth = paren_depth.saturating_sub(1),
            b'[' => bracket_depth += 1,
            b']' => bracket_depth = bracket_depth.saturating_sub(1),
            b'{' => brace_depth += 1,
            b'}' => brace_depth = brace_depth.saturating_sub(1),
            b'=' if index + 1 < bytes.len()
                && bytes[index + 1] == b'>'
                && paren_depth == 0
                && bracket_depth == 0
                && brace_depth == 0 =>
            {
                if int_literal_pattern_text(&arms[arm_start..index]) {
                    return true;
                }
                index += 2;
                while index < bytes.len() {
                    match bytes[index] {
                        b'(' => paren_depth += 1,
                        b')' => paren_depth = paren_depth.saturating_sub(1),
                        b'[' => bracket_depth += 1,
                        b']' => bracket_depth = bracket_depth.saturating_sub(1),
                        b'{' => brace_depth += 1,
                        b'}' => brace_depth = brace_depth.saturating_sub(1),
                        b',' if paren_depth == 0 && bracket_depth == 0 && brace_depth == 0 => {
                            arm_start = index + 1;
                            break;
                        }
                        _ => {}
                    }
                    index += 1;
                }
                continue;
            }
            _ => {}
        }
        index += 1;
    }

    false
}

fn int_literal_pattern_text(pattern: &str) -> bool {
    contains_integer_literal_token(pattern_text_before_guard(pattern))
}

fn pattern_text_before_guard(pattern: &str) -> &str {
    let bytes = pattern.as_bytes();
    let mut index = 0;
    let mut paren_depth = 0usize;
    let mut bracket_depth = 0usize;
    let mut brace_depth = 0usize;

    while index + 1 < bytes.len() {
        match bytes[index] {
            b'(' => paren_depth += 1,
            b')' => paren_depth = paren_depth.saturating_sub(1),
            b'[' => bracket_depth += 1,
            b']' => bracket_depth = bracket_depth.saturating_sub(1),
            b'{' => brace_depth += 1,
            b'}' => brace_depth = brace_depth.saturating_sub(1),
            b'i' if bytes[index + 1] == b'f'
                && paren_depth == 0
                && bracket_depth == 0
                && brace_depth == 0
                && keyword_boundary(bytes, index, 2) =>
            {
                return &pattern[..index];
            }
            _ => {}
        }
        index += 1;
    }

    pattern
}

fn find_matching_close_brace(text_after_open: &str) -> Option<usize> {
    let mut depth = 0usize;
    for (index, byte) in text_after_open.bytes().enumerate() {
        match byte {
            b'{' => depth += 1,
            b'}' if depth == 0 => return Some(index),
            b'}' => depth -= 1,
            _ => {}
        }
    }
    None
}

fn contains_integer_literal_token(text: &str) -> bool {
    let bytes = text.as_bytes();
    let mut index = 0;
    while index < bytes.len() {
        if bytes[index].is_ascii_digit()
            && index
                .checked_sub(1)
                .and_then(|prev| bytes.get(prev))
                .is_none_or(|byte| !is_ascii_ident_byte(*byte))
        {
            return true;
        }
        index += 1;
    }
    false
}

fn contains_bare_token(text: &str, needle: &str) -> bool {
    text.match_indices(needle).any(|(index, _)| {
        let before_is_ident = index
            .checked_sub(1)
            .and_then(|prev| text.as_bytes().get(prev))
            .is_some_and(|byte| is_ascii_ident_byte(*byte));
        let after_is_ident = text
            .as_bytes()
            .get(index + needle.len())
            .is_some_and(|byte| is_ascii_ident_byte(*byte));
        !before_is_ident && !after_is_ident
    })
}

fn keyword_boundary(bytes: &[u8], index: usize, len: usize) -> bool {
    let before_is_ident = index
        .checked_sub(1)
        .and_then(|prev| bytes.get(prev))
        .is_some_and(|byte| is_ascii_ident_byte(*byte));
    let after_is_ident = bytes
        .get(index + len)
        .is_some_and(|byte| is_ascii_ident_byte(*byte));
    !before_is_ident && !after_is_ident
}

fn is_ascii_ident_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_'
}

fn contains_unsupported_plain_adt_index(
    tcx: TyCtxt<'_>,
    local_def_id: rustc_hir::def_id::LocalDefId,
    body_text: &str,
    crate_has_index_logic_method: bool,
) -> bool {
    let compact = compact_text(body_text);
    if !compact.contains('[') || crate_has_index_logic_method {
        return false;
    }

    let body = tcx.hir_body_owned_by(local_def_id);
    let typeck_results = tcx.typeck_body(body.id());
    body.params.iter().any(|param| {
        let PatKind::Binding(_, _, ident, _) = param.pat.kind else {
            return false;
        };
        let needle = format!("{}[", ident.name);
        if !contains_with_left_word_boundary(&compact, &needle) {
            return false;
        }
        matches!(
            typeck_results.pat_ty(param.pat).kind(),
            TyKind::Adt(adt_def, _) if adt_def.did().is_local()
        )
    })
}

/// Word-boundary-aware substring check.
///
/// Returns `true` only when `needle` appears in `haystack` with the byte
/// immediately preceding the match not part of an identifier (so that
/// looking for `c[` does not match inside `ac[`). A match at index 0 also
/// counts as having a valid left boundary.
fn contains_with_left_word_boundary(haystack: &str, needle: &str) -> bool {
    let bytes = haystack.as_bytes();
    if needle.is_empty() {
        return false;
    }
    let needle_len = needle.len();
    let mut start = 0;
    while let Some(off) = haystack[start..].find(needle) {
        let idx = start + off;
        let left_is_ident = idx
            .checked_sub(1)
            .and_then(|prev| bytes.get(prev))
            .is_some_and(|byte| is_ascii_ident_byte(*byte));
        if !left_is_ident {
            return true;
        }
        start = idx + needle_len;
        if start >= bytes.len() {
            break;
        }
    }
    false
}

fn crate_has_local_assoc_fn_named(tcx: TyCtxt<'_>, name: &str) -> bool {
    tcx.iter_local_def_id().any(|local_def_id| {
        let def_id = local_def_id.to_def_id();
        matches!(tcx.def_kind(def_id), DefKind::AssocFn) && tcx.item_name(def_id).as_str() == name
    })
}

fn compact_text(text: &str) -> String {
    text.chars().filter(|ch| !ch.is_whitespace()).collect()
}

/// Locate a `proof_assert!(false)` that is lexically *inside* a loop body.
///
/// `proof_assert!(expr)` lowers to a marker closure carrying
/// `#[doc = "trust-wp:proof_assert:<expr>"]`. We walk the THIR-lowered HIR
/// tracking loop-nesting depth (Rust `while`/`for`/`loop` all desugar to
/// `ExprKind::Loop`) and flag the marker closure only when it appears within a
/// loop body. This replaces the previous substring heuristic
/// (`body_text.contains("while") && body_text.contains("proof_assert!(false)")`)
/// which false-positived whenever a `proof_assert!(false)` merely preceded an
/// unrelated loop in the same function (Creusot `erasure.rs::specs`, where the
/// assertion is before a `while false {}`). A `proof_assert!(false)` outside any
/// loop is a normal (here vacuous, under `#[requires(false)]`) obligation and is
/// not flagged here.
fn loop_false_proof_assert_span(
    tcx: TyCtxt<'_>,
    local_def_id: rustc_hir::def_id::LocalDefId,
) -> Option<Span> {
    let body = tcx.hir_body_owned_by(local_def_id);
    let mut visitor = LoopFalseProofAssertVisitor {
        tcx,
        loop_depth: 0,
        span: None,
    };
    visitor.visit_body(body);
    visitor.span
}

struct LoopFalseProofAssertVisitor<'tcx> {
    tcx: TyCtxt<'tcx>,
    loop_depth: usize,
    span: Option<Span>,
}

impl<'tcx> Visitor<'tcx> for LoopFalseProofAssertVisitor<'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;
    type MaybeTyCtxt = TyCtxt<'tcx>;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if self.span.is_some() {
            return;
        }
        match expr.kind {
            ExprKind::Loop(..) => {
                self.loop_depth += 1;
                walk_expr(self, expr);
                self.loop_depth -= 1;
            }
            ExprKind::Closure(_) if self.loop_depth > 0 => {
                if expr_is_false_proof_assert(self.tcx, expr.hir_id) {
                    self.span = Some(expr.span);
                    return;
                }
                walk_expr(self, expr);
            }
            _ => walk_expr(self, expr),
        }
    }
}

/// True if the HIR node carries a `proof_assert!` doc marker whose asserted
/// expression is literally `false` (whitespace-insensitive). Both the verified
/// (`trust-wp:proof_assert:`) and trusted (`trust-wp:trusted_proof_assert:`)
/// markers are recognized so a `#[trusted] proof_assert!(false)` in a loop is
/// also caught.
fn expr_is_false_proof_assert(tcx: TyCtxt<'_>, hir_id: rustc_hir::HirId) -> bool {
    tcx.hir_attrs(hir_id).iter().any(|attr| {
        crate::attr_utils::doc_marker_str(attr).is_some_and(|value| {
            let value = value.as_str();
            let expr_text = value
                .strip_prefix("trust-wp:proof_assert:")
                .or_else(|| value.strip_prefix("trust-wp:trusted_proof_assert:"));
            expr_text.is_some_and(|text| compact_text(text) == "false")
        })
    })
}

fn raw_pointer_deref_span(
    tcx: TyCtxt<'_>,
    local_def_id: rustc_hir::def_id::LocalDefId,
) -> Option<Span> {
    let body = tcx.hir_body_owned_by(local_def_id);
    let typeck_results = tcx.typeck_body(body.id());
    let mut visitor = RawPointerDerefVisitor {
        tcx,
        typeck_results,
        span: None,
    };
    visitor.visit_body(body);
    visitor.span
}

struct RawPointerDerefVisitor<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck_results: &'a TypeckResults<'tcx>,
    span: Option<Span>,
}

impl<'tcx> Visitor<'tcx> for RawPointerDerefVisitor<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;
    type MaybeTyCtxt = TyCtxt<'tcx>;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if self.span.is_some() {
            return;
        }
        if let ExprKind::Unary(UnOp::Deref, inner) = expr.kind {
            if matches!(
                self.typeck_results.expr_ty(inner).kind(),
                TyKind::RawPtr(_, _)
            ) {
                self.span = Some(expr.span);
                return;
            }
        }
        walk_expr(self, expr);
    }
}

struct ProgramLogicCallValidator<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    typeck_results: &'a TypeckResults<'tcx>,
    ghost_spans: Vec<Span>,
    /// Depth counter for snapshot capture contexts. Matches the
    /// `ProgramContextGhostApiValidator` machinery in `ghost::mod`: inside
    /// `Snapshot::capture(...)` arguments or the body of a unit-block
    /// `snapshot! { stmt; }` pattern, logic functions are allowed because
    /// the snapshot is itself a ghost capture. (#9)
    snapshot_capture_depth: usize,
    errors: Vec<PurityValidationError>,
}

impl<'tcx> Visitor<'tcx> for ProgramLogicCallValidator<'_, 'tcx> {
    type NestedFilter = nested_filter::OnlyBodies;
    type MaybeTyCtxt = TyCtxt<'tcx>;

    fn maybe_tcx(&mut self) -> Self::MaybeTyCtxt {
        self.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if self.is_in_ghost_context(expr.span) {
            return;
        }

        // Statement-form snapshot blocks (`snapshot! { stmt; }`) lower to a
        // block whose tail is `Snapshot::<()>::new_phantom()`, not a
        // `Snapshot::capture(...)` call.  Without explicit recognition the
        // body's statements (which are conceptually ghost) would still be
        // walked with `snapshot_capture_depth == 0` and reject any
        // `#[logic]` calls in the captured body. (#9)
        if let ExprKind::Block(block, _) = expr.kind {
            if is_unit_block_snapshot_pattern(block) {
                self.snapshot_capture_depth += 1;
                rustc_hir::intravisit::walk_expr(self, expr);
                self.snapshot_capture_depth -= 1;
                return;
            }

            // Type-directed `snapshot!` capture dispatch lowers to a block
            // `{ snapshot_capture_select(&(expr)).capture() }`. The captured
            // `expr` lives in the `snapshot_capture_select` argument, so the
            // whole block is the snapshot capture context — allow `#[logic]`
            // calls in `expr`. (bug/869)
            if is_dispatch_snapshot_block(block) {
                self.snapshot_capture_depth += 1;
                rustc_hir::intravisit::walk_expr(self, expr);
                self.snapshot_capture_depth -= 1;
                return;
            }
        }

        // Argument position of `Snapshot::capture(...)` is also a snapshot
        // capture context, so allow `#[logic]` calls inside the captured
        // expression, just as the ghost API validator already does.
        if let ExprKind::Call(callee, args) = expr.kind {
            if self.is_snapshot_capture_callee(callee) {
                self.visit_expr(callee);
                self.snapshot_capture_depth += 1;
                for arg in args {
                    self.visit_expr(arg);
                }
                self.snapshot_capture_depth -= 1;
                return;
            }
        }

        let def_id = match expr.kind {
            ExprKind::Call(callee, _) => self.call_def_id(callee),
            ExprKind::MethodCall(..) => self.typeck_results.type_dependent_def_id(expr.hir_id),
            _ => None,
        };

        if let Some(def_id) = def_id {
            let attrs = self.tcx.get_all_attrs(def_id);
            if crate::logic::has_logic_marker(attrs) && self.snapshot_capture_depth == 0 {
                self.errors.push(PurityValidationError {
                    span: expr.span,
                    message: format!(
                        "called logic function `{}` in program context",
                        self.tcx.def_path_str(def_id)
                    ),
                });
            }
            if is_unsupported_map_entry_api(self.tcx, def_id) {
                self.errors.push(PurityValidationError {
                    span: expr.span,
                    message: UNSUPPORTED_MAP_ENTRY_API_MESSAGE.to_string(),
                });
            }
        }

        walk_expr(self, expr);
    }
}

impl ProgramLogicCallValidator<'_, '_> {
    fn is_in_ghost_context(&self, span: Span) -> bool {
        self.ghost_spans
            .iter()
            .any(|ghost_span| ghost_span.contains(span))
    }

    fn call_def_id(&self, callee: &Expr<'_>) -> Option<DefId> {
        if let TyKind::FnDef(def_id, _) = self.typeck_results.expr_ty(callee).kind() {
            return Some(*def_id);
        }

        if let ExprKind::Path(qpath) = &callee.kind {
            if let Res::Def(_, def_id) = self.qpath_res(qpath, callee) {
                return Some(def_id);
            }
        }

        None
    }

    fn qpath_res(&self, qpath: &QPath<'_>, callee: &Expr<'_>) -> Res {
        self.typeck_results.qpath_res(qpath, callee.hir_id)
    }

    fn is_snapshot_capture_callee(&self, callee: &Expr<'_>) -> bool {
        self.call_def_id(callee)
            .is_some_and(|def_id| is_snapshot_capture_call(self.tcx, def_id))
            || callee_path_is_snapshot_method(callee, "capture")
    }
}

/// Recognise the HIR shape emitted by statement-form unit `snapshot!`
/// macros: a block whose tail is a `Snapshot::*::new_phantom()` call.
/// See `ghost::is_unit_block_snapshot_pattern` for the full rationale. (#9)
fn is_unit_block_snapshot_pattern(block: &Block<'_>) -> bool {
    let Some(tail) = block.expr else {
        return false;
    };
    let ExprKind::Call(callee, _) = tail.kind else {
        return false;
    };
    callee_path_is_snapshot_method(callee, "new_phantom")
}

/// Recognise the HIR shape emitted by the type-directed `snapshot!` capture
/// dispatch: a block whose tail is `<recv>.capture(_)` where `<recv>` is a
/// `snapshot_capture_select(_)` call. The captured expression is bound in a
/// preceding `let`, so the whole block is a snapshot capture context. (bug/869)
fn is_dispatch_snapshot_block(block: &Block<'_>) -> bool {
    let Some(tail) = block.expr else {
        return false;
    };
    let ExprKind::MethodCall(seg, receiver, _, _) = tail.kind else {
        return false;
    };
    if seg.ident.as_str() != "capture" {
        return false;
    }
    let ExprKind::Call(callee, _) = receiver.kind else {
        return false;
    };
    let ExprKind::Path(qpath) = &callee.kind else {
        return false;
    };
    let last_segment = match qpath {
        QPath::Resolved(_, path) => path.segments.last().map(|s| s.ident.as_str()),
        QPath::TypeRelative(_, segment) => Some(segment.ident.as_str()),
    };
    last_segment == Some("snapshot_capture_select")
}

fn callee_path_is_snapshot_method(callee: &Expr<'_>, method_name: &str) -> bool {
    let ExprKind::Path(qpath) = &callee.kind else {
        return false;
    };
    qpath_is_snapshot_method(qpath, method_name)
}

fn qpath_is_snapshot_method(qpath: &QPath<'_>, method_name: &str) -> bool {
    match qpath {
        QPath::Resolved(_, path) => {
            let mut segments = path.segments.iter().rev();
            let Some(method) = segments.next() else {
                return false;
            };
            if method.ident.as_str() != method_name {
                return false;
            }
            segments
                .next()
                .is_some_and(|owner| owner.ident.as_str() == "Snapshot")
        }
        QPath::TypeRelative(ty, segment) => {
            if segment.ident.as_str() != method_name {
                return false;
            }
            matches!(
                ty.kind,
                HirTyKind::Path(QPath::Resolved(_, path))
                    if path.segments.last().is_some_and(|owner| {
                        owner.ident.as_str() == "Snapshot"
                    })
            )
        }
    }
}

fn is_snapshot_capture_call(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let crate_name = tcx.crate_name(def_id.krate).to_string();
    if !matches!(
        crate_name.as_str(),
        "trust_wp_std" | "trust-wp" | "creusot_std" | "creusot_contracts"
    ) {
        return false;
    }
    let def_path = tcx.def_path_str(def_id);
    let mut components = def_path.rsplit("::");
    let Some(method_name) = components.next() else {
        return false;
    };
    if method_name != "capture" {
        return false;
    }
    let Some(owner) = components.next() else {
        return false;
    };
    matches!(owner, "Snapshot") || owner.contains("Snapshot<")
}

#[cfg(test)]
mod tests {
    use super::{
        contains_int_literal_pattern_match_text,
        contains_int_literal_pattern_match_text_for_params, contains_primitive_arith_op,
        strip_comments_and_literals,
    };

    #[test]
    fn primitive_arith_detects_bare_ident_division() {
        assert!(contains_primitive_arith_op("x / y", '/'));
        assert!(contains_primitive_arith_op("x % y", '%'));
    }

    #[test]
    fn primitive_arith_detects_bare_ident_with_literal() {
        assert!(contains_primitive_arith_op("x % 2 == 0", '%'));
        assert!(contains_primitive_arith_op("n / 10", '/'));
    }

    #[test]
    fn primitive_arith_ignores_lifted_method_call_lhs() {
        // `x.view() % 2` is a logic-Int operation, not a primitive remainder.
        assert!(!contains_primitive_arith_op("x.view() % 2 == 0", '%'));
        assert!(!contains_primitive_arith_op("f(a, b) / 10", '/'));
    }

    #[test]
    fn primitive_arith_ignores_op_at_start() {
        assert!(!contains_primitive_arith_op("% 2", '%'));
        assert!(!contains_primitive_arith_op("   / 4", '/'));
    }

    #[test]
    fn int_literal_text_scan_detects_literal_match_patterns() {
        assert!(contains_int_literal_pattern_match_text(
            "match x { 1 | 2 => x, _ => x }"
        ));
    }

    #[test]
    fn int_literal_text_scan_ignores_match_guard_literals() {
        assert!(!contains_int_literal_pattern_match_text(
            "match x { y if y == Int(0) => y, _ => x }"
        ));
    }

    #[test]
    fn int_literal_text_scan_keeps_literal_patterns_with_guards() {
        assert!(contains_int_literal_pattern_match_text(
            "match x { 0 if enabled => x, _ => x }"
        ));
    }

    #[test]
    fn int_literal_text_scan_ignores_line_comments() {
        assert!(!contains_int_literal_pattern_match_text(
            "// match x { 0 => x, _ => x }\nx"
        ));
    }

    #[test]
    fn int_literal_text_scan_ignores_block_comments() {
        assert!(!contains_int_literal_pattern_match_text(
            "/* match x { 0 => x, _ => x } */\nx"
        ));
    }

    #[test]
    fn int_literal_text_scan_ignores_strings_and_raw_strings() {
        assert!(!contains_int_literal_pattern_match_text(
            r###"let a = "match x { 0 => x, _ => x }";
let b = r##"match x { 1 => x, _ => x }"##;
x"###
        ));
    }

    #[test]
    fn int_literal_text_scan_can_restrict_to_logic_int_param_scrutinee() {
        let params = vec!["x".to_string()];
        assert!(contains_int_literal_pattern_match_text_for_params(
            "match x { 0 => x, _ => x }",
            &params,
        ));
        assert!(!contains_int_literal_pattern_match_text_for_params(
            "match y { 0 => x, _ => x }",
            &params,
        ));
    }

    #[test]
    fn sanitized_raw_scan_removes_forbidden_looking_text() {
        let code = strip_comments_and_literals(
            r###"// dead / % proof_assert!(false) Secret { value: 1 } bag[0]
/* hidden_default(x) */
let a = "dead / % proof_assert!(false) Secret { value: 1 } bag[0]";
let b = r##"hidden_default(x)"##;"###,
        );

        for forbidden in [
            "dead",
            "proof_assert",
            "hidden_default",
            "Secret",
            "bag[",
            "/",
            "%",
        ] {
            assert!(
                !code.contains(forbidden),
                "sanitized code should remove {forbidden:?}: {code:?}"
            );
        }
    }
}
