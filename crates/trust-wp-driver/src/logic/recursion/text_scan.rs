// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::collections::HashSet;

pub(super) fn collect_logic_references_from_text(body_text: &str, names: &mut HashSet<String>) {
    let sanitized = strip_non_code_regions(body_text);
    let bytes = sanitized.as_bytes();
    let mut idx = 0usize;
    while idx < bytes.len() {
        if bytes[idx] != b'(' {
            idx += 1;
            continue;
        }

        if let Some(candidate) = extract_call_candidate_before_paren(&sanitized, idx) {
            names.insert(candidate);
        }
        idx += 1;
    }
}

/// Collect bare method names from `<receiver>.method(...)` patterns in body
/// text where the receiver is NOT `self`/`Self`. These calls are filtered out
/// of the main recursion graph (because text scanning cannot determine the
/// receiver type and creating naive edges produces false positives), but they
/// are needed to detect trait-mediated mutual recursion through concrete
/// receivers (creusot tests/should_fail/bug/1565.rs and 459.rs).
///
/// Returns just the method name segment (e.g., `f` from `1i32.f()`,
/// `deep_model` from `a.deep_model()`). Filters out common non-logic keywords
/// (control flow, std constructors, etc.) and macros (calls preceded by `!`).
pub(super) fn collect_non_self_method_call_names_from_text(
    body_text: &str,
    names: &mut HashSet<String>,
) {
    let sanitized = strip_non_code_regions(body_text);
    let bytes = sanitized.as_bytes();
    let mut idx = 0usize;
    while idx < bytes.len() {
        if bytes[idx] != b'(' {
            idx += 1;
            continue;
        }
        if let Some(method_name) = extract_non_self_method_call_name(&sanitized, idx) {
            names.insert(method_name);
        }
        idx += 1;
    }
}

fn extract_non_self_method_call_name(text: &str, paren_idx: usize) -> Option<String> {
    if paren_idx == 0 {
        return None;
    }
    let bytes = text.as_bytes();
    let mut end = paren_idx;
    while end > 0 && bytes[end - 1].is_ascii_whitespace() {
        end -= 1;
    }
    if end == 0 || bytes[end - 1] == b'!' {
        return None;
    }
    // Walk back over ASCII identifier characters only — the method name segment.
    let mut start = end;
    while start > 0 {
        let ch = bytes[start - 1] as char;
        if ch.is_ascii_alphanumeric() || ch == '_' {
            start -= 1;
        } else {
            break;
        }
    }
    if start == end {
        return None;
    }
    // The character immediately before the identifier must be a `.` for this
    // to be a method call. Otherwise, it's a bare function call (already
    // handled by `collect_logic_references_from_text`).
    let mut before_start = start;
    while before_start > 0 && bytes[before_start - 1].is_ascii_whitespace() {
        before_start -= 1;
    }
    if before_start == 0 || bytes[before_start - 1] != b'.' {
        return None;
    }
    // Confirm the receiver is NOT just `self`/`Self` — those calls are already
    // handled as direct self-dispatch edges. Walk back over the receiver
    // identifier to peek at it.
    let mut recv_end = before_start - 1;
    while recv_end > 0 && bytes[recv_end - 1].is_ascii_whitespace() {
        recv_end -= 1;
    }
    let mut recv_start = recv_end;
    while recv_start > 0 {
        let ch = bytes[recv_start - 1] as char;
        if ch.is_ascii_alphanumeric() || ch == '_' {
            recv_start -= 1;
        } else {
            break;
        }
    }
    let receiver = text[recv_start..recv_end].trim();
    if receiver == "self" || receiver == "Self" {
        return None;
    }
    let method = text[start..end].trim().to_string();
    if method.is_empty() || is_non_logic_call_keyword(&method) {
        return None;
    }
    Some(method)
}

#[derive(Clone, Copy)]
enum StringMode {
    Normal { escaped: bool },
    Raw { hashes: usize },
}

fn strip_non_code_regions(text: &str) -> String {
    let bytes = text.as_bytes();
    let mut sanitized = bytes.to_vec();
    let mut idx = 0usize;
    let mut in_line_comment = false;
    let mut block_comment_depth = 0usize;
    let mut string_mode: Option<StringMode> = None;

    while idx < bytes.len() {
        if scrub_line_comment(bytes, &mut sanitized, &mut idx, &mut in_line_comment)
            || scrub_block_comment(bytes, &mut sanitized, &mut idx, &mut block_comment_depth)
            || scrub_string_literal(bytes, &mut sanitized, &mut idx, &mut string_mode)
            || start_line_comment(bytes, &mut sanitized, &mut idx, &mut in_line_comment)
            || start_block_comment(bytes, &mut sanitized, &mut idx, &mut block_comment_depth)
            || start_raw_string(bytes, &mut sanitized, &mut idx, &mut string_mode)
            || start_normal_string(bytes, &mut sanitized, &mut idx, &mut string_mode)
        {
            continue;
        }
        idx += 1;
    }

    String::from_utf8(sanitized).unwrap_or_else(|_| text.to_string())
}

fn scrub_line_comment(
    bytes: &[u8],
    sanitized: &mut [u8],
    idx: &mut usize,
    in_line_comment: &mut bool,
) -> bool {
    if !*in_line_comment {
        return false;
    }
    if bytes[*idx] == b'\n' {
        *in_line_comment = false;
    } else {
        sanitized[*idx] = b' ';
    }
    *idx += 1;
    true
}

fn scrub_block_comment(
    bytes: &[u8],
    sanitized: &mut [u8],
    idx: &mut usize,
    block_comment_depth: &mut usize,
) -> bool {
    if *block_comment_depth == 0 {
        return false;
    }

    if idx.saturating_add(1) < bytes.len() && bytes[*idx] == b'/' && bytes[*idx + 1] == b'*' {
        sanitized[*idx] = b' ';
        sanitized[*idx + 1] = b' ';
        *block_comment_depth += 1;
        *idx += 2;
        return true;
    }
    if idx.saturating_add(1) < bytes.len() && bytes[*idx] == b'*' && bytes[*idx + 1] == b'/' {
        sanitized[*idx] = b' ';
        sanitized[*idx + 1] = b' ';
        *block_comment_depth -= 1;
        *idx += 2;
        return true;
    }

    if bytes[*idx] != b'\n' {
        sanitized[*idx] = b' ';
    }
    *idx += 1;
    true
}

fn scrub_string_literal(
    bytes: &[u8],
    sanitized: &mut [u8],
    idx: &mut usize,
    string_mode: &mut Option<StringMode>,
) -> bool {
    let Some(mode) = *string_mode else {
        return false;
    };

    match mode {
        StringMode::Normal { escaped } => {
            if bytes[*idx] == b'\n' {
                *string_mode = None;
                *idx += 1;
                return true;
            }
            sanitized[*idx] = b' ';
            if escaped {
                *string_mode = Some(StringMode::Normal { escaped: false });
            } else if bytes[*idx] == b'\\' {
                *string_mode = Some(StringMode::Normal { escaped: true });
            } else if bytes[*idx] == b'"' {
                *string_mode = None;
            }
            *idx += 1;
            true
        }
        StringMode::Raw { hashes } => {
            if bytes[*idx] == b'\n' {
                *idx += 1;
                return true;
            }
            if bytes[*idx] == b'"' && raw_string_terminator_matches(bytes, *idx, hashes) {
                mask_span_as_spaces(sanitized, *idx, 1 + hashes);
                *idx += 1 + hashes;
                *string_mode = None;
                return true;
            }
            sanitized[*idx] = b' ';
            *idx += 1;
            true
        }
    }
}

fn start_line_comment(
    bytes: &[u8],
    sanitized: &mut [u8],
    idx: &mut usize,
    in_line_comment: &mut bool,
) -> bool {
    if idx.saturating_add(1) >= bytes.len() || bytes[*idx] != b'/' || bytes[*idx + 1] != b'/' {
        return false;
    }
    mask_span_as_spaces(sanitized, *idx, 2);
    *in_line_comment = true;
    *idx += 2;
    true
}

fn start_block_comment(
    bytes: &[u8],
    sanitized: &mut [u8],
    idx: &mut usize,
    block_comment_depth: &mut usize,
) -> bool {
    if idx.saturating_add(1) >= bytes.len() || bytes[*idx] != b'/' || bytes[*idx + 1] != b'*' {
        return false;
    }
    mask_span_as_spaces(sanitized, *idx, 2);
    *block_comment_depth = 1;
    *idx += 2;
    true
}

fn start_raw_string(
    bytes: &[u8],
    sanitized: &mut [u8],
    idx: &mut usize,
    string_mode: &mut Option<StringMode>,
) -> bool {
    let Some((prefix_len, hashes)) = raw_string_prefix_at(bytes, *idx) else {
        return false;
    };
    mask_span_as_spaces(sanitized, *idx, prefix_len);
    *idx += prefix_len;
    *string_mode = Some(StringMode::Raw { hashes });
    true
}

fn start_normal_string(
    bytes: &[u8],
    sanitized: &mut [u8],
    idx: &mut usize,
    string_mode: &mut Option<StringMode>,
) -> bool {
    if bytes[*idx] != b'"' {
        return false;
    }
    sanitized[*idx] = b' ';
    *idx += 1;
    *string_mode = Some(StringMode::Normal { escaped: false });
    true
}

fn mask_span_as_spaces(sanitized: &mut [u8], start: usize, len: usize) {
    for byte in sanitized.iter_mut().skip(start).take(len) {
        *byte = b' ';
    }
}

fn raw_string_prefix_at(bytes: &[u8], idx: usize) -> Option<(usize, usize)> {
    if idx >= bytes.len() {
        return None;
    }

    let start = match bytes[idx] {
        b'r' => idx,
        b'b' if idx + 1 < bytes.len() && bytes[idx + 1] == b'r' => idx + 1,
        _ => return None,
    };

    let mut cursor = start + 1;
    let mut hashes = 0usize;
    while cursor < bytes.len() && bytes[cursor] == b'#' {
        hashes += 1;
        cursor += 1;
    }

    if cursor < bytes.len() && bytes[cursor] == b'"' {
        let prefix_len = cursor - idx + 1;
        Some((prefix_len, hashes))
    } else {
        None
    }
}

fn raw_string_terminator_matches(bytes: &[u8], quote_idx: usize, hashes: usize) -> bool {
    if quote_idx + hashes >= bytes.len() {
        return false;
    }
    (0..hashes).all(|offset| bytes[quote_idx + 1 + offset] == b'#')
}

fn extract_call_candidate_before_paren(text: &str, paren_idx: usize) -> Option<String> {
    if paren_idx == 0 {
        return None;
    }

    let bytes = text.as_bytes();
    let mut end = paren_idx;
    while end > 0 && bytes[end - 1].is_ascii_whitespace() {
        end -= 1;
    }
    if end == 0 || bytes[end - 1] == b'!' {
        return None;
    }

    let mut start = end;
    while start > 0 {
        let ch = bytes[start - 1] as char;
        if ch.is_ascii_alphanumeric() || matches!(ch, '_' | ':' | '<' | ' ') {
            start -= 1;
        } else if ch == '>' {
            // Allow `>` for generics like `<T>::method(...)` but stop at `=>`
            // (match arm arrow) to avoid extracting `> name` from match bodies.
            if start >= 2 && bytes[start - 2] == b'=' {
                break;
            }
            start -= 1;
        } else {
            break;
        }
    }
    if start == end {
        return None;
    }

    let raw = text[start..end].trim();
    if raw.is_empty() {
        return None;
    }
    if has_non_self_method_receiver(bytes, text, start) {
        return None;
    }
    let mut normalized = normalize_call_candidate(raw);
    if normalized.is_empty() {
        return None;
    }

    // Drop obvious Rust control-flow/primitive calls that are not logic refs.
    let keyword = normalized.rsplit("::").next().unwrap_or(&normalized);
    if is_non_logic_call_keyword(keyword) {
        return None;
    }

    // If this was parsed from a type-cast fragment like `as i32`, ignore it.
    if normalized.starts_with("as ") {
        return None;
    }

    // Preserve canonical `Self::f` style and UFCS spacing style (`<T as Trait>::f`).
    if normalized.starts_with('<') && normalized.contains("as") {
        normalized = normalized.replace("< ", "<").replace(" >", ">");
    }

    Some(normalized)
}

fn has_non_self_method_receiver(bytes: &[u8], text: &str, start: usize) -> bool {
    // Ignore most method calls like `x.f(...)`: text-based extraction cannot
    // distinguish receiver types and can create false recursion edges. Keep
    // `self.f(...)`/`Self::f(...)` style dispatch candidates.
    let mut before_start = start;
    while before_start > 0 && bytes[before_start - 1].is_ascii_whitespace() {
        before_start -= 1;
    }
    if before_start == 0 || bytes[before_start - 1] != b'.' {
        return false;
    }

    let mut recv_end = before_start - 1;
    while recv_end > 0 && bytes[recv_end - 1].is_ascii_whitespace() {
        recv_end -= 1;
    }
    let mut recv_start = recv_end;
    while recv_start > 0 {
        let ch = bytes[recv_start - 1] as char;
        if ch.is_ascii_alphanumeric() || ch == '_' {
            recv_start -= 1;
        } else {
            break;
        }
    }

    let receiver = text[recv_start..recv_end].trim();
    receiver != "self" && receiver != "Self"
}

fn normalize_call_candidate(raw: &str) -> String {
    let mut normalized = raw.split_whitespace().collect::<Vec<_>>().join(" ");
    normalized = normalized
        .replace(":: ", "::")
        .replace(" ::", "::")
        .replace(" :: ", "::");
    normalized.trim().to_string()
}

fn is_non_logic_call_keyword(keyword: &str) -> bool {
    matches!(
        keyword,
        // Rust control-flow keywords
        "if" | "while"
            | "for"
            | "loop"
            | "match"
            | "return"
            | "let"
            | "break"
            | "continue"
            | "unsafe"
            | "async"
            | "await"
            | "move"
            | "yield"
            // Standard enum constructors
            | "Some"
            | "None"
            | "Ok"
            | "Err"
            // Common standard library types (never logic functions)
            | "Vec"
            | "Box"
            | "Option"
            | "Result"
            | "String"
            | "Rc"
            | "Arc"
            | "HashMap"
            | "HashSet"
            | "BTreeMap"
            | "BTreeSet"
            | "Cow"
            | "PhantomData"
            | "Default"
            | "From"
            | "Into"
            | "Cell"
            | "RefCell"
            // Common macros/builtins that survive text extraction
            | "assert"
            | "assert_eq"
            | "assert_ne"
            | "debug_assert"
            | "debug_assert_eq"
            | "debug_assert_ne"
            | "println"
            | "eprintln"
            | "format"
            | "panic"
            | "todo"
            | "unimplemented"
            | "unreachable"
            | "dbg"
            | "write"
            | "writeln"
            | "cfg"
    )
}
