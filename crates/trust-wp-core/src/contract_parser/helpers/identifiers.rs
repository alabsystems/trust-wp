// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Identifier and path parsing: simple names, qualified paths, method names.

use super::super::{ContractParser, ParseError};
use crate::{
    contract_parser::TURBOFISH_ARG_WRAPPER_NAME,
    formula::{intern_sort_name, ExprSort, PureExpr},
};

impl ContractParser<'_> {
    /// Parse a simple identifier (no paths, no colons)
    pub(in crate::contract_parser) fn try_parse_simple_identifier(&mut self) -> Option<String> {
        self.skip_whitespace();

        let c = self.peek()?;
        if !c.is_alphabetic() && c != '_' {
            return None;
        }

        let mut ident = String::new();
        while let Some(c) = self.peek() {
            if c.is_alphanumeric() || c == '_' {
                ident.push(c);
                self.advance();
            } else {
                break;
            }
        }

        if ident.is_empty() {
            None
        } else {
            Some(ident)
        }
    }

    /// Try to parse an identifier (including paths like `i32::MIN`)
    pub(in crate::contract_parser) fn try_parse_identifier(&mut self) -> Option<String> {
        self.skip_whitespace();

        let c = self.peek()?;
        if !c.is_alphabetic() && c != '_' {
            return None;
        }

        let mut ident = self.try_parse_simple_identifier()?;
        loop {
            let checkpoint_pos = self.position;
            let checkpoint_chars = self.chars.clone();

            if !self.try_consume_path_separator() {
                break;
            }
            self.skip_whitespace();

            if let Some(segment) = self.try_parse_simple_identifier() {
                ident.push_str("::");
                ident.push_str(&segment);
            } else {
                // Not a real path segment (e.g., turbofish `::<...>`): roll back.
                self.position = checkpoint_pos;
                self.chars = checkpoint_chars;
                break;
            }
        }

        Some(ident)
    }

    /// Try to consume a path separator, accepting both `::` and `: :`.
    ///
    /// `TokenStream::to_string()` may insert whitespace between punctuation
    /// tokens. Accepting `: :` keeps parsing robust for doc-marker extracted
    /// logic bodies.
    pub(in crate::contract_parser) fn try_consume_path_separator(&mut self) -> bool {
        let checkpoint_pos = self.position;
        let checkpoint_chars = self.chars.clone();

        // Fast path: canonical `::`
        if self.try_consume("::") {
            return true;
        }

        // Fallback: spaced `: :`
        self.position = checkpoint_pos;
        self.chars = checkpoint_chars.clone();
        self.skip_whitespace();
        if self.try_consume(":") {
            self.skip_whitespace();
            if self.try_consume(":") {
                return true;
            }
        }

        self.position = checkpoint_pos;
        self.chars = checkpoint_chars;
        false
    }

    /// Try to parse an optional turbofish suffix like `::<T, N>`.
    ///
    /// The parser preserves the generic arguments behind an internal wrapper so
    /// the driver can later erase type-only generics while retaining const
    /// generics that participate in verification. (#1635)
    pub(in crate::contract_parser) fn try_parse_turbofish_args(
        &mut self,
    ) -> Result<Option<Vec<PureExpr>>, ParseError> {
        let checkpoint_pos = self.position;
        let checkpoint_chars = self.chars.clone();

        self.skip_whitespace();
        if !self.try_consume_path_separator() {
            self.position = checkpoint_pos;
            self.chars = checkpoint_chars;
            return Ok(None);
        }

        self.skip_whitespace();
        if self.peek() != Some('<') {
            self.position = checkpoint_pos;
            self.chars = checkpoint_chars;
            return Ok(None);
        }

        let raw_args = self.capture_balanced_angles_text()?;
        let mut parsed_args = Vec::new();
        for raw_arg in split_turbofish_args(&raw_args) {
            let raw_arg = raw_arg.trim();
            if raw_arg.is_empty() {
                continue;
            }
            parsed_args.push(PureExpr::LogicFnCall {
                name: TURBOFISH_ARG_WRAPPER_NAME.to_string(),
                args: vec![parse_turbofish_arg_expr(raw_arg)],
            });
        }
        Ok(Some(parsed_args))
    }

    /// Capture the text inside a balanced `<...>` group, consuming both
    /// delimiters.
    fn capture_balanced_angles_text(&mut self) -> Result<String, ParseError> {
        if !self.try_consume("<") {
            return Err(self.error("expected '<'"));
        }

        let start = self.position;
        let mut depth = 1u32;
        while let Some(ch) = self.peek() {
            match ch {
                '<' => {
                    depth += 1;
                    self.advance();
                }
                '>' => {
                    depth -= 1;
                    if depth == 0 {
                        let captured = self.input[start..self.position].to_string();
                        self.advance();
                        return Ok(captured);
                    }
                    self.advance();
                }
                _ => {
                    self.advance();
                }
            }
        }

        Err(self.error("unexpected end of input in type annotation"))
    }

    /// Try to parse a fully-qualified associated type/const path.
    ///
    /// Syntax: `<Type as Trait>::IDENT`
    ///
    /// Examples:
    /// - `<I3<T> as Nat>::VALUE`
    /// - `<T as ::std::mem::SizedTypeProperties>::IS_ZST`
    ///
    /// Returns `Some(path_string)` on success or `None` if the current position
    /// does not start a qualified path. The path string preserves the original
    /// syntax so downstream resolution can distinguish it from simple paths.
    ///
    /// This is a speculative parse: on failure the parser position is restored.
    pub(in crate::contract_parser) fn try_parse_qualified_path(&mut self) -> Option<String> {
        self.skip_whitespace();

        // Must start with '<'
        if self.peek() != Some('<') {
            return None;
        }

        let checkpoint_pos = self.position;
        let checkpoint_chars = self.chars.clone();

        // Advance past '<'
        self.advance();

        // Scan for the `as` keyword at depth 0 within the angle brackets.
        // We need to track nested `<>` to skip over generic parameters
        // like `<I3<T> as Nat>`.
        let mut depth = 0u32;
        let mut found_as = false;
        let mut path_buf = String::from("<");

        loop {
            match self.peek() {
                None => {
                    // End of input without finding pattern — restore and bail.
                    self.position = checkpoint_pos;
                    self.chars = checkpoint_chars;
                    return None;
                }
                Some('<') => {
                    depth += 1;
                    path_buf.push('<');
                    self.advance();
                }
                Some('>') => {
                    if depth == 0 {
                        // This is the closing '>' of the outermost qualified path.
                        if !found_as {
                            // No `as` keyword found — not a qualified path.
                            self.position = checkpoint_pos;
                            self.chars = checkpoint_chars;
                            return None;
                        }
                        path_buf.push('>');
                        self.advance();
                        break;
                    }
                    depth -= 1;
                    path_buf.push('>');
                    self.advance();
                }
                Some(c) => {
                    // Check for `as` keyword at depth 0
                    if depth == 0 && c.is_whitespace() {
                        let pre_ws_pos = self.position;
                        let pre_ws_chars = self.chars.clone();
                        self.skip_whitespace();
                        path_buf.push(' ');
                        if self.try_consume_keyword("as") {
                            found_as = true;
                            path_buf.push_str("as ");
                            self.skip_whitespace();
                        } else {
                            // Not `as` — restore whitespace position tracking
                            // and continue scanning.
                            self.position = pre_ws_pos;
                            self.chars = pre_ws_chars;
                            path_buf.pop(); // remove the space we added
                            path_buf.push(c);
                            self.advance();
                        }
                    } else {
                        path_buf.push(c);
                        self.advance();
                    }
                }
            }
        }

        // After `>`, expect `::` then an identifier.
        if !self.try_consume_path_separator() {
            self.position = checkpoint_pos;
            self.chars = checkpoint_chars;
            return None;
        }
        path_buf.push_str("::");

        // Parse the associated constant/type name.
        if let Some(name) = self.try_parse_simple_identifier() {
            path_buf.push_str(&name);

            // Allow further path segments: `<T as Trait>::Module::CONST`
            while self.try_consume_path_separator() {
                if let Some(segment) = self.try_parse_simple_identifier() {
                    path_buf.push_str("::");
                    path_buf.push_str(&segment);
                } else {
                    break;
                }
            }

            Some(canonicalize_qualified_path(&path_buf))
        } else {
            // No identifier after `>::` — not a valid qualified path.
            self.position = checkpoint_pos;
            self.chars = checkpoint_chars;
            None
        }
    }

    /// Parse method name (identifier without path support)
    pub(in crate::contract_parser) fn try_parse_method_name(&mut self) -> Option<String> {
        self.skip_whitespace();
        let c = self.peek()?;
        if !c.is_alphabetic() && c != '_' {
            return None;
        }
        let mut name = String::new();
        while let Some(c) = self.peek() {
            if c.is_ascii_alphanumeric() || c == '_' {
                name.push(c);
                self.advance();
            } else {
                break;
            }
        }
        if name.is_empty() {
            None
        } else {
            Some(name)
        }
    }
}

/// Canonicalize a qualified-path identifier so that whitespace-equivalent
/// forms produce the same string.
///
/// Rules:
/// - Strip whitespace after `<` and before `>`.
/// - Strip whitespace around `::` — EXCEPT when the immediately preceding
///   token is the `as` keyword, in which case exactly one space is preserved
///   between `as` and the following `::`. This keeps `<T as ::std::mem::X>`
///   canonical (matching driver-side emission) rather than collapsing it to
///   the invalid `<T as::std::mem::X>` form. (#7B / Wave 6C)
fn canonicalize_qualified_path(path: &str) -> String {
    let mut out = String::with_capacity(path.len());
    let mut chars = path.chars().peekable();

    while let Some(c) = chars.next() {
        match c {
            '<' => {
                out.push('<');
                while chars.peek().is_some_and(|ch| ch.is_whitespace()) {
                    chars.next();
                }
            }
            '>' => {
                while out.chars().next_back().is_some_and(char::is_whitespace) {
                    out.pop();
                }
                out.push('>');
                while chars.peek().is_some_and(|ch| ch.is_whitespace()) {
                    chars.next();
                }
            }
            ':' if chars.peek() == Some(&':') => {
                // Pop trailing whitespace from `out`. If the resulting suffix
                // is the `as` keyword, re-insert a single space so the
                // canonical form keeps `as ::path` (matches MIR emission).
                while out.chars().next_back().is_some_and(char::is_whitespace) {
                    out.pop();
                }
                if ends_with_keyword_as(&out) {
                    out.push(' ');
                }
                out.push_str("::");
                chars.next();
                while chars.peek().is_some_and(|ch| ch.is_whitespace()) {
                    chars.next();
                }
            }
            _ => out.push(c),
        }
    }

    out
}

/// Return true if `s` ends with the standalone `as` keyword (i.e., `as`
/// preceded by start-of-string or a non-identifier character). This prevents
/// false positives like `Atlas` or `class`.
fn ends_with_keyword_as(s: &str) -> bool {
    let bytes = s.as_bytes();
    let n = bytes.len();
    if n < 2 || &bytes[n - 2..] != b"as" {
        return false;
    }
    if n == 2 {
        return true;
    }
    let prev = bytes[n - 3];
    !(prev.is_ascii_alphanumeric() || prev == b'_')
}

fn parse_turbofish_arg_expr(raw: &str) -> PureExpr {
    if raw.is_empty() {
        return make_turbofish_type_placeholder(raw);
    }

    if is_definitely_type_like_turbofish_arg(raw) {
        return make_turbofish_type_placeholder(raw);
    }

    match ContractParser::new(raw).parse() {
        Ok(expr)
            if matches!(expr, PureExpr::Var(_, _))
                && is_likely_type_like_identifier_or_path(raw) =>
        {
            make_turbofish_type_placeholder(raw)
        }
        Ok(expr) => expr,
        Err(_) => make_turbofish_type_placeholder(raw),
    }
}

fn make_turbofish_type_placeholder(raw: &str) -> PureExpr {
    PureExpr::Var(
        raw.trim().to_string(),
        Some(ExprSort::TypeParam(intern_sort_name(raw.trim()))),
    )
}

fn split_turbofish_args(raw: &str) -> Vec<&str> {
    let mut args = Vec::new();
    let mut start = 0usize;
    let mut angle_depth = 0u32;
    let mut paren_depth = 0u32;
    let mut bracket_depth = 0u32;
    let mut brace_depth = 0u32;

    for (idx, ch) in raw.char_indices() {
        match ch {
            '<' => angle_depth += 1,
            '>' => angle_depth = angle_depth.saturating_sub(1),
            '(' => paren_depth += 1,
            ')' => paren_depth = paren_depth.saturating_sub(1),
            '[' => bracket_depth += 1,
            ']' => bracket_depth = bracket_depth.saturating_sub(1),
            '{' => brace_depth += 1,
            '}' => brace_depth = brace_depth.saturating_sub(1),
            ',' if angle_depth == 0
                && paren_depth == 0
                && bracket_depth == 0
                && brace_depth == 0 =>
            {
                args.push(&raw[start..idx]);
                start = idx + ch.len_utf8();
            }
            _ => {}
        }
    }

    if start <= raw.len() {
        args.push(&raw[start..]);
    }

    args
}

fn is_definitely_type_like_turbofish_arg(raw: &str) -> bool {
    let raw = raw.trim();
    if raw.is_empty() {
        return false;
    }

    if matches!(
        raw,
        "Self"
            | "bool"
            | "char"
            | "str"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "f32"
            | "f64"
    ) {
        return true;
    }

    if raw.contains('[')
        || raw.contains(']')
        || raw.contains('&')
        || raw.contains('*')
        || raw.contains('\'')
        || raw.starts_with("dyn ")
        || raw.starts_with("impl ")
    {
        return true;
    }

    if raw.contains('<') && !raw.starts_with('<') {
        return true;
    }

    is_likely_type_like_identifier_or_path(raw)
}

fn is_likely_type_like_identifier_or_path(raw: &str) -> bool {
    let raw = raw.trim();
    let last_segment = raw.rsplit("::").next().unwrap_or(raw);
    let mut chars = last_segment.chars();
    let Some(first) = chars.next() else {
        return false;
    };

    if !first.is_ascii_uppercase() {
        return false;
    }

    if last_segment.len() == 1 {
        return true;
    }

    let has_lowercase = chars.clone().any(|c| c.is_ascii_lowercase());
    let is_all_caps = last_segment
        .chars()
        .all(|c| c.is_ascii_uppercase() || c.is_ascii_digit() || c == '_');

    has_lowercase || !is_all_caps
}
