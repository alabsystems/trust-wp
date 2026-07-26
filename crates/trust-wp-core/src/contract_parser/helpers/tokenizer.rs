// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Low-level tokenization primitives for the contract parser.
//!
//! Character-by-character consumption, whitespace skipping, keyword matching,
//! and single-token operators.

use super::super::{ContractParser, ParseError};

impl ContractParser<'_> {
    /// Skip whitespace characters
    pub(in crate::contract_parser) fn skip_whitespace(&mut self) {
        while self.peek().is_some_and(char::is_whitespace) {
            self.advance();
        }
    }

    /// Peek at the next character
    pub(in crate::contract_parser) fn peek(&mut self) -> Option<char> {
        self.chars.peek().copied()
    }

    /// Advance to the next character
    pub(in crate::contract_parser) fn advance(&mut self) -> Option<char> {
        let c = self.chars.next();
        if let Some(ch) = c {
            self.position += ch.len_utf8();
        }
        c
    }

    /// Create an error at the current position
    pub(in crate::contract_parser) fn error(&self, message: &str) -> ParseError {
        ParseError {
            message: message.to_string(),
            position: self.position,
        }
    }

    /// Try to consume the given string, returning true if successful
    pub(in crate::contract_parser) fn try_consume(&mut self, s: &str) -> bool {
        self.skip_whitespace();
        let remaining = &self.input[self.position..];
        if remaining.starts_with(s) {
            for _ in s.chars() {
                self.advance();
            }
            true
        } else {
            false
        }
    }

    /// Try to consume a single `&`, but not `&&`.
    pub(in crate::contract_parser) fn try_consume_single_ampersand(&mut self) -> bool {
        self.skip_whitespace();
        let remaining = &self.input[self.position..];
        if remaining.starts_with("&&") {
            return false;
        }
        if remaining.starts_with('&') {
            self.advance();
            return true;
        }
        false
    }

    /// Try to consume a single `|`, but not `||`.
    pub(in crate::contract_parser) fn try_consume_single_pipe(&mut self) -> bool {
        self.skip_whitespace();
        let remaining = &self.input[self.position..];
        if remaining.starts_with("||") {
            return false;
        }
        if remaining.starts_with('|') {
            self.advance();
            return true;
        }
        false
    }

    /// Try to consume a single `.`, but not `..` (range operator). (#1513)
    pub(in crate::contract_parser) fn try_consume_single_dot(&mut self) -> bool {
        self.skip_whitespace();
        let remaining = &self.input[self.position..];
        if remaining.starts_with("..") {
            return false;
        }
        if remaining.starts_with('.') {
            self.advance();
            return true;
        }
        false
    }

    /// Try to consume a single `:`, but not `::` (path separator). (#type-ascription)
    ///
    /// Used by `parse_cast`/`parse_cast_spanned` to detect a type ascription
    /// `expr : Type`. A leading `::` is a path separator and must not be
    /// mistaken for an ascription colon.
    pub(in crate::contract_parser) fn try_consume_single_colon(&mut self) -> bool {
        self.skip_whitespace();
        let remaining = &self.input[self.position..];
        if remaining.starts_with("::") {
            return false;
        }
        if remaining.starts_with(':') {
            self.advance();
            return true;
        }
        false
    }

    /// Try to consume `==` but not `==>` (implication has lower precedence)
    pub(in crate::contract_parser) fn try_consume_eq_not_implies(&mut self) -> bool {
        self.skip_whitespace();
        let remaining = &self.input[self.position..];
        // Match `==` but NOT `==>`
        if remaining.starts_with("==") && !remaining.starts_with("==>") {
            self.advance();
            self.advance();
            true
        } else {
            false
        }
    }

    /// Try to consume a keyword, ensuring it doesn't match an identifier prefix.
    pub(in crate::contract_parser) fn try_consume_keyword(&mut self, s: &str) -> bool {
        self.skip_whitespace();
        let remaining = &self.input[self.position..];
        if !remaining.starts_with(s) {
            return false;
        }
        if remaining[s.len()..]
            .chars()
            .next()
            .is_some_and(Self::is_ident_continue)
        {
            return false;
        }
        for _ in s.chars() {
            self.advance();
        }
        true
    }

    pub(in crate::contract_parser) fn is_ident_continue(c: char) -> bool {
        c.is_ascii_alphanumeric() || c == '_' || c == ':'
    }

    /// If the next token sequence starts a macro invocation (`!(`, `![`, or `!{`),
    /// return the opening delimiter.
    pub(in crate::contract_parser) fn peek_macro_invocation_delimiter(&self) -> Option<char> {
        let mut chars = self.chars.clone();
        if chars.next()? != '!' {
            return None;
        }
        while chars.peek().is_some_and(|c| c.is_whitespace()) {
            chars.next();
        }
        match chars.peek().copied() {
            Some('(') => Some('('),
            Some('[') => Some('['),
            Some('{') => Some('{'),
            _ => None,
        }
    }
}
