// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Specifications for `std::string::String` and `str`
//!
//! These specifications define the contract semantics for String methods.
//! trust-wp-driver uses these specs when verifying code that uses String.
//!
//! Reference: Creusot's `creusot-std/src/std/string.rs`
//!
//! ## Design Notes
//!
//! `String` views as `Seq<char>` (logical sequence of characters) for verification.
//! The view relationship is: `s@` produces a `Seq<char>` with the same characters.

// Allow raw string hashes for spec string literals (consistency over optimization)
#![allow(clippy::needless_raw_string_hashes)]
// Allow doc_markdown pedantic warnings for contract notation
#![allow(clippy::doc_markdown)]

use crate::logic::Seq;

/// Specification trait for `String` methods (internal).
///
/// This trait documents the contracts for String methods using Seq<char> as the
/// logical model. **Users should call standard `String` methods directly** —
/// trust-wp-driver resolves these specs internally. The `_spec()` methods here
/// are for testing trust-wp-std itself.
pub trait StringSpec {
    /// Get the logical view of this String as a Seq<char>.
    fn view_spec(&self) -> Seq<char>;

    /// Specification: result == self.len() (byte length)
    fn len_spec(&self) -> usize;

    /// Specification: result == (self@.len() == 0)
    fn is_empty_spec(&self) -> bool;

    /// Specification: ensures length increases by string@.len()
    fn push_str_spec(&mut self, string: &str);

    /// Specification: ensures self@ == self@.push_back(ch)
    fn push_spec(&mut self, ch: char);

    /// Specification: capacity >= len
    fn capacity_spec(&self) -> usize;

    /// Specification: ensures len == 0
    fn clear_spec(&mut self);
}

impl StringSpec for String {
    fn view_spec(&self) -> Seq<char> {
        Seq::from(self.chars().collect::<Vec<char>>())
    }

    fn len_spec(&self) -> usize {
        self.len()
    }

    fn is_empty_spec(&self) -> bool {
        self.is_empty()
    }

    fn push_str_spec(&mut self, string: &str) {
        self.push_str(string);
    }

    fn push_spec(&mut self, ch: char) {
        self.push(ch);
    }

    fn capacity_spec(&self) -> usize {
        self.capacity()
    }

    fn clear_spec(&mut self) {
        self.clear();
    }
}

/// Internal specification definitions used by the driver's hardcoded fallback
/// tables and local tests. Builtin registry loading happens separately.
#[doc(hidden)]
pub mod specs {
    /// Contract for `String::new`
    pub const NEW: &str = r#"
        ensures: result@.len() == 0
    "#;

    /// Contract for `String::len`
    ///
    /// Note: len() returns byte length, not char count.
    /// The logical view models chars; byte length >= char count in UTF-8.
    pub const LEN: &str = r#"
        ensures: result@ >= self@.len()
        ensures: self@.len() == 1 ==> result@ == self@.index_logic(0).to_utf8().len()
    "#;

    /// Contract for `String::is_empty`
    pub const IS_EMPTY: &str = r#"
        ensures: result == (self.len() == 0)
    "#;

    /// Contract for `String::push_str`
    pub const PUSH_STR: &str = r#"
        params: self, string
        ensures: (^self)@.len() == self@.len() + string@.len()
    "#;

    /// Contract for `String::push`
    pub const PUSH: &str = r#"
        params: self, ch
        ensures: (^self)@ == self@.push_back(ch)
    "#;

    /// Contract for `String::capacity`
    pub const CAPACITY: &str = r#"
        ensures: result@ >= self.len()
    "#;

    /// Contract for `String::clear`
    pub const CLEAR: &str = r#"
        ensures: (^self).len() == 0
    "#;

    /// Contract for `str::len`
    pub const STR_LEN: &str = r#"
        ensures: result >= 0
        ensures: self@.len() == 1 ==> result@ == self@.index_logic(0).to_utf8().len()
    "#;

    /// Contract for `str::is_empty`
    pub const STR_IS_EMPTY: &str = r#"
        ensures: result == (self.len() == 0)
    "#;

    /// Contract for `String::from(&str)` (From<&str> for String)
    ///
    /// Creates a new String from a string slice. The resulting String
    /// has the same logical view (char sequence) as the source str.
    pub const FROM_STR: &str = r#"
        params: s
        ensures: result@.len() == s@.len()
        ensures: result@ == s@
    "#;

    /// Contract for `String::as_str` / String → &str coercion
    ///
    /// The returned str slice has the same logical view as the String.
    pub const AS_STR: &str = r#"
        ensures: result@ == self@
    "#;

    /// Contract for `String::truncate`
    ///
    /// Shortens the string to the specified length.
    pub const TRUNCATE: &str = r#"
        params: self, new_len
        ensures: (^self).len() <= self.len()
    "#;

    /// Contract for `String::contains`
    ///
    /// Returns true if the string contains the given pattern.
    pub const CONTAINS: &str = r#"
        params: self, pat
    "#;

    /// Contract for `String::starts_with`
    pub const STARTS_WITH: &str = r#"
        params: self, pat
    "#;

    /// Contract for `String::ends_with`
    pub const ENDS_WITH: &str = r#"
        params: self, pat
    "#;

    /// Contract for `str::contains`
    pub const STR_CONTAINS: &str = r#"
        params: self, pat
    "#;

    /// Contract for `str::starts_with`
    pub const STR_STARTS_WITH: &str = r#"
        params: self, pat
    "#;

    /// Contract for `str::ends_with`
    pub const STR_ENDS_WITH: &str = r#"
        params: self, pat
    "#;

    /// Contract for `str::trim`
    pub const STR_TRIM: &str = r#"
        ensures: result.len() <= self.len()
    "#;

    /// Contract for `str::to_string` / `ToString::to_string`
    pub const TO_STRING: &str = r#"
        ensures: result@ == self@
    "#;

    /// Contract for `str::chars`
    pub const STR_CHARS: &str = r#"
        params: self
    "#;

    /// Contract for `str::bytes`
    pub const STR_BYTES: &str = r#"
        params: self
    "#;

    /// Contract for `String::reserve`
    pub const RESERVE: &str = r#"
        params: self, additional
        ensures: (^self)@ == self@
    "#;

    /// Contract for `String::with_capacity`
    pub const WITH_CAPACITY: &str = r#"
        ensures: result@.len() == 0
    "#;

    /// Contract for `String::insert`
    pub const INSERT: &str = r#"
        params: self, idx, ch
    "#;

    /// Contract for `String::insert_str`
    pub const INSERT_STR: &str = r#"
        params: self, idx, string
    "#;

    /// Contract for `String::pop`
    pub const POP: &str = r#"
        ensures: self@.len() == 0 ==> result == None
    "#;

    /// Contract for `String::remove`
    pub const REMOVE: &str = r#"
        params: self, idx
    "#;

    /// Contract for `String::retain`
    pub const RETAIN: &str = r#"
        params: self, f
        ensures: (^self).len() <= self.len()
    "#;

    /// Contract for `str::to_owned` / `ToOwned::to_owned`
    ///
    /// Creates an owned String from a string slice, preserving the logical view.
    pub const TO_OWNED: &str = r#"
        ensures: result@ == self@
    "#;

    /// Contract for `str::to_lowercase` — creates new String with lowercase chars.
    /// Cannot express character-level transformation in SMT; prevents opaque fallback.
    pub const TO_LOWERCASE: &str = r#"
        params: self
    "#;

    /// Contract for `str::to_uppercase` — creates new String with uppercase chars.
    /// Cannot express character-level transformation in SMT; prevents opaque fallback.
    pub const TO_UPPERCASE: &str = r#"
        params: self
    "#;

    /// Contract for `str::split` — splits string by pattern, returns iterator.
    /// Prevents opaque-call fallback.
    pub const STR_SPLIT: &str = r#"
        params: self, pat
    "#;

    /// Contract for `str::split_at`.
    ///
    /// `str::split_at` takes a byte index. The singleton UTF-8 clause recovers
    /// the common Creusot pattern where a one-character string is split at that
    /// character's encoded byte length. The singleton-case clauses use
    /// `self@.index_logic(0).to_utf8().len()` so callers with view-level facts
    /// (e.g. `s@ == seq!['c']` plus `'c'.to_utf8() == seq![...]`) can discharge
    /// them without needing `self.len()`.
    ///
    /// The ensures guards deliberately do NOT use `self.len()`: in the contract
    /// DSL that lowers to `seq_len(self@)` = CHAR count (expr_printer
    /// method_smt_name), which for a multi-byte singleton (e.g. 'Ã', 2 bytes)
    /// can never equal the byte index `mid@` — making the guards unsatisfiable
    /// and every postcondition vacuous (decoded live: guard `2 == seq_len(s)`
    /// vs premise `seq_len(s) == 1`; blocked cc/string). The singleton-UTF8
    /// guard states the same full-split condition in derivable terms, and the
    /// empty-tail ensures asserts FULL seq equality to `Seq::empty()` (not just
    /// `.len() == 0`) because the preamble has no `len s == 0 ==> s == empty`
    /// extensionality axiom. SOUND: for a 1-char str, byte_len ==
    /// to_utf8(c).len() and split_at(byte_len) == (self, ""). (#route-100 r4)
    pub const STR_SPLIT_AT: &str = r#"
        params: self, mid
        requires: 0 <= mid@
        requires: self@.len() == 1 ==> mid@ <= self@.index_logic(0).to_utf8().len()
        requires: self@.len() != 1 ==> mid@ <= self.len()
        ensures: self@.len() == 1 && mid@ == self@.index_logic(0).to_utf8().len() ==> result.0@ == self@
        ensures: self@.len() == 1 && mid@ == self@.index_logic(0).to_utf8().len() ==> result.1@ == Seq::empty()
    "#;

    /// Contract for `str::split_whitespace` — splits on whitespace, returns iterator.
    pub const STR_SPLIT_WHITESPACE: &str = r#"
        params: self
    "#;

    /// Contract for `str::lines` — returns line iterator.
    pub const STR_LINES: &str = r#"
        params: self
    "#;

    /// Contract for `str::trim_start` — removes leading whitespace.
    pub const STR_TRIM_START: &str = r#"
        params: self
    "#;

    /// Contract for `str::trim_end` — removes trailing whitespace.
    pub const STR_TRIM_END: &str = r#"
        params: self
    "#;

    /// Contract for `str::replace` — replaces occurrences of pattern with replacement.
    pub const STR_REPLACE: &str = r#"
        params: self, from, to
    "#;

    /// Contract for `str::as_bytes` — view string as byte slice.
    pub const STR_AS_BYTES: &str = r#"
        params: self
    "#;

    /// Contract for `str::parse` — parses string into a type via FromStr.
    pub const STR_PARSE: &str = r#"
        params: self
    "#;

    /// Contract for `str::find` — returns first position of pattern match.
    /// Conservative: unconstrained result, only guarantees index < len when Some.
    pub const STR_FIND: &str = r#"
        params: self, pat
        ensures: match result {
            Some(i) => i < self@.len(),
            None => true,
        }
    "#;

    /// Contract for `str::rfind` — returns last position of pattern match.
    /// Conservative: unconstrained result, only guarantees index < len when Some.
    pub const STR_RFIND: &str = r#"
        params: self, pat
        ensures: match result {
            Some(i) => i < self@.len(),
            None => true,
        }
    "#;

    /// Contract for `str::get` — returns a substring as `Option<&str>`.
    pub const STR_GET: &str = r#"
        params: self, index
    "#;

    /// Contract for `str::splitn` — returns iterator splitting at most n times.
    pub const STR_SPLITN: &str = r#"
        params: self, n, pat
    "#;

    /// Contract for `str::rsplitn` — returns iterator splitting from end at most n times.
    pub const STR_RSPLITN: &str = r#"
        params: self, n, pat
    "#;

    /// Contract for `str::repeat` — repeats a string n times.
    pub const STR_REPEAT: &str = r#"
        params: self, n
        ensures: result@.len() == self@.len() * n
    "#;

    /// Contract for `str::to_ascii_lowercase` — returns ASCII lowercase version.
    /// Length is preserved since ASCII case conversion is char-for-char.
    pub const STR_TO_ASCII_LOWERCASE: &str = r#"
        params: self
        ensures: result@.len() == self@.len()
    "#;

    /// Contract for `str::to_ascii_uppercase` — returns ASCII uppercase version.
    /// Length is preserved since ASCII case conversion is char-for-char.
    pub const STR_TO_ASCII_UPPERCASE: &str = r#"
        params: self
        ensures: result@.len() == self@.len()
    "#;
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_string_view_spec() {
        let s = String::from("hello");
        let seq = s.view_spec();
        assert_eq!(seq.len().0, 5);
    }

    #[test]
    fn test_string_len_spec() {
        let s = String::from("hello");
        assert_eq!(s.len_spec(), 5);
    }

    #[test]
    fn test_string_is_empty_spec() {
        let empty = String::new();
        let non_empty = String::from("x");
        assert!(empty.is_empty_spec());
        assert!(!non_empty.is_empty_spec());
    }

    #[test]
    fn test_string_push_specs() {
        let mut s = String::from("hi");
        s.push_str_spec("!");
        s.push_spec('!');
        assert_eq!(s, "hi!!");
    }

    #[test]
    fn test_string_capacity_spec() {
        let s = String::from("hello");
        assert!(s.capacity_spec() >= s.len());
    }

    #[test]
    fn test_string_clear_spec() {
        let mut s = String::from("hello");
        s.clear_spec();
        assert!(s.is_empty());
    }
}
