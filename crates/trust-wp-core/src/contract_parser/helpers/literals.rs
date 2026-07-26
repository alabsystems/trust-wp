// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Integer/float literal and tuple field index parsing.

use super::super::{ContractParser, ParseError};
use crate::formula::{FloatBits, PureExpr};

impl ContractParser<'_> {
    /// Parse a numeric literal in expression position as either an integer
    /// (`PureExpr::Int`) or a float (`PureExpr::Float`).
    ///
    /// This is the expression-context entry point. It first parses the integer
    /// part exactly like [`Self::try_parse_integer`], then — for *decimal*
    /// literals only — checks for a float continuation:
    ///
    /// - a fractional part: `.` immediately followed by an ASCII digit
    ///   (e.g. `1.5`), or
    /// - an exponent: `e`/`E` optionally followed by a sign and digits
    ///   (e.g. `2e10`, `3E-4`).
    ///
    /// # Disambiguation
    ///
    /// A `.` only starts a fractional part when the next character is a digit.
    /// This deliberately rejects:
    /// - `a..b` / `a..=b` range syntax (`.` is followed by `.`), and
    /// - method/field access like `x.foo` or tuple-index `x.0` — those are
    ///   parsed in postfix position on a *non-numeric* receiver and never
    ///   reach this number parser. (Within a numeric literal, `1.0` is
    ///   unambiguously a float, matching Rust/Pearlite.)
    ///
    /// Hex literals (`0x..`) are never floats and are returned as `Int`.
    ///
    /// Patterns stay integer-only by continuing to call
    /// [`Self::try_parse_integer`] directly.
    pub(in crate::contract_parser) fn try_parse_number(
        &mut self,
    ) -> Result<Option<PureExpr>, ParseError> {
        self.skip_whitespace();
        let start_pos = self.position;

        // Optional negative sign.
        let mut neg = false;
        if self.peek() == Some('-') {
            // Only treat as a numeric sign if a digit follows; otherwise leave
            // it for the unary-minus path (handled by the caller).
            if self.input[self.position..]
                .chars()
                .nth(1)
                .is_some_and(|c| c.is_ascii_digit())
            {
                neg = true;
                self.advance();
            } else {
                return Ok(None);
            }
        }

        // Must have at least one digit to be a number.
        if !self.peek().is_some_and(|c| c.is_ascii_digit()) {
            self.reset_to(start_pos);
            return Ok(None);
        }

        // Hex prefix: `0x` / `0X`. Hex literals are integer-only.
        if self.peek() == Some('0') {
            let after_zero = self.input[self.position..].chars().nth(1);
            if after_zero.is_some_and(|c| c == 'x' || c == 'X') {
                // Delegate to the integer parser (which handles hex), but it
                // does not consume a leading sign, so parse from here and apply
                // the sign ourselves.
                let hex = self.try_parse_integer()?;
                return Ok(hex.map(|n| PureExpr::Int(if neg { -n } else { n })));
            }
        }

        // Decimal integer digits.
        let mut int_part = String::new();
        if neg {
            int_part.push('-');
        }
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                int_part.push(c);
                self.advance();
            } else if c == '_' {
                self.advance();
            } else {
                break;
            }
        }

        // Detect a float continuation: `.digit` or `e`/`E` exponent.
        let has_frac = self.peek() == Some('.')
            && self.input[self.position..]
                .chars()
                .nth(1)
                .is_some_and(|c| c.is_ascii_digit());
        let has_exp = matches!(self.peek(), Some('e' | 'E'))
            && Self::exponent_follows(&self.input[self.position..]);

        if has_frac || has_exp {
            let mut lit = int_part;

            if has_frac {
                // Consume '.' and the fractional digits.
                self.advance(); // '.'
                lit.push('.');
                while let Some(c) = self.peek() {
                    if c.is_ascii_digit() {
                        lit.push(c);
                        self.advance();
                    } else if c == '_' {
                        self.advance();
                    } else {
                        break;
                    }
                }
            }

            // Optional exponent (may follow either a fractional part or the
            // integer part directly, e.g. `1e10` or `1.5e-3`).
            if matches!(self.peek(), Some('e' | 'E'))
                && Self::exponent_follows(&self.input[self.position..])
            {
                lit.push('e');
                self.advance(); // 'e' / 'E'
                if matches!(self.peek(), Some('+' | '-')) {
                    if self.peek() == Some('-') {
                        lit.push('-');
                    }
                    self.advance();
                }
                while let Some(c) = self.peek() {
                    if c.is_ascii_digit() {
                        lit.push(c);
                        self.advance();
                    } else if c == '_' {
                        self.advance();
                    } else {
                        break;
                    }
                }
            }

            // Optional float type suffix (`f32` / `f64`), discarded — contract
            // floats are mathematical reals.
            self.try_consume_float_type_suffix();

            return match lit.parse::<f64>() {
                Ok(v) => Ok(Some(PureExpr::Float(FloatBits::from_f64(v)))),
                Err(_) => Err(self.error(&format!("invalid float literal '{lit}'"))),
            };
        }

        // Not a float — finish as an integer (consume any int type suffix).
        self.try_consume_integer_type_suffix();
        match int_part.parse::<i64>() {
            Ok(n) => Ok(Some(PureExpr::Int(n))),
            Err(_) => Err(self.error(&format!(
                "integer literal '{int_part}' overflows i64 (max {})",
                i64::MAX
            ))),
        }
    }

    /// Returns `true` when an `e`/`E` at the start of `rest` begins a genuine
    /// float exponent — i.e. it is followed by a digit, or by a sign and then
    /// a digit. This avoids misreading a trailing identifier/`else` as an
    /// exponent (e.g. `1 else ...` never reaches here, but `1err` would).
    fn exponent_follows(rest: &str) -> bool {
        let mut chars = rest.chars();
        // Skip the 'e'/'E'.
        chars.next();
        match chars.next() {
            Some(c) if c.is_ascii_digit() => true,
            Some('+' | '-') => chars.next().is_some_and(|c| c.is_ascii_digit()),
            _ => false,
        }
    }

    /// Consume a float type suffix (`f32` / `f64`) if present. Discarded.
    fn try_consume_float_type_suffix(&mut self) {
        let remaining = &self.input[self.position..];
        for suffix in ["f32", "f64"] {
            if let Some(rest) = remaining.strip_prefix(suffix) {
                if !rest.starts_with(|c: char| c.is_alphanumeric() || c == '_') {
                    for _ in suffix.chars() {
                        self.advance();
                    }
                    return;
                }
            }
        }
    }

    /// Reset the parser cursor to `pos`, rebuilding the char iterator.
    fn reset_to(&mut self, pos: usize) {
        self.position = pos;
        self.chars = self.input[pos..].chars().peekable();
    }

    pub(in crate::contract_parser) fn try_parse_integer(
        &mut self,
    ) -> Result<Option<i64>, ParseError> {
        self.skip_whitespace();
        let start_pos = self.position;
        let mut s = String::new();

        // Optional negative sign
        if self.peek() == Some('-') {
            s.push('-');
            self.advance();
        }

        // Must have at least one digit
        if !self.peek().is_some_and(|c| c.is_ascii_digit()) {
            // Backtrack if we consumed a minus sign
            if !s.is_empty() {
                self.position = start_pos;
                self.chars = self.input[start_pos..].chars().peekable();
            }
            return Ok(None);
        }

        // Check for hex prefix: 0x or 0X (#1513)
        if self.peek() == Some('0') {
            self.advance();
            s.push('0');
            if self.peek().is_some_and(|c| c == 'x' || c == 'X') {
                self.advance();
                // Parse hex digits
                let mut hex = String::new();
                while let Some(c) = self.peek() {
                    if c.is_ascii_hexdigit() {
                        hex.push(c);
                        self.advance();
                    } else if c == '_' {
                        self.advance();
                    } else {
                        break;
                    }
                }
                if hex.is_empty() {
                    return Err(self.error("expected hex digit after 0x prefix"));
                }
                self.try_consume_integer_type_suffix();
                let is_neg = s.starts_with('-');
                return match i64::from_str_radix(&hex, 16) {
                    Ok(n) => Ok(Some(if is_neg { -n } else { n })),
                    Err(_) => Err(self.error(&format!("hex literal '0x{hex}' overflows i64"))),
                };
            }
            // Not hex — continue parsing decimal digits after the '0'
        }

        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                s.push(c);
                self.advance();
            } else if c == '_' {
                // Rust-style underscore separators in integer literals (e.g., 1_000_000)
                // Skip underscores — they are visual separators only
                self.advance();
            } else {
                break;
            }
        }

        // Consume optional Rust/type-like suffix (u8, u16, u32, u64, u128,
        // usize, i8, i16, i32, i64, i128, isize, int). These are ignored —
        // all integers are treated as mathematical Int in contract logic.
        self.try_consume_integer_type_suffix();

        match s.parse::<i64>() {
            Ok(n) => Ok(Some(n)),
            Err(_) => Err(self.error(&format!(
                "integer literal '{s}' overflows i64 (max {})",
                i64::MAX
            ))),
        }
    }

    /// Consume an integer type suffix if present (e.g., `u32`, `usize`, `i64`, `int`).
    /// The suffix is discarded — contract integers are untyped mathematical values.
    fn try_consume_integer_type_suffix(&mut self) {
        let remaining = &self.input[self.position..];
        let suffixes = [
            "u128", "u64", "u32", "u16", "u8", "usize", "i128", "i64", "i32", "i16", "i8", "isize",
            "int",
        ];
        for suffix in &suffixes {
            if let Some(rest) = remaining.strip_prefix(suffix) {
                // Only consume if next char after suffix is not alphanumeric
                // (avoid consuming prefix of an identifier like `u32var`)
                if !rest.starts_with(|c: char| c.is_alphanumeric()) {
                    for _ in suffix.chars() {
                        self.advance();
                    }
                    return;
                }
            }
        }
    }

    /// Try to parse a tuple field index (e.g., `0`, `1`, `12`).
    ///
    /// Called after consuming `.` when the next character is a digit.
    /// Returns `Some(index)` if a valid integer index is found,
    /// `None` otherwise (without consuming any characters).
    pub(in crate::contract_parser) fn try_parse_tuple_field_index(&mut self) -> Option<usize> {
        self.skip_whitespace();
        let c = self.peek()?;
        if !c.is_ascii_digit() {
            return None;
        }
        let start_pos = self.position;
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() {
                s.push(c);
                self.advance();
            } else {
                break;
            }
        }
        if let Ok(index) = s.parse::<usize>() {
            Some(index)
        } else {
            // Backtrack on parse failure (extremely large index)
            self.position = start_pos;
            self.chars = self.input[start_pos..].chars().peekable();
            None
        }
    }
}
