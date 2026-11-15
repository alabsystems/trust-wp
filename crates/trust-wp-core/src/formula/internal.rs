// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Workspace-internal helper APIs for formula lowering.
//!
//! These modules are intentionally exposed so `trust-wp-driver` and `trust-wp-ay`
//! can share encoding conventions with `trust-wp-core`, but they are not part of
//! the stable semantic AST API. External users should prefer
//! `trust_wp_core::formula::{Formula, PureExpr, Pattern, ...}` and treat
//! `formula::internal::*` as unstable implementation detail.

/// Synthetic builtin logic-function names shared across crates.
pub mod builtins {
    /// Prefix of a std-spec term only a call site can resolve; the encoder
    /// refuses any that reaches it.
    pub const STD_SITE_MARKER_PREFIX: &str = super::super::types::STD_SITE_MARKER_PREFIX;

    /// Uninterpreted metadata-stripping cast of a raw pointer.
    pub const PTR_THIN_LOGIC_FN: &str = super::super::types::PTR_THIN_LOGIC_FN;

    /// Prefix of a clause's raw-pointer cast the driver has not classified;
    /// the encoder refuses any that reaches it.
    pub const PTR_CAST_PENDING_PREFIX: &str = super::super::types::PTR_CAST_PENDING_PREFIX;

    /// Prefix of the uninterpreted function of a raw-pointer cast's type
    /// pair (an unsizing, or a cast neither the identity nor `thin`).
    pub const PTR_PAIR_LOGIC_FN_PREFIX: &str = super::super::types::PTR_PAIR_LOGIC_FN_PREFIX;
}

/// Synthetic symbol naming helpers used by tuple lowering.
pub mod tuple_lowering {
    /// Prefix used for synthetic logic-function encodings of tuple literals.
    pub const TUPLE_LOGIC_FN_PREFIX: &str = super::super::types::TUPLE_LOGIC_FN_PREFIX;

    /// Prefix used for synthetic logic-function encodings of tuple field access.
    pub const TUPLE_FIELD_LOGIC_FN_PREFIX: &str = super::super::types::TUPLE_FIELD_LOGIC_FN_PREFIX;

    /// Prefix used for synthetic logic-function encodings of named struct field access.
    pub const NAMED_FIELD_LOGIC_FN_PREFIX: &str = super::super::types::NAMED_FIELD_LOGIC_FN_PREFIX;

    /// Build the synthetic logic-function name for an N-ary tuple literal.
    #[must_use]
    pub fn tuple_logic_fn_name(arity: usize) -> String {
        super::super::types::tuple_logic_fn_name(arity)
    }

    /// Parse a synthetic tuple logic-function name and recover its arity.
    #[must_use]
    pub fn tuple_logic_fn_arity(name: &str) -> Option<usize> {
        super::super::types::tuple_logic_fn_arity(name)
    }

    /// Build the synthetic logic-function name for tuple field access.
    #[must_use]
    pub fn tuple_field_logic_fn_name(index: usize) -> String {
        super::super::types::tuple_field_logic_fn_name(index)
    }

    /// Parse a synthetic tuple field logic-function name and recover its field index.
    #[must_use]
    pub fn tuple_field_logic_fn_index(name: &str) -> Option<usize> {
        super::super::types::tuple_field_logic_fn_index(name)
    }
}

/// The type marker of a machine-integer bit operation (D-242).
///
/// A MIR `&`, `|`, `^`, `<<`, `>>` or `!` on a machine integer is lowered to
/// the plain `PureExpr` operator, which names no width: the encoder reads an
/// unannotated bit operator at 64 bits with an UNSIGNED `bv2int`, which is the
/// Rust operation only for an unsigned type of at most 64 bits and only for
/// the operators whose result never leaves the type (`&`, `|`, `^`, `>>`). The
/// driver therefore wraps every other machine bit operation in
/// `__trust_wp_int_bitop_{s|u}{bits}(op)` — the operation AT the type of its
/// (left) operand — and the encoder computes it at `bits` with that
/// signedness. Value-wise the marker is the Rust result: `<<` drops the bits
/// shifted out of the type, `!` complements within it, a signed result is read
/// as two's complement, and a signed `>>` is arithmetic.
pub mod machine_bitop {
    /// Prefix of the marker name.
    pub const PREFIX: &str = "__trust_wp_int_bitop_";

    /// The marker name for a `bits`-wide integer of the given signedness.
    #[must_use]
    pub fn name(signed: bool, bits: u32) -> String {
        format!("{PREFIX}{}{bits}", if signed { 's' } else { 'u' })
    }

    /// Parse a marker name into `(bits, signed)`.
    #[must_use]
    pub fn parse(name: &str) -> Option<(u32, bool)> {
        let suffix = name.strip_prefix(PREFIX)?;
        let (signed, digits) = if let Some(rest) = suffix.strip_prefix('s') {
            (true, rest)
        } else {
            (false, suffix.strip_prefix('u')?)
        };
        if digits.is_empty() || !digits.bytes().all(|b| b.is_ascii_digit()) {
            return None;
        }
        let bits: u32 = digits.parse().ok()?;
        (1..=128).contains(&bits).then_some((bits, signed))
    }

    /// Whether the unannotated reading (64 bits, unsigned `bv2int`) differs
    /// from the Rust operation for this operator at this type, i.e. whether
    /// the driver must emit the marker. `complement` is `!`; `shift_left` is
    /// `<<`; every other operator is `&`, `|`, `^` or `>>`.
    #[must_use]
    pub fn needed(signed: bool, bits: u32, complement: bool, shift_left: bool) -> bool {
        if signed || bits > 64 {
            // A negative result read through an unsigned `bv2int`, a signed
            // `>>` read as logical, or a 128-bit operand cut to 64 bits.
            return true;
        }
        // Unsigned and at most 64 bits: `&`, `|`, `^`, `>>` of in-range
        // operands stay in range; `<<` and `!` leave the type below 64 bits.
        (complement || shift_left) && bits < 64
    }
}

#[cfg(test)]
mod tests {
    use super::machine_bitop;

    #[test]
    fn machine_bitop_name_round_trips() {
        for signed in [false, true] {
            for bits in [8, 16, 32, 64, 128] {
                assert_eq!(
                    machine_bitop::parse(&machine_bitop::name(signed, bits)),
                    Some((bits, signed))
                );
            }
        }
        for name in [
            "__trust_wp_int_bitop_x8",
            "__trust_wp_int_bitop_u",
            "__trust_wp_int_bitop_u0",
            "__trust_wp_int_bitop_u+8",
            "__trust_wp_int_bitop_s129",
            "__trust_wp_int_truncate_u8",
        ] {
            assert_eq!(machine_bitop::parse(name), None, "{name}");
        }
    }

    /// Exactly the operations the 64-bit unsigned reading gets wrong are
    /// marked: below 64 bits an unsigned `<<` or `!` leaves the type, and
    /// every signed and every 128-bit operation is misread.
    #[test]
    fn machine_bitop_marks_what_the_bare_reading_misreads() {
        assert!(machine_bitop::needed(false, 8, false, true));
        assert!(machine_bitop::needed(false, 32, true, false));
        assert!(!machine_bitop::needed(false, 8, false, false));
        assert!(!machine_bitop::needed(false, 64, false, true));
        assert!(!machine_bitop::needed(false, 64, true, false));
        assert!(machine_bitop::needed(true, 8, false, false));
        assert!(machine_bitop::needed(true, 64, false, false));
        assert!(machine_bitop::needed(false, 128, false, false));
    }
}
