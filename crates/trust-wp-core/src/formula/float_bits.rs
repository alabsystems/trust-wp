// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! IEEE-754 float literals and the two binary formats Rust's floats use.

/// An IEEE-754 binary format: Rust's `f32` (binary32) or `f64` (binary64).
///
/// A float value is a point of one of these formats, never a real number:
/// every operation on it rounds, and NaN and the two infinities and zeros are
/// values of it. The width therefore travels with every float sort and every
/// float literal, because the same decimal names different values in the two
/// formats (`0.1f32 as f64 != 0.1f64`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum FloatWidth {
    /// binary32: 8 exponent bits, 24 significand bits (hidden bit included).
    F32,
    /// binary64: 11 exponent bits, 53 significand bits (hidden bit included).
    F64,
}

impl FloatWidth {
    /// Exponent field width, the `eb` of SMT-LIB's `(_ FloatingPoint eb sb)`.
    #[must_use]
    pub const fn exponent_bits(self) -> u32 {
        match self {
            Self::F32 => 8,
            Self::F64 => 11,
        }
    }

    /// Significand width including the hidden bit, the `sb` of SMT-LIB's
    /// `(_ FloatingPoint eb sb)`.
    #[must_use]
    pub const fn significand_bits(self) -> u32 {
        match self {
            Self::F32 => 24,
            Self::F64 => 53,
        }
    }

    /// The Rust type name (`f32` / `f64`), also the spelling used inside the
    /// IEEE builtin names.
    #[must_use]
    pub const fn rust_name(self) -> &'static str {
        match self {
            Self::F32 => "f32",
            Self::F64 => "f64",
        }
    }

    /// The width named by a Rust type name.
    #[must_use]
    pub fn from_rust_name(name: &str) -> Option<Self> {
        match name {
            "f32" => Some(Self::F32),
            "f64" => Some(Self::F64),
            _ => None,
        }
    }
}

/// A float literal: a value of one IEEE-754 format, stored by bit pattern so
/// that `PureExpr` can derive `Eq`/`Hash`.
///
/// `width` is `None` only for an unsuffixed literal written in a contract,
/// whose format is the one its Rust context infers (`result == 0.1` over an
/// `f32` result means `0.1f32`). Such a literal keeps the decimal rounded
/// directly into EACH format, which is what rustc does once it has inferred
/// the type: rounding it to `f64` first and then to `f32` can land on a
/// different `f32` value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FloatBits {
    /// The value's `f64` bit pattern (an `f32` is widened exactly; an
    /// unsuffixed literal's is its own `f64` rounding).
    value: u64,
    /// An unsuffixed literal's own `f32` rounding; `0` for a suffixed one.
    narrow: u32,
    width: Option<FloatWidth>,
}

impl FloatBits {
    /// An `f64` value.
    #[must_use]
    pub fn from_f64(v: f64) -> Self {
        Self {
            value: v.to_bits(),
            narrow: 0,
            width: Some(FloatWidth::F64),
        }
    }

    /// An `f32` value.
    #[must_use]
    pub fn from_f32(v: f32) -> Self {
        Self {
            value: f64::from(v).to_bits(),
            narrow: 0,
            width: Some(FloatWidth::F32),
        }
    }

    /// An unsuffixed contract literal, from its decimal spelling (no `_`,
    /// no suffix), whose format its context decides (see the type docs).
    /// `None` when the spelling is not a float literal.
    #[must_use]
    pub fn unsuffixed(decimal: &str) -> Option<Self> {
        let wide: f64 = decimal.parse().ok()?;
        let narrow: f32 = decimal.parse().ok()?;
        Some(Self {
            value: wide.to_bits(),
            narrow: narrow.to_bits(),
            width: None,
        })
    }

    /// The literal's format, or `None` for an unsuffixed contract literal.
    #[must_use]
    pub fn width(self) -> Option<FloatWidth> {
        self.width
    }

    /// The value, widened to `f64` (exact for both formats).
    #[must_use]
    pub fn to_f64(self) -> f64 {
        f64::from_bits(self.value)
    }

    /// The same value as a literal of format `width`, when it is one.
    ///
    /// A literal already of another format is `None`: `as` between float
    /// types is an operation, not a spelling. An unsuffixed literal takes its
    /// own rounding into `width`.
    #[must_use]
    pub fn in_width(self, width: FloatWidth) -> Option<Self> {
        match (self.width, width) {
            (Some(own), _) if own == width => Some(self),
            (Some(_), _) => None,
            (None, FloatWidth::F64) => Some(Self::from_f64(self.to_f64())),
            (None, FloatWidth::F32) => Some(Self::from_f32(f32::from_bits(self.narrow))),
        }
    }

    /// The IEEE-754 bit pattern of this literal in its own format (`None` for
    /// an unsuffixed literal, whose format is not decided yet).
    #[must_use]
    #[allow(clippy::cast_possible_truncation)] // an f32 literal's value is an f32 value
    pub fn ieee_bits(self) -> Option<u64> {
        match self.width? {
            FloatWidth::F64 => Some(self.value),
            FloatWidth::F32 => Some(u64::from((self.to_f64() as f32).to_bits())),
        }
    }
}

impl std::fmt::Display for FloatBits {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_f64())
    }
}
