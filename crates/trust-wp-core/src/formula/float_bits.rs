// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! IEEE 754 float value stored as bit pattern for `Eq`/`Hash` compatibility.

/// IEEE 754 float value stored as bit pattern for `Eq`/`Hash` compatibility.
///
/// `PureExpr` derives `Eq` which `f64` does not implement. Storing the bit
/// representation via `f64::to_bits()` gives us bit-exact equality and lets
/// `FloatBits` participate in `Eq`/`Hash` derives. `f32` values are losslessly
/// promoted to `f64` before storage.
///
/// Conversion: `FloatBits::from_f64(v)` / `FloatBits::to_f64()`.
/// NaN/Inf are representable (the encoder rejects them at encoding time).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct FloatBits(pub u64);

impl FloatBits {
    /// Create from an `f64` value.
    #[must_use]
    pub fn from_f64(v: f64) -> Self {
        Self(v.to_bits())
    }

    /// Create from an `f32` value (losslessly promoted to f64).
    #[must_use]
    pub fn from_f32(v: f32) -> Self {
        Self::from_f64(f64::from(v))
    }

    /// Convert back to `f64`.
    #[must_use]
    pub fn to_f64(self) -> f64 {
        f64::from_bits(self.0)
    }
}

impl std::fmt::Display for FloatBits {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_f64())
    }
}
