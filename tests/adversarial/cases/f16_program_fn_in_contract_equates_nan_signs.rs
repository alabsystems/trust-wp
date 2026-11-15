//@ expect: reject
//@ ay-not-unsat: same16
//@ mechanism: the `f16`/`f128` twins of f64_program_fn_in_contract_equates_nan_signs.rs. The float model has
//@ mechanism: one NaN (D-216), and D-217 keeps it for `f16`/`f128`, so a contract's logical `x == y` holds of
//@ mechanism: `f16::NAN` and `-f16::NAN`; a program function a contract applies is read as an uninterpreted
//@ mechanism: function of the model value, and congruence equates `sign16(x)` with `sign16(y)`, which
//@ mechanism: `is_sign_negative` tells apart. Over an `f64` argument ay answers unknown, since its
//@ mechanism: floating-point path does not decide a variable under congruence; an `f16`/`f128` value is an
//@ mechanism: element of an uninterpreted sort under D-217, which needs no floating-point reasoning, so ay
//@ mechanism: answers unsat, and only the demotion of the placeholder's integer-carried argument
//@ mechanism: (`sort_fallback_to_int_from_logic_fn`), which is no float guard, withholds the credit. The
//@ mechanism: same holds of `f128` (`same128`) and through `to_bits` (`same_bits16`).
//@ accept-means: `same16(f16::NAN, -f16::NAN)` meets the precondition, and `sign16` returns `false` for the
//@ accept-means: first argument and `true` for the second; an accept claims they agree.
//@ fixed-by: OPEN — committed RED rather than hidden (D-216).
//@ teeth: TEETH LOST when committed: ay answers unsat on `same16`, `same128` and `same_bits16`, and each is
//@ teeth: reported unknown only by the sort-fallback demotion; `ay-not-unsat` fails until the model or the
//@ teeth: placeholder reading changes.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![feature(f16)]
#![feature(f128)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn sign16(x: f16) -> bool {
    x.is_sign_negative()
}

#[requires(x == y)]
#[ensures(sign16(x) == sign16(y))]
pub fn same16(x: f16, y: f16) {}

pub fn sign128(x: f128) -> bool {
    x.is_sign_negative()
}

#[requires(x == y)]
#[ensures(sign128(x) == sign128(y))]
pub fn same128(x: f128, y: f128) {}

pub fn bits16(x: f16) -> u16 {
    x.to_bits()
}

#[requires(x == y)]
#[ensures(bits16(x) == bits16(y))]
pub fn same_bits16(x: f16, y: f16) {}
