//@ expect: reject
//@ verdict: error
//@ refused-with: as std::ops::Add>` runs outside ghost!(...) and snapshot!(...)
//@ mechanism: trust-wp-std's `Int` is `Int(pub i128)` at run time, and its operators and conversions
//@ mechanism: are ordinary Rust on that `i128`: `+` overflows past `i128::MAX`, `/` divides by zero,
//@ mechanism: and `Int::from(u128)` panics past `i128::MAX` ("u128 value exceeds Int host range").
//@ mechanism: Program code may build and compute with an `Int`, and the verifier reads each operation as
//@ mechanism: the unbounded logical one, which has no panic to owe. Under Creusot `Int`'s operations are
//@ mechanism: logic functions, which program code cannot call. The program-context validator audits
//@ mechanism: ghost and snapshot uses only (D-139 names the logic types as not audited).
//@ accept-means: program bodies whose `Int` arithmetic panics at run time are reported verified and the
//@ accept-means: crate exits 0.
//@ fixed-by: D-193: a call that runs an `Int` operation whose `i128` body is not the logical one (its
//@ fixed-by: arithmetic, `From<u128>`, a comparison with another type) is refused in code that runs.
//@ WHY THE CONTRACT IS FALSE: each function panics on every call ("attempt to add with overflow",
//@ WHY THE CONTRACT IS FALSE: "attempt to divide by zero", "u128 value exceeds Int host range").
//@ teeth: ACCEPTED (all three verified, exit 0) at the campaign base 4c832882 and at wp-s140 598eed1d.
//@ teeth: Natively, against the campaign's debug trust-wp-std, each function panics as named; with
//@ teeth: overflow checks off in trust-wp-std, `add_past_i128` wraps and returns `false` instead.
//@ teeth: Refused at wp-s150; logic_int_exact_operations_in_program_context_control, the exact
//@ teeth: operations in program code and the arithmetic in `ghost!`, verifies at both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result)]
pub fn add_past_i128() -> bool {
    let a = Int(i128::MAX);
    let b = a + Int(1);
    b > a
}

#[ensures(result)]
pub fn div_by_zero() -> bool {
    let _q = Int(1) / Int(0);
    true
}

#[ensures(result)]
pub fn from_u128_max() -> bool {
    let _a = Int::from(u128::MAX);
    true
}
