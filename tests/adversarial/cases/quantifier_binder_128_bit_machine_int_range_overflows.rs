//@ expect: reject
//@ verdict: failed
//@ fn-failed: only_zero
//@ mechanism: D-203 states a machine-integer binder's range as `low <= x && x < high`, computing the
//@ mechanism: bounds in `i128` (`quantifiers::MachineInt::range_of`): `1 << bits` for an unsigned type and
//@ mechanism: `-(1 << (bits - 1))` .. `1 << (bits - 1)` for a signed one. For `u128` the shift is by 128 and
//@ mechanism: for `i128` the low bound negates `i128::MIN`: both overflow. With overflow checks (a debug
//@ mechanism: build) the contract macro panics while parsing the clause, so a crate spelling any
//@ mechanism: `u128`/`i128` binder fails to compile ("custom attribute panicked: attempt to shift left with
//@ mechanism: overflow" / "attempt to negate with overflow"). Without them (a release build) the shift
//@ mechanism: wraps: `u128` ranges over `0 <= x < 1`, so `forall<x: u128> x@ == 0` holds in the solver,
//@ mechanism: and `i128` over `-2^127 <= x < -2^127`, empty, so every `forall<x: i128>` claim holds and no
//@ mechanism: `exists` does. Each function here claims what no 128-bit value satisfies; `2^127` and `2^128`
//@ mechanism: are spelled as products the parser reads.
//@ fixed-by: D-211 — the bounds are built without an `i128` overflow (`range_of`, `power_of_two`).
//@ accept-means: a release build verifies `forall<x: u128> x@ == 0` and `forall<x: i128> false`-shaped claims.
//@ teeth: MEASURED in the debug build the corpus runs: the contract macro panics and the crate does not
//@ teeth: compile (no verdict). The release bounds were computed by the same expressions compiled without
//@ teeth: overflow checks: `u128` -> (0, 1), `i128` -> (-2^127, -2^127). With D-211: each function
//@ teeth: FAILED (postcondition).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

// WRONG: 1 is a `u128`.
#[ensures(forall<x: u128> x@ == 0)]
pub fn only_zero() {}

// WRONG: no `i128` is both 7 and not 7.
#[ensures(forall<x: i128> x@ == 7 && x@ != 7)]
pub fn contradiction() {}

// WRONG: 2^128 is no `u128`.
#[ensures(exists<x: u128> x@ == 4294967296 * 4294967296 * 4294967296 * 4294967296)]
pub fn two_pow_128() {}

// WRONG: 2^127 is no `i128`.
#[ensures(exists<x: i128> x@ == 2147483648 * 4294967296 * 4294967296 * 4294967296)]
pub fn two_pow_127() {}
