//@ expect: verify
//@ mechanism: control for u128_literal_suffix_contract_false, which differs in one literal: a clause
//@ mechanism: holding a `u128`-suffixed literal is parsed, and its value is read. The contract
//@ mechanism: parser's suffix range for `u128` once computed `(1 << 127) - 1` in `i128`, which
//@ mechanism: overflows, so every such clause panicked the contract macro in a debug build
//@ mechanism: (`custom attribute panicked: attempt to subtract with overflow`) and the crate did
//@ mechanism: not compile (should_succeed/integer_ops.rs, category driver_panic).
//@ xfail: D-232 refuses `+` and `<<` on `u128`: the oracle's operations on it wrap at 128 bits,
//@ xfail: beyond what native replay evaluates.
//@ xfail-verdict: unknown
//@ teeth: control; before the fix both functions were compile errors, neither was examined
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ < 100)]
#[ensures(result == x + 1u128)]
pub fn inc(x: u128) -> u128 {
    x + 1
}

#[ensures(result == n << 3u128)]
pub fn shl3(n: u128) -> u128 {
    n << 3
}
