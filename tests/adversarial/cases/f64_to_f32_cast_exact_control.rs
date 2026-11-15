//@ expect: verify
//@ xfail: the solver reaches UNSAT on the floating-point query, and strict certification withholds it
//@ xfail: (`proof-trusted`): ay's proof checker has no rule for a floating-point theory lemma. D-215
//@ xfail: names this price. The reals proved it before D-215, reading the cast as the identity.
//@ xfail-verdict: unknown
//@ mechanism: twin of f64_to_f32_cast_read_as_identity.rs at a value `f32` represents exactly:
//@ mechanism: `0.5f64 as f32 as f64` is `0.5`, so the contract is true.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x == 0.5)]
#[ensures(result)]
pub fn roundtrip(x: f64) -> bool {
    (x as f32) as f64 == x
}
