//@ expect: verify
//@ xfail: a wrong reject, `p unknown (refutation withheld)`. The `Option<bool>` scrutinee is declared at
//@ xfail: `OptionInt`, whose payload is an integer, and the body's `Some(v) => v` is read through a
//@ xfail: `Bool`-ranged projection the datatype's selector does not define, so the body's value and the
//@ xfail: clause's `v` are unrelated (`p FAILED` with `x = Some(0)` and `result = true` before D-218).
//@ xfail: `x.is_some()` reads `x` before the match splits it, so D-218 withholds that model; the projection
//@ xfail: gap is open with or without the split.
//@ xfail-verdict: unknown
//@ mechanism: An `Option` whose payload is not an integer.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: OPEN
//@ teeth: control — `p FAILED` before D-218, withheld with it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x.is_some())]
#[ensures(match x { Some(v) => result == v, None => false })]
pub fn p(x: Option<bool>) -> bool {
    match x {
        Some(v) => v,
        None => false,
    }
}
