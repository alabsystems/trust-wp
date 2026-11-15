//@ expect: verify
//@ xfail: a wrong reject, `p unknown (refutation withheld)`: the split of
//@ xfail: opaque_option_param_read_before_match_control.rs on `x_current`, withheld by D-218.
//@ xfail-verdict: unknown
//@ mechanism: opaque_option_param_read_before_match_control.rs through `&mut`: `(*x).is_some()` and
//@ mechanism: `match *x` both read `x_current`, which the match upgrades under a fresh symbol.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: OPEN, with opaque_option_param_read_before_match_control.rs.
//@ teeth: control — `p FAILED` before D-218, withheld with it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires((*x).is_some())]
#[ensures(match *x { Some(_) => true, None => false })]
pub fn p(x: &mut Option<u32>) {}
