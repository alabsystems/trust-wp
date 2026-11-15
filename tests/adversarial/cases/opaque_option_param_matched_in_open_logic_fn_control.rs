//@ expect: verify
//@ xfail: a wrong reject, `p unknown (refutation withheld)`. The match is in the body of the open logic
//@ xfail: function: its parameter `o` is met at the opaque `Option` sort and upgraded to `OptionInt` under
//@ xfail: a fresh symbol where the body matches it, so the precondition on `x` does not reach the arms.
//@ xfail: D-218 withholds the model of the split.
//@ xfail-verdict: unknown
//@ mechanism: The logic-function spelling of opaque_option_param_read_before_match_control.rs.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: OPEN
//@ teeth: control — `p FAILED` before D-218, withheld with it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn is_s(o: Option<u32>) -> bool {
    match o {
        Some(_) => true,
        None => false,
    }
}

#[requires(x.is_some())]
#[ensures(is_s(x))]
pub fn p(x: Option<u32>) {}
