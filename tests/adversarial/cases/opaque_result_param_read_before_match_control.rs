//@ expect: verify
//@ xfail: a wrong reject, `p unknown (sort-coercion bridge in negated goal)`. `r.is_ok()` reads `r` at the
//@ xfail: opaque `Result` sort, and the match upgrades it to `ResultIntInt` through a structural bridge
//@ xfail: that carries the variant tag but not `is_ok`, so the precondition does not reach the arms; the
//@ xfail: bridge's own demotion withholds the model. Not a fresh-symbol split: D-218 does not act here.
//@ xfail-verdict: unknown
//@ mechanism: The `Result` spelling of opaque_option_param_read_before_match_control.rs.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: OPEN
//@ teeth: control — `unknown` over the bridge before D-218 and with it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(r.is_ok())]
#[ensures(match r { Ok(_) => true, Err(_) => false })]
pub fn p(r: Result<u32, u32>) {}
