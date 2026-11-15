//@ expect: reject
//@ verdict: unknown
//@ refused-with: p unknown (refutation withheld: a phantom sort upgrade split `x`
//@ mechanism: The twin of opaque_option_param_read_before_match_control.rs whose clause claims the arm the
//@ mechanism: precondition excludes. The split leaves the precondition unread by the arms, so the refutation
//@ mechanism: is withheld (D-218) as the control's is; the fail-safe withholds, it never proves.
//@ accept-means: a precondition read before a match proves the arm it excludes.
//@ fixed-by: n/a — rejected before D-218 and with it.
//@ teeth: `p FAILED` before D-218; `p unknown (refutation withheld)` with it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x.is_some())]
#[ensures(match x { Some(_) => false, None => true })]
pub fn p(x: Option<u32>) {}
