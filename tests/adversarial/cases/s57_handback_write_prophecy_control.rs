//@ expect: verify
//@ mechanism: control: `^result == ^p` is TRUE for a written handback — the returned borrow is reborrowed for the remainder of `p`'s lifetime, so the two prophecies resolve together. The s57 refusal drops the CURRENT-value binding only and must keep this premise, otherwise it costs a true claim.
//@ fixed-by: n/a — over-refusal guard for the s57_handback_write_* cases.
//@ teeth: control - must keep verifying. Verified on a wp-campaign ce1d56fc build of this
//@ teeth: branch too, on the same final-value-only handback spelling, so a later refusal here is a
//@ teeth: real over-tightening.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^result == ^p)]
pub fn hand_back_write_final(p: &mut u32) -> &mut u32 {
    *p = 9;
    p
}
