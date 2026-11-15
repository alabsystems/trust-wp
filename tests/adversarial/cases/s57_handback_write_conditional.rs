//@ expect: reject
//@ mechanism: same defect with the store on ONE branch only. `result == p` is false exactly on the `b == true` path, so a lane that consults the store must refuse the whole contract, not just the written path.
//@ fixed-by: wp-s57 435abd9b
//@ accept-means: the store analysis is being read path-insensitively in the permissive direction — a store that reaches the return on SOME path is not enough to withdraw the entry-pointee binding.
//@ WHY THE PROGRAM IS WRONG: with `b == true`, `*result` is 9 while `*p` is the entry value.
//@ teeth: A/B'd against wp-campaign ce1d56fc: NOT accepted there either —
//@ teeth: it errored out (`0 verified, 0 failed, 1 errors`, `base_exit_code=2`,
//@ teeth: on the conditional-store probe v4_cond). This case has no teeth against ce1d56fc; it is
//@ teeth: kept as the path-sensitivity pin for the new refusal, which turns it into a
//@ teeth: proper counterexample rejection (`base_exit_code=1`).
//@ verdict: failed
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == p)]
pub fn hb_cond(p: &mut u32, b: bool) -> &mut u32 {
    if b {
        *p = 9;
    }
    p
}
