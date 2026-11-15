//@ expect: verify
//@ xfail: the nested block's `k` and `host`'s `k` print one path, `host::k`, and the identity tables
//@ xfail: cannot tell them apart, so the call is refused. The isolating twin of
//@ xfail: block_shadowed_same_path_logic_fn_granted.rs (one literal differs).
//@ mechanism: control: `inner` returns 0, which is the nested block's `k()`, the function its contract
//@ mechanism: names.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn host() -> u32 {
    #[logic(open)]
    fn k() -> Int {
        pearlite! { 10 }
    }
    {
        #[logic(open)]
        fn k() -> Int {
            pearlite! { 0 }
        }
        #[ensures(result@ == k())]
        fn inner() -> u32 {
            0
        }
        inner()
    }
}
