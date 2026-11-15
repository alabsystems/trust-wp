//@ expect: reject
//@ mechanism: the callee writes through its `&mut` parameter and then hands that borrow back as the result. Under the Creusot reading `result == p` on a `&mut` is `*result == *p && ^result == ^p` with `*p` the ENTRY pointee, so `*result == 9` refutes it for every entry value but 9. Every extraction lane named the returned borrow `Var("p")` — the same carrier as the parameter — so the obligation collapsed to the syntactic identity `p == p` and the store was never consulted. This is the CALLEE side (how the contract is PROVED), not the call-site framing s48 owns.
//@ fixed-by: wp-s57 435abd9b (refuse the entry pointee for a borrow handed back after a store reaches the return)
//@ accept-means: `result == p` on a `&mut` is being read as reference identity instead of the (current, final) pair equality Creusot defines, so a callee may rewrite the pointee it promises to hand back unchanged.
//@ WHY THE PROGRAM IS WRONG: `*result` is 9 at the return; `*p` is the caller's entry value, which the contract never constrains.
//@ teeth: A/B'd both sides: ACCEPTED (`trust-wp: hand_back_write verified`,
//@ teeth: `base_exit_code=0`) on a wp-campaign ce1d56fc build of this sandbox
//@ teeth: running this same program; rejected here.
//@ verdict: failed
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == p)]
pub fn hand_back_write(p: &mut u32) -> &mut u32 {
    *p = 9;
    p
}
