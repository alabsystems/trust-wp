//@ expect: reject
//@ mechanism: the return-expression (function contract) twin of s84_moved_borrow_write_lost: the primary extraction lane binds `x` to its entry value, a whole-local move of the borrow is not tracked as an alias, and the store through the moved borrow never reaches `x`, so the returned `x` is proved equal to 5.
//@ fixed-by: wp-s84 (the return-expression lane fails closed on a value read after a store through a borrow of it — the same staleness gate the call-precondition sink already had)
//@ accept-means: a function that writes a local through a moved `&mut` and returns the local is proved to return the entry value — a plain-Rust false accept in a `#[ensures]` clause.
//@ WHY THE PROGRAM IS WRONG: `*r2 = 7` sets `x` to 7 and `x` is returned; `result == 5` is false on every run.
//@ teeth: LIVE on the campaign tip 684821d0: ACCEPTED, `k verified`, base_exit_code=0
//@ teeth: measured directly on this program. PRE-EXISTING. With the
//@ teeth: return gate: unknown, exit 2.
//@ verdict: unknown
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;
#[ensures(result == 5i32)]
pub fn k() -> i32 {
    let mut x = 5i32;
    let r = &mut x;
    let r2 = r;
    *r2 = 7;
    x
}
