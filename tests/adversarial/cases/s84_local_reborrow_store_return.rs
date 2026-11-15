//@ expect: reject
//@ mechanism: the primary extraction lane records a store through a local `&mut` borrow (`let r = &mut x; *r = 7;`) as a fact about `*r` but never rebinds the borrowed local `x`, so the returned `x` is still its entry value. The proof_assert lane handles this exact shape (the substitution lane's borrow chain rebinds `x`); the return-expression lane does not, and the staleness gate that fails call PRECONDITIONS closed on such a read (`h_stale_deref_store_borrowed_local`) does not cover a read into the return value.
//@ fixed-by: wp-s84 (the return-expression lane fails closed on a value read after a store through a borrow of it — the same staleness gate the call-precondition sink already had)
//@ accept-means: a function that writes a local through a borrow and returns the local is proved to return the entry value — a plain-Rust false accept in a `#[ensures]` clause, no move and no ghost code involved.
//@ WHY THE PROGRAM IS WRONG: `*r = 7` sets `x` to 7 and `x` is returned; `result == 5` is false on every run.
//@ teeth: LIVE on the campaign tip 684821d0: ACCEPTED, `k verified`, base_exit_code=0
//@ teeth: (z_reborrow_local_ens_false.out). The true twin
//@ teeth: `result == 7` is REFUTED on the same binary, so the lane positively believes x == 5. PRE-EXISTING.
//@ teeth: With the return gate: unknown, exit 2 (same probe).
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
    *r = 7;
    x
}
