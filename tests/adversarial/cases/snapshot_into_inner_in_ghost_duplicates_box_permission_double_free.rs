//@ expect: reject
//@ mechanism: a snapshot is `Copy` whatever it holds, and ghost code may take its value out: trust-wp
//@ mechanism: allows `Snapshot::into_inner` (and `inner`, and a deref) inside `ghost!`, where Creusot's
//@ mechanism: are logic functions ghost code cannot call and only `into_ghost`, for a `Plain` type, is
//@ mechanism: open. So `snapshot!(*own)` then `ghost!(s.into_inner())` is a second
//@ mechanism: `Ghost<Box<Perm<_>>>` equal to the first, and each discharges `to_box`'s
//@ mechanism: `ptr == *own.ward()` for the one pointer: two boxes own one allocation.
//@ accept-means: a body that boxes one allocation back twice, through a permission a snapshot duplicated
//@ accept-means: in ghost code, is reported verified and exits 0.
//@ fixed-by: OPEN — a guard, not a demonstrated false accept: rejected today only because ay returns
//@ fixed-by: `unknown (incomplete)` on the second ward identity. It succeeds
//@ fixed-by: snapshot_into_ghost_duplicates_box_permission_double_free, which D-193's `T: Plain` on
//@ fixed-by: `into_ghost` stopped compiling. Closing the shape means ghost code takes a value out of a
//@ fixed-by: snapshot only where its type is `Plain`.
//@ WHY THE CONTRACT IS FALSE: `f` frees one allocation twice and aborts on every call.
//@ teeth: UNVERIFIED as a false accept: `unknown (incomplete)` at the campaign base 6e6bf5f3 and at
//@ teeth: wp-s150. Natively, built against trust-wp-std, `f` aborts on the double free.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{ghost::perm::Perm, prelude::*};

#[ensures(true)]
pub fn f() {
    let (p, own) = Perm::new(5i32);
    let s = snapshot!(*own);
    let own2: Ghost<Box<Perm<*const i32>>> = ghost!(s.into_inner());
    let b1 = unsafe { Perm::to_box(p, own) };
    let b2 = unsafe { Perm::to_box(p, own2) };
    drop(b1);
    drop(b2);
}
