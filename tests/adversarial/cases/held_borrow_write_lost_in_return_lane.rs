//@ expect: reject
//@ mechanism: the RETURN lane's spelling of struct_held_borrow_write_lost and
//@ mechanism: tuple_held_borrow_write_lost, which are closed only in the proof_assert lane: a `&mut` held
//@ mechanism: in a struct, a tuple or an `Option`, written through by the host itself, and the borrowed
//@ mechanism: local returned. The primary walk leaves a deref write whose owner is a whole local to the
//@ mechanism: per-borrow carrier lane (`handle_projected_write`), which tracks only a borrow chain of
//@ mechanism: whole-local `&mut` locals and never one read back out of an aggregate; and the return sink's
//@ mechanism: stale-read guard (`DerefStoreStaleness`) does not union a borrow with the aggregate that
//@ mechanism: holds it. So `c` is returned at its value before the write.
//@ accept-means: a postcondition over a local is proved against its value before a write through a borrow the
//@ accept-means: host packed into a struct, a tuple or an `Option`.
//@ WHY THE CONTRACT IS FALSE: every host returns 7.
//@ fixed-by: D-127: the stale-read guard joins a borrow to the aggregate that holds it, and a store
//@ fixed-by: through the holder that the extraction lanes do not carry to `c` makes `c`'s read stale,
//@ fixed-by: which fails closed.
//@ teeth: MEASURED as ACCEPTED, exit 0, every host `verified`, with and without D-140 on a tree
//@ teeth: without D-127; every host `unknown` with D-127. Without D-127 the TRUE twins (claiming 7)
//@ teeth: were FAILED, so the lane was wrong in both directions.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct H<'a> {
    pub p: &'a mut i32,
}

#[ensures(result == 5i32)]
pub fn in_struct() -> i32 {
    let mut c = 5i32;
    let h = H { p: &mut c };
    *h.p = 7;
    c
}

#[ensures(result == 5i32)]
pub fn in_tuple() -> i32 {
    let mut c = 5i32;
    let t = (&mut c,);
    *t.0 = 7;
    c
}

#[ensures(result == 5i32)]
pub fn in_option() -> i32 {
    let mut c = 5i32;
    let o = Some(&mut c);
    if let Some(r) = o {
        *r = 7;
    }
    c
}
