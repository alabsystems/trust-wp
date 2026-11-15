//@ expect: reject
//@ mechanism: a local's borrow held by an array (`[&mut c]`), an `Option` written through a
//@ mechanism: reference to it (`if let Some(r) = &mut o { **r = 5 }`), a tuple written through a
//@ mechanism: reference to the tuple (`let r = &mut t; *r.0 = 5`), a borrow moved out of its
//@ mechanism: holder (`let r = t.0; *r = 5`), and a borrow a CALL returned stored into a holder
//@ mechanism: (`t.0 = id(&mut c)`), each written, then read by a `proof_assert!`. D-129's first
//@ mechanism: cut counted only a store whose place did not begin with a dereference and was not
//@ mechanism: in a holder it took the lanes to follow, so an element store, a store through a
//@ mechanism: reference to the holder, and a store through a moved-out borrow were "followed"; and
//@ mechanism: a call's result was not joined to the borrow it was handed.
//@ accept-means: an assertion about a local after a write through a holder of its borrow is
//@ accept-means: credited against the local's value from before the write.
//@ WHY THE CONTRACT IS FALSE: each body writes 5 into the local the assertion says is 0.
//@ fixed-by: D-129 (the lanes follow a store only through a `&mut` parameter, a borrow of a local
//@ fixed-by: assigned once, or a field of a tuple or struct holder they bind; a call result joins the
//@ fixed-by: classes of the borrows it was handed)
//@ refused-with: proof_assert in creusot_test::arr_holder error: stale read refused
//@ also-verified: id
//@ teeth: MEASURED (debug driver, ay 57a37e51): on 2c859203 (before D-129) arr_holder's,
//@ teeth: arr_second_element's, opt_holder's and reborrowed_holder's assertions were VERIFIED and
//@ teeth: arr_holder and arr_second_element were credited; via_id and moved_out were inconclusive.
//@ teeth: D-129's first cut (salvage 643f93a7) still VERIFIED arr_holder, opt_holder and
//@ teeth: reborrowed_holder. With the fix each of the six is refused as a stale read.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub fn id<'a>(r: &'a mut i32) -> &'a mut i32 {
    r
}

pub fn arr_holder() {
    let mut c = 0i32;
    let a = [&mut c];
    *a[0] = 5i32;
    proof_assert!(c == 0i32);
}

pub fn arr_second_element() {
    let mut c = 0i32;
    let mut d = 0i32;
    let a = [&mut c, &mut d];
    *a[1] = 5i32;
    proof_assert!(d == 0i32);
}

pub fn opt_holder() {
    let mut c = 0i32;
    let mut o = Some(&mut c);
    if let Some(r) = &mut o {
        **r = 5i32;
    }
    proof_assert!(c == 0i32);
}

pub fn reborrowed_holder() {
    let mut c = 0i32;
    let mut t = (&mut c, 0i32);
    let r = &mut t;
    *r.0 = 5i32;
    proof_assert!(c == 0i32);
}

pub fn moved_out() {
    let mut c = 0i32;
    let t = (&mut c, 0i32);
    let r = t.0;
    *r = 5i32;
    proof_assert!(c == 0i32);
}

pub fn via_id() {
    let mut b = 0i32;
    let mut c = 0i32;
    let mut t = (&mut b, 0i32);
    t.0 = id(&mut c);
    *t.0 = 5i32;
    proof_assert!(c == 0i32);
}
