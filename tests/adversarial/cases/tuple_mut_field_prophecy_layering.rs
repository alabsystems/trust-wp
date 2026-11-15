//@ expect: reject
//@ mechanism: For a BY-VALUE tuple of mutable references, `^p.0` and `*p.0` are lowered onto the
//@ mechanism: same layer. The clause prints as `^__trust_wp_tuple_get_0(*p)` — a dereference of the
//@ mechanism: tuple the source never writes — and the prophecy equality `^p.0 == *p.0` is then
//@ mechanism: discharged by reflexivity, with the body's write through `p.0` invisible on that
//@ mechanism: layer. The fail-closed final-collapse guard covers a struct carrier with the same two
//@ mechanism: `&mut` fields (it refuses `^s`, naming "collapsing would assert the false equality
//@ mechanism: `^s == *s`"); the tuple lane reaches that equality without passing the guard.
//@ fixed-by: ?
//@ accept-means: the prophecy equality that GRANTS final-value facts was granted over the wrong
//@ accept-means: layer, so "this function did not change the target" is provable for a function
//@ accept-means: that changes it. Every `^`-bearing postcondition on a by-value tuple of `&mut`
//@ accept-means: parameters is then worthless, in both directions.
//@
//@ WHY THE CONTRACT IS FALSE, as a concrete execution: let mut v = 0; let mut w = 0;
//@ m((&mut v, &mut w)); afterwards v == 9 and both borrows have expired, so `^p.0` is 9 while
//@ `*p.0` — the entry value — is 0.
//@ teeth: SELF-EVIDENT, committed RED: this case is ACCEPTED today, on a fresh build of the tip
//@ teeth: and on the separately built campaign tree binary, so no knob is needed to show it bites.
//@ teeth: The obligation is genuinely examined rather than dropped: the identical function with
//@ teeth: `#[ensures(^p.0 == 8)]` is refuted with a counterexample naming p.0_final, and the TRUE
//@ teeth: claim `#[ensures(^p.0 == 9)]` on this same body is refuted too — the same mis-layering
//@ teeth: pointing the other way, which is why the control ships xfail.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^p.0 == *p.0)]
pub fn m<'a>(p: (&'a mut i32, &'a mut i32)) {
    *p.0 = 9;
}

// The refutation, in executable Rust: `v` enters at 0 and leaves at 9, so the
// final value of the first borrow is not its entry value.
pub fn caller() {
    let mut v = 0i32;
    let mut w = 0i32;
    m((&mut v, &mut w));
    assert!(v == 9);
}
