//@ expect: reject
//@ verdict: error
//@ refused-with: cannot dereference a ghost value in program context
//@ mechanism: the program-context validator skips a `#[check(ghost)]` body, which a program may call:
//@ mechanism: `h` dereferences its `Ghost` parameter outside `ghost!`, so `f`'s call runs
//@ mechanism: `<Ghost<i32> as Deref>::deref` and panics. Creusot's `Ghost` deref requires `false`
//@ mechanism: outside a ghost block, so `h` does not verify there.
//@ accept-means: `h` and `f` are reported verified; `f` panics on every call.
//@ fixed-by: D-139 — a `#[check(ghost)]` body's ghost reads outside `ghost!` are validated as a
//@ fixed-by: program's.
//@ teeth: ACCEPTED (`h verified`, `f verified`, exit 0) when committed; natively `f` panics.
//@ teeth: Refused at `*g` under D-139.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[check(ghost)]
#[ensures(result == *g)]
pub fn h(g: Ghost<i32>) -> i32 {
    *g
}

#[ensures(true)]
pub fn f() {
    let _ = h(ghost!(5i32));
}
