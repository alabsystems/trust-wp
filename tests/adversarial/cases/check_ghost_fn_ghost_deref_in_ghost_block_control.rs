//@ expect: verify
//@ mechanism: the TRUE twin of check_ghost_fn_ghost_deref_called_from_program_panics: `h` reads its
//@ mechanism: ghost inside `ghost!`, which is erased at run time, so `f`'s call does not panic.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `h verified`, `f verified`, exit 0, when committed.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[check(ghost)]
#[ensures(*result == *g)]
pub fn h(g: Ghost<i32>) -> Ghost<i32> {
    ghost!(*g)
}

#[ensures(true)]
pub fn f() {
    let _ = h(ghost!(5i32));
}
