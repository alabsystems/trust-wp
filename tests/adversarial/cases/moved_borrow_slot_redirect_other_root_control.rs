//@ expect: verify
//@ mechanism: The isolating twin of moved_borrow_slot_redirect_other_root_write_lost: the same
//@ mechanism: moved borrow, the same slot pointer and the same write through it, with the
//@ mechanism: redirect `*s = b` deleted. `b`'s borrow never enters the slot, so the write
//@ mechanism: through `**s` cannot reach its referent and `^b == *b` is TRUE. The two programs
//@ mechanism: differ in whether the fact is true and in nothing else, so this case is what says
//@ mechanism: D-79 refuses the escape rather than every parameter of a function holding a slot
//@ mechanism: pointer.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(^b == *b)]
pub fn f(a: &mut i32, b: &mut i32) {
    let mut p = a;
    let s = &mut p;
    **s = 9;
}
