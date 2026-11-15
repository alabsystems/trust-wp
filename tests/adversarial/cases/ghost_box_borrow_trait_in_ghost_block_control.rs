//@ expect: verify
//@ mechanism: the TRUE twin of ghost_box_borrow_trait_in_program_context_panics: the same
//@ mechanism: `BorrowMut` call on a `Ghost<Box<i32>>`, inside `ghost!`, which is erased at run time.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `f verified`, exit 0, with the program-context refusal of the trait call in force.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
use std::borrow::BorrowMut;

#[ensures(true)]
pub fn f() {
    let mut x = ghost!(Box::new(5i32));
    ghost! {
        let r: &mut i32 = BorrowMut::<i32>::borrow_mut(&mut x);
        *r = 6;
    };
}
