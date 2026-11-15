//@ expect: reject
//@ mechanism: an assertion inside a closure is a goal of the closure, which is its own function with its own verdict; folding it into the enclosing function's verdict would withhold a credit the parent earned on its own contract
//@ accept-means: the closure's assertion, false for every argument but 7, is discharged.
//@ WHY THE ASSERTION IS FALSE: the closure admits any argument below 100 and is called with 3; nothing says its argument is 7.
//@ fn-failed: parent::{closure#2}
//@ also-verified: parent
//@ teeth: MEASURED on the parent commit: `parent::{closure#2} verified ✓` beside its own FAILED assertion, the closure spelling of the defect. With the credit held, the closure is FAILED and `parent` keeps the credit its contract earned; a fold keyed on the enclosing item instead of the function whose MIR holds the assertion would drop `parent`'s credit and break the declaration.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ < 100)]
#[ensures(result@ == x@ + 1)]
pub fn parent(x: u32) -> u32 {
    let c = #[requires(y@ < 100)]
    #[ensures(result@ == y@)]
    |y: u32| {
        proof_assert!(y@ == 7);
        y
    };
    let _ = c(3);
    x + 1
}
