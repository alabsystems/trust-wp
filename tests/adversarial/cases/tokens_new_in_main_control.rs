//@ expect: verify
//@ mechanism: `Tokens::new()` is the one ghost constructor Creusot calls from program code, once, in
//@ mechanism: `main`, and the validator allows it there. trust-wp-std's body panicked at run time
//@ mechanism: ("ghost code only") while nothing owed that panic, so this contract was FALSE while it
//@ mechanism: verified; the body is now the zero-sized ghost handle, Creusot's `Ghost::conjure()`,
//@ mechanism: and it is TRUE.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: D-139 — `Tokens::new()` is the zero-sized handle at run time.
//@ teeth: ACCEPTED as a reject case when committed (`main verified`, exit 0; natively the call
//@ teeth: panicked); verified under D-139, where natively it returns.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{ghost::invariant::Tokens, prelude::*};

#[ensures(result == 1)]
pub fn main() -> i32 {
    let _t = Tokens::new();
    1
}
