//@ expect: reject
//@ mechanism: a caller does not see what a spec-bearing `FnMut` closure writes to a variable it
//@ mechanism: captures. `x` is captured by unique borrow; the closure's body sets it to 50; after
//@ mechanism: `c()` the caller still reads `x` at its entry value 0. The closure's contract
//@ mechanism: (`ensures(true)`) says nothing about the capture's final value, so the only sound
//@ mechanism: reading is that `x` is unknown after the call; the call lane leaves it bound to the
//@ mechanism: value it had before the borrow instead. The spellings through a struct field, a tuple
//@ mechanism: field, a reborrow inside the body, a whole-value assignment, a `move` closure over a
//@ mechanism: `&mut`, and a spec-bearing helper that performs the write were all measured
//@ mechanism: ACCEPTED the same way; the contract-free closure spellings measured were not.
//@ accept-means: any claim about a captured variable's value before a spec-bearing `FnMut` call
//@ accept-means: survives the call whatever the closure wrote.
//@ fixed-by: OPEN — committed RED rather than hidden. It predates D-104 and is outside it: the only
//@ fixed-by: lane D-104 edits is the clause-free panic account, and `f` here carries a clause.
//@ WHY THE CONTRACT IS FALSE: the closure sets `x` to 50 and `f` returns `x`, so `result@ == 50`,
//@ WHY THE CONTRACT IS FALSE: not 0. The closure's own `ensures(true)` is TRUE, declared below.
//@ teeth: MEASURED as ACCEPTED, exit 0, `f verified ✓`, `f::{closure#2} verified ✓`.
//@ also-verified: f::{closure#2}
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == 0)]
pub fn f() -> u8 {
    let mut x = 0u8;
    let mut c = #[ensures(true)]
    || {
        x = 50;
    };
    c();
    x
}
