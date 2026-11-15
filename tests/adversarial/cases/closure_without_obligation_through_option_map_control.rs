//@ expect: verify
//@ mechanism: control for D-118: a closure with NO obligation site (no runtime check, no abort, no
//@ mechanism: precondition-bearing callee) handed to `Option::map` by a contracted host. Its
//@ mechanism: precondition is `true`, so it is not made a target and the host's credit rests on
//@ mechanism: nothing. A rule that refused every host handing a closure to a combinator fails here.
//@ accept-means: n/a (control) — this contract is TRUE and nothing here can panic.
//@ fixed-by: n/a (control)
//@ teeth: control — verifies, with no closure named in any verdict line.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@ == 1)]
pub fn pick(o: Option<u32>) -> u32 {
    let _ = o.map(|x| x == 3);
    1
}
