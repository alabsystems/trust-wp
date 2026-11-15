//@ expect: reject
//@ also-verified: h::{closure#1}
//@ mechanism: a closure of two parameters is called with (4, 3). A `Fn*` call passes them as ONE
//@ mechanism: tuple after the receiver; the closure's clauses name each parameter. A call that binds
//@ mechanism: its parameters to anything but the tuple's fields in order grants `result == b` about
//@ mechanism: the wrong value.
//@ accept-means: the closure's postcondition over its second parameter was granted about the first
//@ accept-means: argument.
//@ WHY THE CONTRACT IS FALSE: `h()` returns `f(4, 3)`, which is 3, not 4. The closure's own
//@ WHY THE CONTRACT IS FALSE: contract is true and is credited on purpose.
//@ teeth: ACCEPTED (exit 0, `h verified`) on a build of D-180 that binds the tuple's fields in reverse
//@ teeth: order. Rejected at the head before D-180 (the second parameter unbound, the call failing
//@ teeth: closed) and with D-180 (`h` FAILED on the postcondition).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result@ == 4)]
pub fn h() -> u32 {
    let f = #[ensures(result == b)] |_a: u32, b: u32| b;
    f(4, 3)
}
