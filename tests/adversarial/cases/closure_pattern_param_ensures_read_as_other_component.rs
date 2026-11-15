//@ expect: reject
//@ also-verified: h::{closure#1}
//@ mechanism: a closure of two tuple-pattern parameters, `|(_c, _d), (_a, b)| b`, called with
//@ mechanism: ((0, 0), (0, 3)). The binding `b` is the projection `.1` of the closure's second
//@ mechanism: parameter (D-177), and that parameter is the second field of the tuple the `Fn*` call
//@ mechanism: passes; read at another component or at the first parameter, the closure's
//@ mechanism: postcondition says `result` is 0.
//@ accept-means: the pattern binding of a closure parameter was read at the call as a value other than
//@ accept-means: the component it binds.
//@ WHY THE CONTRACT IS FALSE: `h()` returns `f((0, 0), (0, 3))`, which is 3, not 0. The closure's
//@ WHY THE CONTRACT IS FALSE: own contract is true and is credited on purpose.
//@ teeth: ACCEPTED (exit 0, `h verified`) on a build of D-180 that binds the tuple's fields in reverse
//@ teeth: order. Rejected at the head before D-180 (the parameter `b` is projected from unbound, the
//@ teeth: call failing closed) and with D-180 (`h` FAILED on the postcondition).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result@ == 0)]
pub fn h() -> u32 {
    let f = #[ensures(result == b)] |(_c, _d): (u32, u32), (_a, b): (u32, u32)| b;
    f((0, 0), (0, 3))
}
