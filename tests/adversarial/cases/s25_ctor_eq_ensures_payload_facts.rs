//@ expect: reject
//@ mechanism: constructor-equality payload facts asserted at encode time, reached through a user
//@ mechanism: enum postcondition `result == E::A(1)`
//@ fixed-by: cfff9b4 (s25 vacuous whole-value equality)
//@ accept-means: unguarded constructor payload premises are back on the postcondition path
//@
//@ WHY THE CONTRACT IS FALSE: the function returns E::A(2).
//@ teeth: VERIFIED — accepted (verified) on d9164f2, rejected (FAILED) with cfff9b4.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub enum E {
    A(i32),
    B,
}

#[ensures(result == E::A(1i32))]
pub fn enum_false() -> E {
    E::A(2i32)
}
