//@ expect: verify
//@ mechanism: control for sp19: Option<u32> == Option<u32> runs core's structural eq over a library type; std PARTIAL_EQ admitted
use creusot_std::prelude::*;
#[ensures(result)]
pub fn f(a: Option<u32>) -> bool { a == a }
