//@ expect: verify
//@ mechanism: control for sp14/sp15/sp20: std u32 Ord::max and comparisons keep std's contracts
use creusot_std::prelude::*;
#[ensures(result@ == 2)]
pub fn f() -> u32 { 1u32.max(2u32) }
#[ensures(result)]
pub fn g(a: u32, b: u32) -> bool { a.max(b) >= a }
#[ensures(result == (a < b))]
pub fn h(a: u32, b: u32) -> bool { a < b }
