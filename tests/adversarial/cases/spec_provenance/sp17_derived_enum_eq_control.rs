//@ expect: verify
//@ xfail: the contract-free body is now a verification target and its body obligations are
//@ xfail: stated for the first time; ay does not decide them, so the item reports
//@ xfail: `unknown` and the run is no longer clean. The case's own claim is unaffected —
//@ xfail: nothing it asserts was refuted. An XPASS here means the newly-stated obligations
//@ xfail: became decidable.
//@ mechanism: control for sp17: derived PartialEq on an enum over u32/bool/char is logical equality (eq and ne)
use creusot_std::prelude::*;
#[derive(Clone, Copy, PartialEq)]
pub enum E { A(u32), B(bool, char) }
#[ensures(result)]
pub fn f(x: E) -> bool { x == x }
#[ensures(result == (a == b))]
pub fn g(a: E, b: E) -> bool { a == b }
