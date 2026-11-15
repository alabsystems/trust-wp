//@ expect: reject
//@ mechanism: s26 addendum shape — a LOCAL contract-less fn computing `10 / y`; its division-by-zero obligation is posed NOWHERE in trust-wp, so it must never collect item-level credit, and its caller must not be handed a claim about its result
//@ accept-means: trust-wp credited a claim about the result of a contract-less callee it never read, while the `[@expl:division by zero]` / `[@expl:Div overflow]` goals Creusot poses for `10 / y` (see tests/should_succeed/bug/395.rs in the triage) went unexamined
//@ fixed-by: n/a — s80 addendum FALSE-ACCEPT gate; the goal kind belongs to s16 + the panic-site lane
//@ teeth: rejected on wp-s80 base (`requires(false)`) and after the s80 fix (route (a) leaves this non-recursive call Opaque). Prospective for any route that credits contract-less local callees before s16 lands.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// Contract-less, LOCAL. `div10(0)` panics: "attempt to divide by zero".
// `div10(i32::MIN)` with y == -1 overflows. Neither obligation is posed today.
fn div10(y: i32) -> i32 {
    10 / y
}

// WRONG: caller(5) returns 2, not 10.
#[ensures(result@ == 10i32@)]
pub fn caller(y: i32) -> i32 {
    div10(y)
}
