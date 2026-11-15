//@ expect: reject
//@ mechanism: a `requires` clause names a PARAMETER's `precondition`, and a local closure in the
//@ mechanism: body happens to share its source name. Rewriting a precondition in PREMISE position
//@ mechanism: then replaces the parameter's uninterpreted predicate with the LOCAL closure's body
//@ mechanism: WP, so the callee assumes a fact about one closure while its callers discharge a
//@ mechanism: clause about another.
//@ accept-means: a caller's proof obligation and the callee's assumption are about different
//@ accept-means: closures, so any precondition can be laundered by shadowing a parameter's name.
//@ fixed-by: ?
//@ teeth: the contract is false by execution — the identity closure satisfies the `requires` at
//@ teeth: every argument, and `launder(|x| x, 0)` divides by zero.
//@ also-verified: needs_nonzero
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(x != 0i32)]
#[ensures(result@ == 10i32@ / x@)]
pub fn needs_nonzero(x: i32) -> i32 {
    10i32 / x
}

#[requires(g.precondition((k,)))]
#[ensures(result@ == 10i32@ / k@)]
pub fn launder<G: Fn(i32) -> i32>(g: G, k: i32) -> i32 {
    let g = |x: i32| needs_nonzero(x);
    g(k)
}
