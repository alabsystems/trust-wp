//@ expect: reject
//@ mechanism: a logic function with no `ensures` is credited on its body goals alone; the standard-library precondition of `unwrap_logic` is one of them (`std_logic_precondition`), so a proved assertion beside it earns nothing.
//@ accept-means: a requires-only logic function that unwraps a possibly-`None` option is credited `verified` on a true assertion.
//@ WHY IT IS FALSE: at `o == None` the body evaluates `None.unwrap_logic()`.
//@ teeth: MEASURED on the commit before D-119: nothing examined (`proved, not credited`, exit 2). With the lane crediting a function with no `ensures` but no standard-library preconditions owed, `caller verified ✓`.
//@ fixed-by: D-119
//@ verdict: unknown
//@ refused-with: caller unknown (logic callee precondition not proved)
//@ note: not refuted: the encoder models `Option<Int>` over `Int` with uninterpreted testers, and no
//@ note: validated model of `o == None` comes back; the goal is examined and not proved.
//@ also-verified-assertion: creusot_test::caller
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(true)]
pub fn caller(o: Option<Int>) -> Int {
    proof_assert!(true);
    o.unwrap_logic()
}
