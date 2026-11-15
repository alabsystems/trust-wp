//@ expect: reject
//@ verdict: error
//@ refused-with: in a specification with no type-check closure, which the contract parser reads as the `view` builtin
//@ mechanism: the unwritable-clause door of program_ensures_view_call_renamed_impl_trait_return.rs: `0 <= view(x) < 6` is a chained comparison, which the contract parser reads as `0 <= view(x) && view(x) < 6` and which Rust does not parse, so the type-check vehicle writes no closure for it and rustc's resolution of `view` (`use crate::seven as view;`) is never read. The parser reads the bare `view(x)` as the view builtin, and the `requires` gives `x@ == 5`. Found probing sideways from D-136.
//@ fixed-by: D-240: the crate is refused before any clause is read (`call_resolution::misread_specification_names`).
//@ accept-means: a program function is credited on a postcondition that holds only when a call renamed onto `view` is read as the view builtin, and the crate exits 0.
//@ WHY IT IS FALSE: `view(x)` is `seven(x)`, which is `7`, and `7 < 6` is false; `prog(5)` returns with the postcondition false.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open and with D-136: `trust-wp: prog verified ✓`. The control is program_ensures_view_call_renamed_chained_comparison_control.rs, which differs in the renaming `use` alone and verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic(open)]
pub fn seven(x: u32) -> Int {
    7
}

use crate::seven as view;

#[requires(x@ == 5)]
#[ensures(0 <= view(x) < 6)]
pub fn prog(x: u32) -> u32 {
    x
}
