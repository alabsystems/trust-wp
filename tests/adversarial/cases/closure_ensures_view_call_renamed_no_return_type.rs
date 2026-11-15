//@ expect: reject
//@ verdict: error
//@ refused-with: in a specification with no type-check closure, which the contract parser reads as the `view` builtin
//@ mechanism: the closure door of program_ensures_view_call_renamed_impl_trait_return.rs: `use crate::seven as view;` then `view(result)` in the `ensures` of a closure written without `-> T`. The vehicle writes a closure's clause check beside the closure only when it can re-declare every parameter and, for an `ensures` that names `result`, the result type (`spec_tc::closure_clause_statement`), so this clause has no type-check closure and rustc's resolution of `view` is never read. The parser reads the bare `view(result)` as the view builtin, and the closure is credited on `result@ == 5`. Closures are commonly written without a return type. Found probing sideways from D-136.
//@ fixed-by: D-240: the crate is refused before any clause is read (`call_resolution::misread_specification_names`).
//@ accept-means: a closure is credited on a postcondition that holds only when a call renamed onto `view` is read as the view builtin, and the crate exits 0.
//@ WHY IT IS FALSE: the closure returns `x`, and `view(result)` is `seven(result)`, which is `7`, never `5`.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open and with D-136: `trust-wp: prog::{closure#0} verified ✓`. The control is closure_ensures_view_call_renamed_no_return_type_control.rs, which differs in the renaming `use` alone and verifies.
//@ also-verified: prog
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

pub fn prog() -> u32 {
    let c = #[requires(x@ == 5)]
    #[ensures(view(result) == 5)]
    |x: u32| x;
    c(5)
}
