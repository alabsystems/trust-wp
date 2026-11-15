//@ expect: reject
//@ verdict: error
//@ refused-with: in a specification with no type-check closure, which the contract parser reads as the `view` builtin
//@ mechanism: the precondition spelling of closure_ensures_view_call_renamed_no_return_type.rs: `use crate::seven as view;` then `view(x)` in the `requires` of a closure whose parameter has no type annotation. The vehicle cannot re-declare an unannotated parameter (`spec_tc::closure_clause_statement`), so the clause has no type-check closure and rustc's resolution of `view` is never read; the same closure with `|x: u32|` is refused by D-136's specification check. The parser reads the bare `view(x)` as the view builtin, so the precondition `prog` owes at `c(5u32)` is `5 == 5`. Found probing sideways from D-136.
//@ fixed-by: D-240: the crate is refused before any clause is read (`call_resolution::misread_specification_names`).
//@ accept-means: a function is credited although it calls a closure outside its precondition, read through a call renamed onto `view`, and the crate exits 0.
//@ WHY IT IS FALSE: the closure's precondition is `seven(x) == 5`, that is `7 == 5`, which no call satisfies; `prog` calls it.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open and with D-136: `trust-wp: prog verified ✓`. The control is closure_requires_view_call_renamed_unannotated_param_control.rs, which differs in the renaming `use` alone and verifies.
//@ also-verified: prog::{closure#1}
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

#[ensures(true)]
pub fn prog() -> u32 {
    let c = #[requires(view(x) == 5)]
    |x| x;
    c(5u32)
}
