//@ expect: reject
//@ verdict: error
//@ refused-with: in a specification with no type-check closure, which the contract parser reads as the `view` builtin
//@ mechanism: program_ensures_view_call_renamed.rs on a function returning `impl Sized`: `use crate::seven as view;` then `view(x)` in the `ensures`. D-136's specification refusal (`call_resolution::misread_specification_calls`) reads only the calls of the type-check closures `trust-wp-macros` writes for clauses, and the vehicle writes none for an `ensures` whose `result` type it cannot write as a closure parameter (`spec_tc::result_type` is `None` for `impl Trait`), so rustc's resolution of `view` is never read. The contract parser reads a bare one-argument `view(e)` as the view builtin whatever the name resolves to, so the clause is `x@ == 5`, which the `requires` gives. The other doors to a clause with no type-check closure are program_ensures_view_call_renamed_chained_comparison.rs and the closure spellings closure_ensures_view_call_renamed_no_return_type.rs and closure_requires_view_call_renamed_unannotated_param.rs. A logic body with no type-checked form is refused when the crate binds the builtin's name elsewhere (`call_resolution::untyped_misread`); a clause with none is not. Found probing sideways from D-136.
//@ fixed-by: D-240: the crate is refused before any clause is read (`call_resolution::misread_specification_names`).
//@ accept-means: a program function is credited on a postcondition that holds only when a call renamed onto `view` is read as the view builtin, and the crate exits 0.
//@ WHY IT IS FALSE: `view(x)` is `seven(x)`, which is `7` for every `x`, never `5`; `prog(5)` returns with the postcondition false.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open and with D-136: `trust-wp: prog verified ✓`. The control is program_ensures_view_call_renamed_impl_trait_return_control.rs, which differs in the renaming `use` alone and verifies.
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
#[ensures(view(x) == 5)]
pub fn prog(x: u32) -> impl Sized {
    x
}
