//@ expect: verify
//@ xfail: a comparison in a body whose operand is an associated constant (`x < i32::MAX`) is
//@ xfail: dropped from the body's translation: the local it assigns is left unconstrained, so
//@ xfail: the branch it decides is read as either arm and `bump` is reported FAILED on a model
//@ xfail: the program cannot reach (`x = 0` taking the `else` arm). A body that returns
//@ xfail: `i32::MAX` itself is translated; its literal twin, program_assoc_const_branch_literal_twin,
//@ xfail: verifies.
//@ mechanism: over-refusal control: the guard keeps `x + 1` below `i32::MAX`, so the addition
//@ mechanism: cannot panic and the result is positive for every `x >= 0`. The trait_project
//@ mechanism: fixture's refinement impls spell the same guard as a literal for this reason.
//@ fixed-by: n/a (control; open)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control; measured FAILED on the campaign head)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ >= 0)]
#[ensures(result@ > 0)]
pub fn bump(x: i32) -> i32 {
    if x < i32::MAX {
        x + 1
    } else {
        x
    }
}
