//@ expect: reject
//@ mechanism: the path-call spelling of logic_fn_std_program_method_precondition: `Option::unwrap(o)`. The walk matches a path call against the crate's own program functions (`ProgramFnsWithRequires`), which a standard function is not, and the encoder reads it as the `Some` payload selector. Found probing sideways from D-120.
//@ accept-means: a logic function that calls `Option::unwrap` on a possibly-`None` option, spelled as a path call, is credited `verified` and the crate exits 0.
//@ WHY IT IS FALSE: at `o == None` the body evaluates `Option::unwrap(None)`, and `Option::unwrap` requires `self != None`; Creusot admits no program function in a logic body at all.
//@ teeth: MEASURED ACCEPTED, exit 0, with D-120 open: `creusot_test::caller verified ✓`.
//@ fixed-by: D-136
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[ensures(true)]
pub fn caller(o: Option<Int>) -> Int {
    Option::unwrap(o)
}
