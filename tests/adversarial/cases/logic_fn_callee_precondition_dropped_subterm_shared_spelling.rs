//@ expect: reject
//@ mechanism: a call inside a subterm the type-check vehicle does not type-check, where another call of the body has the same spelling and a different definition. `f.postcondition(np(y))` is a flat `Fn` predicate with no argument before its result, which the vehicle leaves unconstrained (`spec_tc::encode`, `is_untyped_flat_fn_spec_call`), so rustc resolves no call inside it. The body's other `np`, under a block-scoped `use crate::free as np;`, denotes `free`. The walk read a parsed call as denoting whatever rustc resolved ANY call of its spelling to, so the dropped `np(y)`, which denotes `needs_pos` through the module's `use`, owed only what `free` requires: nothing. Found probing sideways from D-120.
//@ accept-means: a logic function that calls another outside its precondition, inside a subterm rustc never resolved, is credited `verified` because a same-spelled call elsewhere in the body denotes a function with no precondition.
//@ WHY IT IS FALSE: at `y == 0` the body evaluates `np(0)`, which is `needs_pos(0)`, and `needs_pos` requires `x > 0`; Creusot's `vc_caller` carries that precondition and is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0, on the rustc-resolution walk that matches a parsed call by its spelling alone: `creusot_test::caller verified ✓`. The same body with the tuple spelling `f.postcondition((), np(y))`, which the vehicle type-checks, is refuted on that build. Controls: logic_fn_callee_precondition_dropped_subterm_control.rs and logic_fn_callee_precondition_dropped_subterm_typed_control.rs.
//@ fixed-by: D-136
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[requires(x > 0)]
pub fn needs_pos(x: Int) -> Int {
    x
}

#[logic]
pub fn free(x: Int) -> Int {
    x
}

use crate::needs_pos as np;

#[logic]
#[ensures(true)]
pub fn caller<F: Fn() -> Int>(f: F, y: Int) -> bool {
    let a = {
        use crate::free as np;
        np(y)
    };
    f.postcondition((), a) == f.postcondition(np(y))
}
