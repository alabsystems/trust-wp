//@ expect: reject
//@ mechanism: a parameter pattern's binding is read as the parameter's positional projection: `a` in
//@ mechanism: `(a, _b): (u32, u32)` is `arg0.0`, over the name `name_unnamed_params` gives the
//@ mechanism: parameter (D-177 writes it into the clause text as `(arg0.0)`). That name is not a Rust
//@ mechanism: name, so a module item may take it, and a module `const` of that spelling is what the
//@ mechanism: clause's `arg0` is read as: `result == a` is owed as `result == 5`.
//@ accept-means: a pattern binding's projection was read as a module constant spelled like the
//@ accept-means: parameter's positional name.
//@ WHY THE CONTRACT IS FALSE: `g((7, 0))` returns 5, not 7.
//@ fixed-by: D-179 — the positional name is `__twp_arg0`, in a namespace no source identifier may
//@ fixed-by: use, so the projection is `(__twp_arg0.0)` and no constant is substituted into it.
//@ teeth: ACCEPTED (exit 0, `g verified`) at the reviewed head, and with every crate checked out at
//@ teeth: the campaign base in place, where the MIR destructuring substitution read `a` as the same
//@ teeth: `arg0.0`. The twin that names the const `k0` and is otherwise identical is FAILED on both,
//@ teeth: so the projection IS read as the const.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[allow(non_upper_case_globals)]
pub const arg0: (u32, u32) = (5, 5);

#[ensures(result == a)]
pub fn g((a, _b): (u32, u32)) -> u32 {
    5u32
}
