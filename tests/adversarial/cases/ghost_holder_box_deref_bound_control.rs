//@ expect: verify
//@ mechanism: the TRUE twin of ghost_holder_deref_bound_in_program_context_panics: `Option::as_deref`
//@ mechanism: asks `Deref` of a `Box` holding the ghost, not of the ghost, and `Box`'s deref returns
//@ mechanism: `&Ghost<i32>` without running the ghost's own. Only a `Deref` or `Borrow` asked of a
//@ mechanism: `Ghost` or `Snapshot` itself runs the panicking body.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — natively `f` returns `true`; verified before and after the holder check asks `Deref`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result)]
pub fn f() -> bool {
    let g: Ghost<i32> = ghost!(5i32);
    let o = Some(Box::new(g));
    o.as_deref().is_some()
}
