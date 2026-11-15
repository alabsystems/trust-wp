//@ expect: verify
//@ mechanism: control for D-118's store-only constructors: a generic callable moved into a `Box` and
//@ mechanism: the box handed to a verified hop that charges its precondition (the shape of Creusot's
//@ mechanism: closures/13_ref_box `test2`). `Box::new` stores its argument and never calls it, so it
//@ mechanism: is no hand-off; reading it as one refused the host for a type parameter handed to code
//@ mechanism: trust-wp does not verify.
//@ accept-means: n/a (control) — the host's `requires` is the hop's.
//@ fixed-by: n/a (control)
//@ teeth: control — `boxed_generic verified` on the binary before D-118 and after it; withdrawn on the
//@ teeth: one that read every std callee as running its callable argument.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(f.precondition((x,)))]
#[ensures(f.postcondition((x,), result))]
fn call_fn<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
    f(x)
}

#[requires(f.precondition((x,)))]
#[ensures(f.postcondition((x,), result))]
pub fn boxed_generic<F: Fn(i32) -> i32>(f: F, x: i32) -> i32 {
    call_fn(Box::new(f), x)
}
