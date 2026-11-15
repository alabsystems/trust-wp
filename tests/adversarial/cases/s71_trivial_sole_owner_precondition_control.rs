//@ expect: verify
//@ mechanism: over-refusal control for the wp-s71 v2 trivial-precondition identity rule: c2 has
//@ mechanism: no `#[requires]` and is the sole closure of arity 0 in the body, so the
//@ mechanism: `__trust_wp_tuple0().precondition(..)` obligation of `call_plain(&mut c2, 0)` is
//@ mechanism: c2's and is `true` (Creusot's precondition of a closure without requires); c1's
//@ mechanism: `requires(x > 0)` at `call_plain(&mut c1, 1)` holds and stays an obligation.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control) — this contract is TRUE and must keep verifying.
//@ teeth: n/a — over-refusal control; verifies on wp-s71 v2.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires((*f).precondition((arg,)))]
#[ensures(exists<st> (*f).postcondition_mut((arg,), st, result))]
pub fn call_plain<F: FnMut(i32) -> i32>(f: &mut F, arg: i32) -> i32 {
    f(arg)
}

#[ensures(true)]
pub fn driver_fn(y: i32) -> i32 {
    let mut c1 = {
        #[requires(x > 0)]
        #[ensures(result == x)]
        move |x: i32| -> i32 {
            if x > 0 {
                x
            } else {
                y
            }
        }
    };
    let mut c2 = |_x: i32| -> i32 { 2 };
    let _ = call_plain(&mut c2, 0);
    call_plain(&mut c1, 1)
}

pub fn main() {
    let _ = driver_fn(3);
}
