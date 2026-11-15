//@ expect: verify
//@ mechanism: control for closure_second_param_ensures_read_as_first_argument: a closure of two
//@ mechanism: parameters is called with (4, 3), and its `ensures` over the SECOND parameter is
//@ mechanism: granted at the call. A `Fn*` call passes the parameters as one tuple; each is that
//@ mechanism: tuple's field, the value the closure's own lane reads.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ teeth: n/a — over-refusal control.
//@ fixed-by: D-180 — the parameters are bound to the tuple's fields; before, the second was unbound
//@ fixed-by: and the call failed closed (`h` unknown).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result@ == 3)]
pub fn h() -> u32 {
    let f = #[ensures(result == b)] |_a: u32, b: u32| b;
    f(4, 3)
}
