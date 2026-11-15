//@ expect: reject
//@ verdict: unknown
//@ refused-with: `__lfidU__ambiguous__constant__K` was not resolved to one definition by the driver
//@ also-verified: b::g
//@ mechanism: two callees spell `K` in their own modules, where it names different constants:
//@ mechanism: `a::f` promises `result == a::K` (0), `b::g` requires `x == b::K` (10). Both read the
//@ mechanism: one value the short-name table held (10), so `h` discharged `g`'s precondition from
//@ mechanism: `f`'s postcondition and was credited, while `a::f`, which is correct, FAILED.
//@ accept-means: `h` passes 0 to `b::g`, whose precondition requires 10.
//@ fixed-by: D-111 (a bare constant name the crate gives more than one meaning is refused wherever the table substitutes it)
//@ teeth: MEASURED before D-111: rejected only because `a::f FAILED ✗` on a true contract; `b::g verified ✓` and `h verified ✓` beside it. At the fix every clause spelling the name is refused and no function in the crate is credited on it; const_short_name_unique_control.rs, one constant spelled everywhere, verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod a {
    use creusot_std::prelude::*;
    pub const K: u32 = 0;
    #[ensures(result == K)]
    pub fn f() -> u32 {
        0
    }
}

pub mod b {
    use creusot_std::prelude::*;
    pub const K: u32 = 10;
    #[requires(x == K)]
    pub fn g(x: u32) {}
}

#[ensures(true)]
pub fn h() {
    let y = a::f();
    b::g(y);
}
