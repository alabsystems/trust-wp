//@ expect: reject
//@ verdict: unknown
//@ refused-with: `__lfidU__ambiguous__constant__K` was not resolved to one definition by the driver
//@ mechanism: a bare constant name that module `a` imports from another crate under an alias
//@ mechanism: (`use core::u8::MAX as K`, 255) was given the value of an unrelated local constant of the
//@ mechanism: same short name (`b::K`, 10): the substitution table sees only local constant items and
//@ mechanism: looks names up without their scope.
//@ accept-means: `a::f` claims `result == u8::MAX` and returns 10.
//@ fixed-by: D-111 (a bare constant name the crate gives more than one meaning is refused wherever the table substitutes it)
//@ teeth: MEASURED before D-111: ACCEPTED, exit 0, `a::f verified ✓`. At the fix every clause spelling the name is refused and no function in the crate is credited on it; const_short_name_unique_control.rs, one constant spelled everywhere, verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod a {
    use creusot_std::prelude::*;
    #[allow(deprecated)]
    use core::u8::MAX as K;
    #[ensures(result == K)]
    pub fn f() -> u8 {
        10
    }
}

pub mod b {
    pub const K: u8 = 10;
}
