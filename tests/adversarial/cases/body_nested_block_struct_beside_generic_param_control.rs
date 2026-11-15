//@ expect: verify
//@ xfail: D-198's price: a struct `W` in a nested block of the body may or may not enclose the
//@ xfail: clause (a macro that wraps the body moves the clause into that block), so `W` is refused,
//@ xfail: not read as the parameter. It verified before D-198, on the parameter.
//@ mechanism: control: `f<W: Tr>` declares a struct `W` only in a NESTED block of its body; the
//@ mechanism: clause stands in the top-level block, where `W` is the generic parameter, and `f`
//@ mechanism: returns 10, which Tr's declaration of `k` ensures.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    #[logic]
    #[ensures(result == 10)]
    fn k() -> Int;
}

#[ensures(result@ == W::k())]
pub fn f<W: Tr>() -> u32 {
    {
        struct W;
        let _ = W;
    }
    10
}
