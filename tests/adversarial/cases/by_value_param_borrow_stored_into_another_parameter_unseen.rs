//@ expect: reject
//@ mechanism: a by-value parameter that HOLDS a `&'a mut` (`h: H<'a>`) is stored into another
//@ mechanism: parameter's memory (`*v = Some(h)` with `v: &mut Option<H<'a>>`), so whoever holds `v`
//@ mechanism: after the call writes through the borrow and decides its final value. D-107's signature
//@ mechanism: check (`contract_signature::params_lent_into_another_parameter`) asks only of a parameter
//@ mechanism: that IS a `&mut` whether another parameter may absorb its borrow; a borrow held inside a
//@ mechanism: by-value parameter is never asked, and the function's lane reads `^h.0` as the last value
//@ mechanism: the body stored. The `v.push(h)` spelling is refused; the assignment spelling is not.
//@ mechanism: Found probing sideways from D-140; no drop glue is involved.
//@ accept-means: a function is credited with the final value of a borrow it handed to its caller's
//@ accept-means: memory, which the caller then writes.
//@ WHY THE CONTRACT IS FALSE: `let mut v = None; stash(H(&mut c), &mut v); *v.unwrap().0 = 9;` leaves
//@ WHY THE CONTRACT IS FALSE: `c` at 9, the final value of the borrow `h.0`; the contract says 0.
//@ fixed-by: OPEN: committed RED. The signature check must ask the same of every `&'r mut` a by-value
//@ fixed-by: parameter holds, and refuse a clause reading that parameter's final value when another
//@ fixed-by: parameter may absorb one.
//@ teeth: LIVE: ACCEPTED, exit 0, `stash` `verified`, before D-140 and after it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct H<'a>(pub &'a mut u32);

#[ensures((^h.0)@ == 0u32)]
pub fn stash<'a>(h: H<'a>, v: &mut Option<H<'a>>) {
    *h.0 = 0;
    *v = Some(h);
}
