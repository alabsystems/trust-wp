//@ expect: verify
//@ mechanism: the isolating twin of async_fn_mut_param_ensures_granted_at_unpolled_call, for D-117's grant rule on a free function. The same `ensures((^x)@ == 5)`, the same caller and the same unpolled `drop`; the only change is where `*x = 5` runs. Here it is the sync item's own body, before it returns a future that captures nothing, so the call does perform the write, the item is verified as an ordinary function, and its `ensures` is granted at the call. The grant is withheld only from an item that merely BUILDS a coroutine (`is_coroutine_body`), not from every item whose result is a future. MEASURED: the twin credits `f` before D-117's grant rule and is refused fail-closed under it; this control keeps `g` and `f` verified under both.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control) — `g` writes 5 through `x` before it returns, so `y` is 5 after the call whether or not the future is ever polled, and `f` returns 5.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

use std::future::Future;

#[ensures((^x)@ == 5)]
pub fn g(x: &mut u32) -> impl Future<Output = ()> {
    *x = 5;
    async {}
}

#[ensures(result@ == 5)]
pub fn f() -> u32 {
    let mut y = 0u32;
    drop(g(&mut y));
    y
}
