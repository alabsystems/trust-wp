//@ expect: verify
//@ mechanism: control for associated_type_callable_to_option_map_uncharged: the same generic host
//@ mechanism: and combinator, but the associated type is bounded by `Copy` alone and rides inside a
//@ mechanism: closure with no obligation. An associated type is a hand-off only when its item bounds
//@ mechanism: make it callable; a rule that refused every associated type fails here.
//@ accept-means: n/a (control) — nothing here can panic.
//@ fixed-by: n/a (control)
//@ teeth: control — `host verified`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait Tr {
    type V: Copy;
}

#[ensures(result@ == 1)]
pub fn host<T: Tr>(v: T::V, o: Option<usize>) -> u32 {
    let _ = o.map(|_j| v);
    1
}
