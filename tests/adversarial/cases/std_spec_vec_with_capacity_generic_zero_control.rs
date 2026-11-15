//@ expect: verify
//@ xfail: the price of sizing allocation specs at the call site: a generic element type has no byte
//@ xfail: size there, so the precondition keeps its size marker and the encoder refuses it, even
//@ xfail: for a capacity of 0 that no size can overflow (D-121).
//@ mechanism: the generic-caller side of spec_fn_vec_with_capacity_overflow_std_spec_silent: a
//@ mechanism: `Vec::<T>::with_capacity(0)` in a body generic over `T`. An XPASS here means a
//@ mechanism: generic element size became readable, which must not let a generic
//@ mechanism: `with_capacity(n)` with `n` unbounded verify.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — measured `unknown` (`std spec clause ... was not resolved at its call site`).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result@.len() == 0)]
pub fn f<T>() -> Vec<T> {
    Vec::with_capacity(0)
}
