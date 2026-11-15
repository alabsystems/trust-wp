//@ expect: reject
//@ mechanism: compound single-field struct W(Vec) result rebuilt by aggregate W(v) after v.push: body lowers W(v) to v while the contract keeps tuple_get_0(result) (wp-s11 review probe n_rewrap_push)
//@ accept-means: the result length was identified with the parameter field length although the body pushed one element
//@ teeth: verified (false accept) at wp-s11 1d1d3e5; rejected on wp-campaign 31addb5 (sort conflict / counterexample); refused by the compound single-field aggregate guard (25a0223)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct W(pub Vec<u64>);

#[requires(w.0@.len() < 100)]
#[ensures(result.0@.len() == w.0@.len())]
pub fn rewrap_push(w: W) -> W {
    let mut v = w.0;
    v.push(7);
    W(v)
}
