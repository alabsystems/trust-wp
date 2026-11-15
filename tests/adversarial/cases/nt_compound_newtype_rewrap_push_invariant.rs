//@ expect: reject
//@ mechanism: type invariant on compound single-field struct W(Vec): result built by W(v) after a push must re-establish the invariant (wp-s11 review probe i_ret_push)
//@ accept-means: the invariant postcondition of a result that can hold 5 elements was discharged
//@ teeth: verified (false accept) at wp-s11 1d1d3e5; rejected on wp-campaign 31addb5 (sort conflict / counterexample); refused by the compound single-field aggregate guard (25a0223)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::{invariant::Invariant, prelude::*};

pub struct W(pub Vec<u64>);

impl Invariant for W {
    #[logic]
    fn invariant(self) -> bool {
        pearlite! { self.0@.len() < 5 }
    }
}

pub fn ret_push(w: W) -> W {
    let mut v = w.0;
    v.push(1);
    W(v)
}
