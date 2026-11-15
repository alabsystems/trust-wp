//@ expect: verify
//@ xfail: the otherwise obligation `x@<2 && x@>=0 ==> !(x!=0 && x!=1)` needs integer reasoning; frozen ay returns unsat with no certificate (proof-trusted => unknown). Before wp-s29 it verified only via the circular LetAssume {x==0||x==1}.
//@ mechanism: otherwise arm made unreachable by the precondition
//@ accept-means: n/a (control) — TRUE contract, must keep verifying
//@ fixed-by: wp-s29 panic-paths-soundness
//@ teeth: n/a — over-refusal control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ < 2)]
#[ensures(result@ >= 1)]
pub fn f(x: u8) -> u8 {
    match x {
        0 => 1,
        1 => 2,
        _ => unreachable!(),
    }
}
