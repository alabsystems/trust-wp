//@ expect: verify
//@ xfail: ay proves the overflow obligation UNSAT but its strict certificate is not trust-free, so the
//@ xfail: verdict is `unknown (loop call obligations: proof-trusted)`, never FAILED.
//@ mechanism: control: `i += 1` cannot overflow while `i < l.m`, because `l.m` is a `u32`. The loop
//@ mechanism: call-obligation VC carried no range for an ADT field, so it reported a validated model
//@ mechanism: with `l.m == 4294967296` and `i == 4294967295` as `FAILED (loop call obligations)`: a
//@ mechanism: value the program cannot hold. It now carries the ADT field ranges the function-level
//@ mechanism: VC carries.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct Lim { pub m: u32 }

pub fn go(l: &Lim) {
    let mut i = 0u32;
    #[invariant(i <= l.m)]
    while i < l.m { i += 1; }
}
