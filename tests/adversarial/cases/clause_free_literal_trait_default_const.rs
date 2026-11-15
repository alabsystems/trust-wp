//@ expect: reject
//@ mechanism: D-142's literal rule reads an edge as dead when the discriminant is a value-stable
//@ mechanism: literal. `T::FLAG` is a trait constant whose default an implementation may override, so
//@ mechanism: its default `false` is not its value: the switch must be charged over the symbol, and
//@ mechanism: that charge is refuted.
//@ accept-means: the extractor read a trait constant as its default and the literal rule then read
//@ accept-means: the `panic!()` edge as dead.
//@ WHY THE CONTRACT IS FALSE: a clause-free `verified` claims no execution panics; `hop::<S>()` with
//@ WHY THE CONTRACT IS FALSE: `impl Tr for S { const FLAG: bool = true; }` panics.
//@ verdict: failed
//@ fn-failed: hop
//@ teeth: UNVERIFIED — no build translated the constant as its default; the case pins the shape.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub trait Tr {
    const FLAG: bool = false;
}

pub fn hop<T: Tr>() {
    if T::FLAG {
        panic!()
    }
}
