//@ expect: reject
//@ mechanism: the concrete spelling of clause_free_literal_trait_default_const: `S` overrides the
//@ mechanism: trait's default `false` with `true`, so the literal the switch reads selects the
//@ mechanism: `panic!()` edge, which must stay live.
//@ accept-means: the extractor read `<S as Tr>::FLAG` as the trait's default and the literal rule
//@ accept-means: then read the `panic!()` edge as dead.
//@ WHY THE CONTRACT IS FALSE: a clause-free `verified` claims no execution panics; every call of
//@ WHY THE CONTRACT IS FALSE: `hop` panics.
//@ verdict: error
//@ refused-with: vacuous (contradictory premises)
//@ teeth: UNVERIFIED — no build translated the constant as its default; the case pins the shape.
//@ teeth: With D-166 the taken `panic!()` arm is the literal `false` its gate owes; at the top level the
//@ teeth: premises contradict and `hop` is reported vacuous, never verified.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

pub trait Tr {
    const FLAG: bool = false;
}

pub struct S;

impl Tr for S {
    const FLAG: bool = true;
}

pub fn hop() {
    if <S as Tr>::FLAG {
        panic!()
    }
}
