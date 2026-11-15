//@ expect: verify
//@ xfail: the unfold that made a caller-built aggregate decidable REFUSES a newtype
//@ xfail: definition, and this is the price. A newtype's invariant body is written against
//@ xfail: the collapsed `self.0 == self` identity, so substituting the CONSTRUCTOR for
//@ xfail: `self` would state the clause about the wrapper where it meant the payload —
//@ xfail: a rewrite that could land either side of the real obligation. Refusing it leaves
//@ xfail: the newtype shape exactly as undischargeable as every constructed aggregate was.
//@ xfail: Retire this directive when the payload, not the wrapper, is what `self` is bound
//@ xfail: to for a newtype.
//@ mechanism: the single-field twin of callee_typeinv_constructed_arg_letbound_control,
//@ mechanism: whose two-field spelling verifies. The pair is what says the surviving
//@ mechanism: refusal is the newtype guard and not the constructed argument.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct Five(pub i32);

impl Invariant for Five {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.0@ == 5 }
    }
}

#[ensures(result@ == 5)]
pub fn get(f: Five) -> i32 {
    f.0
}

#[ensures(result@ == 5)]
pub fn caller() -> i32 {
    get(Five(5))
}
