//@ expect: reject
//@ mechanism: a trait method's `#[ensures(result + 1u8 > result)]` over a `u8` result, owed by an
//@ mechanism: impl that inherits it: the clause is typed by the trait-signature helper and read by
//@ mechanism: the impl's verification.
//@ mechanism: D-135 item 3: in the pinned oracle an operator on machine-integer operands means
//@ mechanism: creusot-std's logic impl, the type's bit-vector operation, which WRAPS (`u8 + u8` is
//@ mechanism: `creusot.int.UInt8$BW$.add`); a reading of it as mathematical integer arithmetic
//@ mechanism: proves a contract the oracle refutes.
//@ accept-means: an inherited trait postcondition's operator was read as mathematical integer
//@ accept-means: arithmetic where the impl owes it.
//@ WHY THE CONTRACT IS FALSE: <S as T>::m returns 255, and the wrapping sum 0 is not above 255.
//@ fixed-by: D-232
//@ teeth: ACCEPTED at exit 0 while every machine-integer operator of a clause was read as
//@ teeth: mathematical integer arithmetic; rejected once it reads at its operands' type.
//@ teeth: Found probing sideways from D-232.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub trait T {
    #[ensures(result + 1u8 > result)]
    fn m(&self) -> u8;
}

pub struct S;

impl T for S {
    fn m(&self) -> u8 {
        255
    }
}
