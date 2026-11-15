//@ expect: reject
//@ verdict: failed
//@ fn-failed: caller
//@ also-verified: via, mid, <Sum10 as Total>::total
//@ mechanism: two generic hops whose type parameters are declared in opposite orders: `mid<B, A>`
//@ mechanism: calls `via<A, B>` with its `B` at `via`'s index 1, and `caller` fixes `mid`'s `B`
//@ mechanism: (index 0) at `Sum10`. Each instantiation reads the parameter's index in the generics
//@ mechanism: of the body it enters, so the clause owed at `via(a, b)` is `mid`'s `inv_B(b)` and
//@ mechanism: the one owed at `mid(s, 0u8)` is `Sum10`'s invariant of `s` (D-141).
//@ accept-means: the instantiation reads a type parameter at its position in some other function's
//@ accept-means: generics (`B` is `mid`'s first and `via`'s second), so `mid(s, 0u8)` charges `s`
//@ accept-means: at `u8`, which carries nothing, and `s` goes uncharged.
//@ WHY THE CONTRACT IS FALSE: `caller` overwrites `s` with 1 and 1, the impl returns 2, and
//@ WHY THE CONTRACT IS FALSE: `caller` claims 10.
//@ teeth: MEASURED with the instantiating call's clause dropped by a local knob: `caller` is
//@ teeth: credited `verified`, exit 0.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct Sum10 {
    pub a: i32,
    pub b: i32,
}

impl Invariant for Sum10 {
    #[logic(open)]
    fn invariant(self) -> bool {
        pearlite! { self.a@ + self.b@ == 10 }
    }
}

pub trait Total {
    #[ensures(result@ == 10)]
    fn total(self) -> i32;
}

impl Total for Sum10 {
    fn total(self) -> i32 {
        self.a + self.b
    }
}

#[ensures(result@ == 10)]
pub fn via<A, B: Total>(_a: A, b: B) -> i32 {
    b.total()
}

#[ensures(result@ == 10)]
pub fn mid<B: Total, A>(b: B, a: A) -> i32 {
    via(a, b)
}

#[ensures(result@ == 10)]
pub fn caller(mut s: Sum10) -> i32 {
    s.a = 1;
    s.b = 1;
    mid(s, 0u8)
}
