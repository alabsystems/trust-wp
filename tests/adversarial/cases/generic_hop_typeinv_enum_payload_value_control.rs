//@ expect: verify
//@ xfail: `via` is unknown (proof-trusted): ay proves it and the strict certificate is withheld,
//@ xfail: as for a concrete `Option<Sum10>` body. Retire this directive when that certificate is
//@ xfail: rendered.
//@ mechanism: the value twin of generic_hop_typeinv_enum_payload: 3 and 7 keep the invariant, and
//@ mechanism: `caller` verifies: the owed match over `Some(<the aggregate caller wrote>)` is reduced
//@ mechanism: to the arm the constructor selects and unfolded (D-141). With that reading disabled by
//@ mechanism: a local knob `caller` is refuted on this TRUE program, the match left undecided.
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
pub fn via<T: Total>(o: Option<T>) -> i32 {
    match o {
        Some(t) => t.total(),
        None => 10,
    }
}

#[ensures(result@ == 10)]
pub fn caller(mut s: Sum10) -> i32 {
    s.a = 3;
    s.b = 7;
    via(Some(s))
}
