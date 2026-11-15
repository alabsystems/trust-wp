//@ expect: verify
//@ xfail: `caller` verifies — it forwards its own `Option<Sum10>`, whose invariant it holds, so
//@ xfail: the clause owed where `T` is fixed discharges from that premise (D-141) — but `via` is
//@ xfail: `unknown (proof-trusted)`: ay proves its match and the strict certificate is withheld,
//@ xfail: exactly as for a concrete `Option<Sum10>` parameter. Retire this directive when that
//@ xfail: certificate is issued.
//@ mechanism: the TRUE twin of generic_hop_typeinv_enum_payload with the overwrite deleted.
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
pub fn caller(o: Option<Sum10>) -> i32 {
    via(o)
}
