//@ expect: verify
//@ xfail: D-141's price: an impl of a foreign trait's method holds no parameter premise, since std
//@ xfail: reaches it from code no lane walks, so `from`, dividing by a value only the invariant
//@ xfail: bounds, is refuted. Creusot charges `inv` at every call, std's included.
//@ xfail-verdict: failed
//@ mechanism: the TRUE twin of std_question_mark_to_local_from_typeinv_uncharged.rs: the value
//@ mechanism: converted keeps its invariant.
//@ teeth: control — verified with the three route arms knobbed off, on a premise no route owed.
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

pub struct Out {
    pub v: i32,
}

impl From<Sum10> for Out {
    fn from(s: Sum10) -> Out {
        let r = s.a + s.b;
        Out { v: 100 / (r - 2) }
    }
}

#[ensures(true)]
pub fn caller() -> Result<i32, Out> {
    let e: Result<i32, Sum10> = Err(Sum10 { a: 3, b: 7 });
    let v = e?;
    Ok(v)
}
