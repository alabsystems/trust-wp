// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `go_star` is credited `verified*` (its contract names `lie`, an unverified
//! axiom) and rests on `gen_read`'s trait grant; what the only impl returns is
//! the one token the twin changes.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct W;

pub trait Rd {
    #[ensures(result)]
    fn rd(&self) -> bool;
}

impl Rd for W {
    fn rd(&self) -> bool {
        false
    }
}

#[logic(open)]
#[ensures(result)]
pub fn lie() -> bool {
    pearlite! { false }
}

#[ensures(result)]
pub fn gen_read<T: Rd>(t: &T) -> bool {
    t.rd()
}

#[ensures(result && (lie() || !lie()))]
pub fn go_star() -> bool {
    gen_read::<W>(&W)
}

fn main() {}
