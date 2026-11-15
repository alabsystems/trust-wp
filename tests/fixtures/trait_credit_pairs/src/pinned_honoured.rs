// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `<W as Rd>::rd` refutes `Rd::rd`. A call pinned to V's impl rests on V's
//! impl alone; what `<V as Rd>::rd` returns is the one token the twin changes.

#![allow(unexpected_cfgs)]
#![allow(dead_code, unused_variables)]

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct W;
pub struct V;

pub trait Rd {
    #[ensures(result)]
    fn rd(&self) -> bool;
}

impl Rd for W {
    fn rd(&self) -> bool {
        false
    }
}

impl Rd for V {
    fn rd(&self) -> bool {
        true
    }
}

impl V {
    #[ensures(result)]
    pub fn m(&self) -> bool {
        self.rd()
    }
}

#[ensures(result)]
pub fn gen_read<T: Rd>(t: &T) -> bool {
    t.rd()
}

#[ensures(result)]
pub fn go_v() -> bool {
    gen_read::<V>(&V)
}

#[ensures(result)]
pub fn go_vd() -> bool {
    V.rd()
}

#[ensures(result)]
pub fn go_vm() -> bool {
    V.m()
}

#[ensures(result)]
pub fn go_wd() -> bool {
    W.rd()
}

fn main() {}
