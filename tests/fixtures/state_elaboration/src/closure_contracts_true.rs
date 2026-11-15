// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The true readings of `closure_contracts_false`. The alias spelling was
//! unknown while a closure's parameter aliases were left to the parser.

#![feature(stmt_expr_attributes, proc_macro_hygiene)]
#![allow(unused)]

use trust_wp::prelude::*;

pub fn let_alias_control() {
    let c = #[requires((*p)@ < 100)]
    #[ensures({ let q = p; old(q@) + 1 == q@ })]
    |p: &mut u32| {
        *p += 1;
    };
    let mut z = 1u32;
    c(&mut z);
}

pub fn plain_control() {
    let c = #[requires(*p < 100i32)]
    #[ensures((*p)@ == old((*p)@) + 1)]
    |p: &mut i32| {
        *p += 1;
    };
    let mut z = 1i32;
    c(&mut z);
}

fn main() {}
