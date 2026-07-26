// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(dead_code, unexpected_cfgs)]

use trust_wp::logic::{dead, Int};

pub struct Bag {
    value: i32,
}

#[trust_wp::opaque]
pub struct Secret {
    value: i32,
}

#[trust_wp::logic]
fn non_opaque_dead(flag: bool) -> Int {
    if flag {
        dead
    } else {
        Int(0)
    }
}

#[trust_wp::logic]
fn primitive_div(x: i32, y: i32) -> i32 {
    x / y
}

#[trust_wp::logic]
fn primitive_rem(x: i32, y: i32) -> i32 {
    x % y
}

#[trust_wp::logic]
fn int_literal_or_match(x: Int) -> Int {
    match x {
        1 | 2 => Int(0),
        _ => Int(1),
    }
}

#[trust_wp::logic]
fn unsupported_index(bag: Bag, idx: usize) -> i32 {
    bag[idx]
}

#[trust_wp::logic]
fn opaque_field(secret: Secret) -> i32 {
    secret.value
}

#[trust_wp::logic]
fn hidden_default(x: i32) -> i32 {
    x
}

#[trust_wp::logic(open(crate))]
fn scoped_open_leaks_hidden_default(x: i32) -> i32 {
    hidden_default(x)
}

fn main() {}
