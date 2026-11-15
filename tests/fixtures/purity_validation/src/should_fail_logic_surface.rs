// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Logic-surface gaps the DRIVER diagnoses (`callbacks::purity_validation`)
//! on a crate that type-checks. The gaps that are type errors of the
//! specification — machine-integer `/` and `%`, indexing a type without an
//! `IndexLogic` impl — are in `should_fail_logic_surface_types.rs`: rustc
//! stops at a type error before the driver runs, so they cannot share a
//! build with these.

#![allow(dead_code, unexpected_cfgs)]

use trust_wp::logic::{dead, Int};

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
fn int_literal_or_match(x: Int) -> Int {
    match x {
        1 | 2 => Int(0),
        _ => Int(1),
    }
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
