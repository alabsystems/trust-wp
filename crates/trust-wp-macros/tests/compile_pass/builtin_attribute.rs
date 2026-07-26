// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-pass test: `#[builtin("name")]` is accepted on functions, types,
//! and modules, and the item is passed through unchanged.

use trust_wp_macros::builtin;

#[builtin("int::add")]
fn add(a: i32, b: i32) -> i32 {
    a + b
}

#[builtin("seq::Seq")]
struct SeqStub;

#[builtin("prim::option")]
enum OptionStub {
    None,
    Some(i32),
}

#[builtin("theory::arith")]
mod arith_theory {
    pub fn zero() -> i32 {
        0
    }
}

fn main() {
    let _ = add(1, 2);
    let _ = SeqStub;
    let _ = OptionStub::Some(3);
    let _ = arith_theory::zero();
}
