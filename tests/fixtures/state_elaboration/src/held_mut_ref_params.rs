// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A `&mut` a parameter holds without being it (a binding of a destructuring
//! parameter pattern, a field of a tuple parameter, an element of an array
//! parameter) has no placement: the
//! state rule reads the states of a `&mut` parameter's own name, and the
//! driver models neither the pre-Creusot nor Creusot's reading of such a
//! read (`(^p)@ == (*p)@ + 1` below was unknown). `*p == old(*p)` verified, true
//! only if the destructured `p` is no `&mut` parameter for the dialect, which
//! the text does not say; the array's true `^a[0] == *a[0] + 1` was refuted
//! with a final value nothing resolves. Each is refused by name.

#![allow(unused)]

use trust_wp::prelude::*;

#[requires(*p < 100i32)]
#[ensures(*p == old(*p))]
fn destructured_old((p, q): (&mut i32, &mut i32)) {
    *p += 1;
}

#[requires(*p < 100i32)]
#[ensures((^p)@ == (*p)@ + 1)]
fn destructured_creusot((p, q): (&mut i32, &mut i32)) {
    *p += 1;
}

#[requires(*t.0 < 100i32)]
#[ensures(*t.0 == old(*t.0))]
fn tuple_param_old(t: (&mut i32, i32)) {
    *t.0 += 1;
}

#[requires(*a[0] < 100i32)]
#[ensures(^a[0] == *a[0] + 1i32)]
fn array_param_creusot(mut a: [&mut i32; 1]) {
    *a[0] += 1;
}

fn main() {}
