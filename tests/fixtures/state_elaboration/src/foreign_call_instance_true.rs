// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A call of a foreign item is read at the type it returns there. `Iterator::
//! next` declares `Option<<Self as Iterator>::Item>`, a projection that may
//! carry a borrow its holder writes through by interior mutability, so the
//! `^self` of its spec had no reading at any call and every `for` loop owed a
//! fail-closed `false`; on a `Range<isize>` it returns `Option<isize>`, which
//! carries nothing. `IndexMut::index_mut` on a `Vec<i32>` returns `&mut i32`,
//! read through its own prophecy (D-124).

#![feature(stmt_expr_attributes, proc_macro_hygiene)]
#![allow(unused)]

use trust_wp::prelude::*;

#[requires(n@ >= 0)]
#[ensures(result == n)]
pub fn for_range_counts_to_n(n: isize) -> isize {
    let mut i = 0;
    #[invariant(i@ == produced.len() && i <= n)]
    for _ in 0..n {
        i += 1;
    }
    i
}

#[ensures(result == n)]
pub fn for_range_usize(n: usize) -> usize {
    let mut i = 0usize;
    #[invariant(i@ == produced.len() && i <= n)]
    for _ in 0..n {
        i += 1;
    }
    i
}

#[requires(v@.len() > 0)]
#[ensures((^v)@.len() == v@.len())]
#[ensures((^v)@[0] == 5i32)]
pub fn index_mut_set(v: &mut Vec<i32>) {
    v[0] = 5;
}

fn main() {}
