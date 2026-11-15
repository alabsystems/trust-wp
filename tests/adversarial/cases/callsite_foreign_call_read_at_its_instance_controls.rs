//@ expect: verify
//@ mechanism: control for reading a foreign callee's result at the call. `Iterator::next` declares
//@ mechanism: `Option<<Self as Iterator>::Item>`, a projection that may carry a borrow written
//@ mechanism: through by interior mutability, so D-107's result rule refused the `^self` of its
//@ mechanism: spec at every call and each `for` loop owed a fail-closed `false`; at a
//@ mechanism: `Range<isize>` (or `Range<usize>`) the call returns `Option<isize>`, which carries
//@ mechanism: nothing. `IndexMut::index_mut` on a `Vec<i32>` likewise returns `&mut i32`, whose
//@ mechanism: final value is the argument's (`^self` read through `^result`).
//@ fixed-by: D-124 (a foreign callee's result is read at the type the call returns)
//@ teeth: MEASURED (debug driver) with the call-site reading ablated to the declared signature
//@ teeth: (the reading at 05e9c0c7): all three unknown, `goal set carries a fail-closed false`,
//@ teeth: the dropped clause `next`'s `(*self).produces(seq![v], ^self)` and `index_mut`'s
//@ teeth: `ix.has_value((^self)@, ^result)`. On 576532d7, before D-107, all three verified.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

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
