//@ expect: reject
//@ mechanism: by-value parameters whose write the lane cannot name apart from the entry value (D-241
//@ mechanism: names it apart only for plain data written by stores it records): an array element store
//@ mechanism: (`a[0] = 5`), a write through a `&mut` borrow of an enum's payload, a field store to a
//@ mechanism: struct holding a `Box`, and a generic parameter re-bound. Each keeps the parameter's own
//@ mechanism: name for its value at the assertion, so an entry fact or a copy of the entry value would
//@ mechanism: speak of the written value: on D-240 the element store and the payload write left the
//@ mechanism: `#[requires]` standing, and a copy of a generic parameter followed the re-bind.
//@ accept-means: an assertion is credited from a parameter's entry `#[requires]`, or from a copy of its
//@ accept-means: entry value, after the body wrote the parameter in place.
//@ WHY THE CONTRACT IS FALSE: `array_index_write([0, 0])` has `a[0] == 5`; `enum_inner_write(Some(0))`
//@ WHY THE CONTRACT IS FALSE: has `o == Some(5)`; `boxed_field_write(Q { a: 3, b: .. })` has `q.a == 7`;
//@ WHY THE CONTRACT IS FALSE: `generic_copy_reads_other(0, 1)` has `c == 0`, `y == 1`.
//@ fixed-by: D-241: a write to a parameter's own storage that the lane does not name apart withdraws
//@ fixed-by: the entry facts that read the written part, and a field store re-binds no unrenamed parameter.
//@ teeth: MEASURED on D-240: each assertion verified; with D-241 each is rejected.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct Q {
    pub a: u32,
    pub b: Box<u32>,
}

#[requires(a[0]@ == 0)]
pub fn array_index_write(mut a: [u32; 2]) {
    a[0] = 5;
    proof_assert!(a[0]@ == 0);
}

#[requires(o == Some(0u32))]
pub fn enum_inner_write(mut o: Option<u32>) {
    if let Some(v) = &mut o {
        *v = 5;
    }
    proof_assert!(o == Some(0u32));
}

#[requires(q.a@ == 3)]
pub fn boxed_field_write(mut q: Q) {
    q.a = 7;
    proof_assert!(q.a@ == 3);
    let _ = q;
}

pub fn generic_copy_reads_other<T: Copy>(mut x: T, y: T) {
    let c = x;
    x = y;
    proof_assert!(c == y);
    let _ = x;
}
