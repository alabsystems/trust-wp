// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! False contracts whose names a destructuring closure parameter or a type
//! argument binds, each verified at exit 0 while the binding was read at
//! another place.

use trust_wp::prelude::*;

// A destructuring closure parameter is one parameter: `y` is the first
// field (the alias's value), `b` the second field of the first field. Each
// flattened name was bound to the field at its flattened position.
#[ensures(|(x @ y, _z)| y == 2)]
fn closure_alias_reads_the_first_field() -> (i32, i32) {
    (1, 2)
}

#[ensures(|((a, b), c)| b == 3)]
fn closure_nested_tuple_reads_the_inner_field() -> ((i32, i32), i32) {
    ((1, 2), 3)
}

pub trait Tag {
    const TAG: i32;
}

impl Tag for u8 {
    const TAG: i32 = 1;
}

impl Tag for u16 {
    const TAG: i32 = 2;
}

#[logic(open)]
fn tag<T: Tag>() -> i32 {
    T::TAG
}

// A type argument is part of which function is called; dropped, both sides
// read one `tag()`.
#[ensures(tag::<u8>() == tag::<u16>())]
fn type_arguments_differ() {}

fn main() {}
