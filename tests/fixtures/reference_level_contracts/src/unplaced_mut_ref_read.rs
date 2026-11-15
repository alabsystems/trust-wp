// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! A clause that reads a parameter at a reference level its type does not
//! have, or reads a `&mut` parameter's referent through a value holding the
//! parameter some other way than by its name (a `let` of a tuple, a
//! constructor pattern), has no reading: `*x` of an `x: i32` was read as `x`
//! where spelled directly and not through a binder, and the state rule keyed
//! by a `&mut` parameter's name read the entry value where it could not see
//! the name. Each is refused by name. The chained comparison keeps an
//! ill-typed clause from the Rust type-check.

use trust_wp::{ensures, requires};

#[requires(*p < 100)]
#[ensures({ let t = (p, 0); *t.0 == old(*p) })]
fn deref_through_a_tuple_binding(p: &mut i32) {
    *p += 1;
}

#[requires(*p < 100)]
#[ensures(match Some(p) { Some(q) => *q == old(*p), None => true })]
fn deref_through_a_constructor_pattern(p: &mut i32) {
    *p += 1;
}

// In `ref a @ t` only `a` binds by reference: `t` is the `i32` itself, and
// `*t` has no reading. It was read as `*x`, i.e. `x`.
#[ensures({ let ref a @ t = x; *t == result && 0 < 1 < 2 })]
fn deref_of_a_by_value_subpattern(x: i32) -> i32 {
    x
}

#[ensures(*x == result && 0 < 1 < 2)]
fn deref_of_a_value_param(x: i32) -> i32 {
    x
}

#[ensures(^y == result && 0 < 1 < 2)]
fn final_of_a_shared_reference(y: &i32) -> i32 {
    *y
}

fn main() {}
