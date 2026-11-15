//@ expect: reject
//@ mechanism: `Option::insert` returns a `&mut T` into the option it fills, so the value the option
//@ mechanism: is left with is `Some(^result)`: whatever the caller writes through the result. The
//@ mechanism: std contract states `(^self) == Some(value)` instead, in both spec tables (the builtin
//@ mechanism: registry's `core::option::Option::insert` and `option::specs::INSERT`), a final value
//@ mechanism: the callee cannot decide. At the call `^o` is read as `Some(0)`, and the caller's
//@ mechanism: `*r = 5` through the returned borrow is never seen. D-102/D-107 read a `&mut` result
//@ mechanism: through its own prophecy (`^p == ^result`), which is sound only when the callee's
//@ mechanism: clause states the final value that way; this clause does not. It is not D-124's
//@ mechanism: reading: `&mut T` and `&mut i32` both carry a borrow and neither exposes interior
//@ mechanism: mutability, so the declared signature and the instance agree.
//@ accept-means: a std contract that pins the final value of a `&mut` parameter lent into the
//@ accept-means: returned `&mut` lets any write through the result go unseen by the caller.
//@ WHY THE CONTRACT IS FALSE: `o` starts `None`; `insert(0)` makes it `Some(0)` and returns a
//@ WHY THE CONTRACT IS FALSE: borrow of its payload; `*r = 5` leaves it `Some(5)`, not `Some(0)`.
//@ fixed-by: OPEN — committed RED rather than hidden. Closing it means `Option::insert` states
//@ fixed-by: Creusot's `*result == value && ^self == Some(^result)`, in both spec tables.
//@ teeth: MEASURED (debug driver): ACCEPTED at exit 0 (`verified`, a strict UNSAT proof, no
//@ teeth: fail-closed goal), with the call read at its instance and, the review knob ablating the
//@ teeth: instance reading, at the declared signature alike. The local spelling (`o` a local, read
//@ teeth: after the write) is caught only as vacuous: the spec contradicts the write.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(*o == None)]
#[ensures(^o == Some(0i32))]
pub fn insert_then_write_through_result(o: &mut Option<i32>) {
    let r = o.insert(0i32);
    *r = 5i32;
}
