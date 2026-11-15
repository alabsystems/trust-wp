//@ expect: verify
//@ xfail: `Option::insert`'s std contract states `(^self) == Some(value)`, so the option's final
//@ xfail: value is read as `Some(0)` and the true `Some(5)` the caller writes through the returned
//@ xfail: borrow is not proved (unknown today). Creusot proves this contract (`^self == Some(^result)`).
//@ mechanism: control for option_insert_result_written_through_final_claimed.rs: the TRUE final
//@ mechanism: value of an option filled by `insert` and written through the returned `&mut`.
//@ fixed-by: n/a (control; open until the contract states the final value through `^result`)
//@ accept-means: n/a (control). An XPASS means the contract changed: the RED twin must then reject.
//@ teeth: n/a — control.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[requires(*o == None)]
#[ensures(^o == Some(5i32))]
pub fn insert_then_write_through_result_true(o: &mut Option<i32>) {
    let r = o.insert(0i32);
    *r = 5i32;
}
