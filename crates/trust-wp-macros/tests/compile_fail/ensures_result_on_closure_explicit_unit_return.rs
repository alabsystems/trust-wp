// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-fail test: explicit `-> ()` closure still rejects free `result`
//! in `#[ensures]` (#2542).

#![feature(proc_macro_hygiene)]
#![feature(stmt_expr_attributes)]

use trust_wp_macros::ensures;

fn main() {
    // ERROR: `result` requires the annotated item to return a value
    let _clos = #[ensures(result == 0)]
    || -> () {};
}
