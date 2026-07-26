// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-fail test: free `result` in `#[ensures]` on a closure whose body
//! is definitely unit (semicolon-terminated block) (#2542).

#![feature(proc_macro_hygiene)]
#![feature(stmt_expr_attributes)]

use trust_wp_macros::ensures;

fn main() {
    // ERROR: `result` requires the annotated item to return a value
    let _clos = #[ensures(result == 0)]
    || {
        let _ = 1;
    };
}
