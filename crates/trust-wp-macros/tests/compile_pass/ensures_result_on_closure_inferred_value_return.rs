// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Compile-pass test: `#[ensures(result ...)]` is valid on closures with
//! inferred non-unit return types (#2542).
//!
//! Requires nightly features: `proc_macro_hygiene` allows attribute macros on
//! statements, and `stmt_expr_attributes` allows attributes on expressions.

#![feature(proc_macro_hygiene)]
#![feature(stmt_expr_attributes)]

use trust_wp_macros::ensures;

fn main() {
    let x = 0u32;
    let _clos = #[ensures(result == 0)]
    || x;

    let _clos2 = #[ensures(result == 0)]
    || {
        let _ = 1;
        x
    };
}
