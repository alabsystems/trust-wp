// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Regression fixture for #940.
//! Verifies that `ensures(result.<field>)` is rewritten through the struct field map.

use trust_wp::ensures;

struct Ret {
    value: i32,
}

#[ensures(result.value > 0)]
fn make_ret() -> Ret {
    Ret { value: 1 }
}

fn main() {
    let _ = make_ret();
}
