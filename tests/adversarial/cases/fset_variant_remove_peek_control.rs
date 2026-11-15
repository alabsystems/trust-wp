//@ expect: verify
//@ mechanism: control for fset_variant_insert_nondecreasing.rs and
//@ mechanism: fset_variant_remove_unheld_nondecreasing.rs, the should_succeed row bug/vcgen's shape:
//@ mechanism: removing the set's own `peek` shortens a non-empty set by one. The decrease query names
//@ mechanism: `len`, `remove`, `peek` and `is_empty` but no `contains`; the FSet linking axioms go
//@ mechanism: through membership and are asserted anyway. A path condition that reads the function
//@ mechanism: being defined is not a hypothesis of the query. Before, the query saw uninterpreted
//@ mechanism: symbols and the crate stopped compiling on `does not strictly decrease`.
//@ teeth: control
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::{
    logic::{FSet, Int},
    prelude::*,
};

#[logic(open)]
#[requires(!s.is_empty())]
#[variant(s.len())]
pub fn peel(s: FSet<Int>) -> Int {
    let x = s.peek();
    let rest = s.remove(x);
    if rest.is_empty() {
        x
    } else {
        let rec = peel(rest);
        if x >= rec { x } else { rec }
    }
}

#[ensures(result == n)]
pub fn uses_peel(n: u32) -> u32 {
    n
}
