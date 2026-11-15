//@ expect: verify
//@ mechanism: the TRUE twin of seq_view_eq_callee_elem_read. Before the result view took the
//@ mechanism: components of the value it views, the element read on it was a second `select`
//@ mechanism: over fresh proxies equated to the source's; ay found the UNSAT but its proof went
//@ mechanism: through a Nelson-Oppen array/offset lemma the strict checker declines, so the
//@ mechanism: verdict was withheld (proof-trusted).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result@ == v@)]
pub fn same(v: Vec<u32>) -> Vec<u32> { v }

#[requires(v@.len() == 2 && v@[1]@ == 7)]
#[ensures(result@.len() == 2 && result@[1]@ == 7)]
pub fn c_elem(v: Vec<u32>) -> Vec<u32> {
    let r = same(v);
    r
}
