//@ expect: reject
//@ mechanism: the ENSURES lane's twin of closure_param_loop_write_assertion_stale_entry_fact: `stale_entry_facts::loop_invalidated_param_names` read the closure's `_2` as its second source parameter, of which there is none, so no entry fact was dropped and `(*y)@ == 7` survived the loop to discharge the postcondition.
//@ accept-means: a closure's postcondition about a by-reference parameter's pointee, which a loop overwrote, is discharged by the entry precondition.
//@ WHY THE POSTCONDITION IS FALSE: the loop body runs once and sets `*y` to 3, which the closure returns.
//@ teeth: MEASURED ACCEPTED, exit 0, on the parent commit: `parent::{closure#0} verified ✓`.
//@ fixed-by: D-106 — both lanes name invalidated locals through `name_invalidated_args`
//@ fn-failed: parent::{closure#0}
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn parent() {
    let c = #[requires((*y)@ == 7)]
    #[ensures(result@ == 7)]
    |y: &mut u32| -> u32 {
        let mut i = 0u32;
        #[invariant(i@ <= 1)]
        while i < 1 {
            *y = 3;
            i += 1;
        }
        *y
    };
    let _ = c;
}
