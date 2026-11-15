//@ expect: reject
//@ mechanism: `has_logic_marker` reads any `#[doc = "trust-wp:logic:.."]` as a `#[logic]`
//@ mechanism: function, whoever wrote it, and the program-context ghost validator skips a logic
//@ mechanism: body (`validate_ghost_value_uses` is `!is_logic`), so neither its ghost deref nor any
//@ mechanism: D-193 item 2 operation in it is refused. `#[logic]` replaces the run-time body with
//@ mechanism: `unreachable!()`; the marker written by hand keeps the body the user wrote, which runs.
//@ mechanism: A call to it is refused as a logic call, and a logic impl of a program trait method by
//@ mechanism: the logic recursion check, but named as a value and handed to `Option::map` it runs
//@ mechanism: inside `map` (logic_fn_named_as_value_in_program_context_panics). The logic-marker
//@ mechanism: twin of ghost_marker_written_by_hand_runs_ghost_deref, whose ghost marker D-193 item 1
//@ mechanism: honours only where trust-wp-macros wrote every copy; found probing D-193 sideways.
//@ fixed-by: OPEN — committed RED rather than hidden. Closing it means the logic marker counts only
//@ fixed-by: where trust-wp-macros wrote it (`marker_is_from_trust_wp_macros`, as the ghost and
//@ fixed-by: spec_tc markers), or a logic function named as a value outside a snapshot or ghost block
//@ fixed-by: is refused as a call to it is.
//@ accept-means: a program body that hands a function marked logic by hand to `Option::map` is
//@ accept-means: credited `verified`, though that function's body dereferences a ghost at run time.
//@ WHY THE CONTRACT IS FALSE: `via_option_map` panics on every call ("Ghost deref called at runtime
//@ WHY THE CONTRACT IS FALSE: - only valid in ghost code").
//@ teeth: MEASURED on the debug driver of wp-s150 with D-193 and its follow-up: `via_option_map`
//@ teeth: verified, exit 0. Natively, built against trust-wp-std, it exits 101 with that panic. The
//@ teeth: same marker on an impl method of a program trait (local or `Drop`, `Deref`, `Add`,
//@ teeth: `PartialEq`) is refused by the logic recursion check, and on a closure is not read as logic.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[doc = "trust-wp:logic:"]
pub fn reads(g: &Ghost<i32>) -> bool {
    let v: i32 = **g;
    v == v
}

#[ensures(result)]
pub fn via_option_map() -> bool {
    let g: Ghost<i32> = ghost!(5i32);
    let _b = Some(&g).map(reads);
    true
}
