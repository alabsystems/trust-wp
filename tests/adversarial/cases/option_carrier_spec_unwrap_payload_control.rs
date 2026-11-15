//@ expect: verify
//@ mechanism: a spec's `opt.unwrap()` over a parameter held in the generic `Option` carrier is
//@ mechanism: read through the carrier's bridge to the native `OptionInt`, the same bridge the
//@ mechanism: call's `Some(result) == self` reaches the value through, so the two are one
//@ mechanism: term. Before, the spec read an uninterpreted function of `opt` that no fact
//@ mechanism: mentioned, and this program was left unknown (quantifier-unhandled). The
//@ mechanism: extern_spec_project fixture's `get_value`, with std's unwrap spec in place of the
//@ mechanism: fixture's extern_spec; its false twins are option_carrier_spec_unwrap_claims_off_by_one
//@ mechanism: and option_carrier_spec_unwrap_claims_other_option.
//@ fixed-by: n/a (control)
//@ accept-means: n/a (control)
//@ teeth: n/a (control; MEASURED `get_value unknown (quantifier-unhandled)` on the campaign head
//@ teeth: and `get_value verified` with the bridged read; both false twins rejected on each)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(opt.is_some())]
#[ensures(result == opt.unwrap())]
pub fn get_value(opt: Option<i32>) -> i32 {
    opt.unwrap()
}
