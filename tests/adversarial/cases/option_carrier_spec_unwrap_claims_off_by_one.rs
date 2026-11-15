//@ expect: reject
//@ mechanism: the false twin of option_carrier_spec_unwrap_payload_control: the bridged read of
//@ mechanism: `opt.unwrap()` must give the payload the call returns, not a value free enough to
//@ mechanism: meet any claim about it.
//@ WHY THE CONTRACT IS FALSE: `opt == Some(0)`: `get_value` returns 0, and `opt.unwrap() + 1` is 1.
//@ fixed-by: n/a (guards option_carrier_spec_unwrap_payload_control's bridged read)
//@ accept-means: the spec's payload of an option is not tied to the value unwrap returns.
//@ teeth: UNVERIFIED as a gate: no build is known to accept it. MEASURED unknown on the
//@ teeth: campaign head and with the bridged read.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(opt.is_some())]
#[ensures(result == opt.unwrap() + 1)]
pub fn get_value(opt: Option<i32>) -> i32 {
    opt.unwrap()
}
