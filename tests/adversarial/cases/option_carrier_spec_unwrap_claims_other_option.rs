//@ expect: reject
//@ mechanism: two parameters held in the generic `Option` carrier, each read through the
//@ mechanism: carrier's bridge to `OptionInt` when a spec unwraps it. The bridge is one function
//@ mechanism: for both, so this guards against it identifying their payloads: the result is
//@ mechanism: `a`'s payload and the clause names `b`'s.
//@ WHY THE CONTRACT IS FALSE: `a == Some(1)`, `b == Some(2)`: `get` returns 1, `b.unwrap()` is 2.
//@ fixed-by: n/a (guards option_carrier_spec_unwrap_payload_control's bridged read)
//@ accept-means: the payloads of two different options are read as one.
//@ teeth: UNVERIFIED as a gate: no build is known to accept it. MEASURED unknown on the
//@ teeth: campaign head and with the bridged read, where its true twin (the clause naming `a`)
//@ teeth: verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(a.is_some() && b.is_some())]
#[ensures(result == b.unwrap())]
pub fn get(a: Option<i32>, b: Option<i32>) -> i32 {
    a.unwrap()
}
