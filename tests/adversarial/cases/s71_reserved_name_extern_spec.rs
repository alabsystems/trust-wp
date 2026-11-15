//@ expect: reject
//@ verdict: error
//@ refused-with: lies in a namespace the verifier synthesizes names in
//@ mechanism: an `extern_spec!` ensures is ASSUMED at every call of its target, so its text
//@ mechanism: takes credit like any other clause — but its doc marker is spelled
//@ mechanism: `trust-wp:extern_spec:ensures=<text>`, a kind the reserved-name scan did not read.
//@ fixed-by: wp-s71 v3 (`push_marker_clauses` reads the extern_spec payload)
//@ accept-means: reserved `__trust_wp_*` spellings in an extern spec reach the encoder unrefused,
//@ accept-means: where they collide with the encoder's own synthesized tuple projections.
//@ WHY THIS MUST BE REFUSED: `__trust_wp_tuple_get_0` is the driver's own synthesized name;
//@ WHY THIS MUST BE REFUSED: `spec_tc::encode` leaves such calls untyped on the premise that
//@ WHY THIS MUST BE REFUSED: the driver refuses every one of them in spec text.
//@ teeth: (i) pre-fix build wp-s71 ca2b5ed4: no refusal — the clause reached ay, which died
//@ teeth: `ay error: process-isolated verifier exited without an outcome: signal 4`
//@ teeth: on the review probe of this extern_spec spelling. Fail-closed, but unrefused.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

extern_spec! {
    impl i32 {
        #[ensures(result == 3u32 && __trust_wp_tuple_get_0((1i32, 2i32)) == 7i32)]
        fn count_ones(self) -> u32;
    }
}

#[ensures(result == 1i32)]
pub fn driver_fn() -> i32 {
    let n: i32 = 7i32;
    let _c = n.count_ones();
    1i32
}

pub fn main() {
    let _ = driver_fn();
}
