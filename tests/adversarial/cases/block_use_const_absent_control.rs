//@ expect: verify
//@ mechanism: control: the same contract with no import in the block: `K` has one meaning, the root's
//@ mechanism: constant (10), and `inner` returns 10. A refusal of
//@ mechanism: block_use_const_resolved_as_module_const_granted.rs and
//@ mechanism: block_glob_import_const_resolved_as_module_const_granted.rs must be keyed on the import.
//@ fixed-by: n/a (control for block_use_const_resolved_as_module_const_granted.rs; verified before
//@ fixed-by: D-195 and with it)
//@ accept-means: n/a (control)
//@ teeth: n/a (over-refusal control)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub const K: u8 = 10;

pub fn host() -> u8 {
    #[ensures(result == K)]
    fn inner() -> u8 {
        10
    }
    inner()
}
