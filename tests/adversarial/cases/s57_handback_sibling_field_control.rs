//@ expect: verify
//@ mechanism: control: the write is to the SIBLING field, so the handed-back borrow still points at the entry value and `*result == (*s).0` is TRUE. It pins that the s57 refusal compares the written place against the returned referent rather than refusing on the parameter's alias class alone.
//@ fixed-by: n/a — over-refusal guard for s57_handback_write_field.
//@ teeth: control - must keep verifying. Verified on the wp-campaign ce1d56fc worktree build
//@ teeth: and on the pre-front baseline build too.
//@ teeth: The first cut of the s57 refusal (435abd9b, alias-class only) DID reject it; 4da7f19a
//@ teeth: is what restores it, so this control has real teeth against an over-tightening.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

pub struct S(pub u32, pub u32);

#[ensures(*result == (*s).0)]
pub fn hb_other_field(s: &mut S) -> &mut u32 {
    s.1 = 9;
    &mut s.0
}
