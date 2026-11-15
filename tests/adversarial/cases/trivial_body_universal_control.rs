//@ expect: verify
//@ mechanism: control for `trivial_body_universal_false`, shaped as should_succeed/specification/forall.rs `f` (Creusot's vc_f): a true universal over a trivial body is PROVED, not assumed
//@ teeth: over-refusal control — measured `assumed (axiom-only function ...)`, exit 2, before the fix; `verified ✓` after it
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(forall<_x: u32> true && true && true && true && true && true && true && true && true)]
pub fn f() {}
