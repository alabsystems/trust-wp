//@ expect: verify
//@ xfail: a pearlite closure applied through `Mapping::get` in an ensures is not proved — the
//@ xfail: contract is TRUE and FAILS with a counterexample on the merged tip 4e4613be and after;
//@ xfail: pre-existing closure-encoding incompleteness, not the parser lowering
//@ mechanism: the control for closurepat_named_field_param: the same closure
//@ mechanism: destructures its parameter in the BODY with `match`, which is placed from the
//@ mechanism: declaration, as the parameter pattern now is (D-100). While this control fails,
//@ mechanism: that case's verdict cannot distinguish a misreading from the right reading.
//@ accept-means: n/a (control).
//@ teeth: n/a — control; MEASURED failed, exit 1, on 4e4613be and on the fixed binary.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct S { pub b: u32, pub a: u32 }

#[requires(s.a@ == 5 && s.b@ == 0)]
#[ensures({ let f = |p: S| match p { S { a: aa, b: _bb } => aa@ }; f.get(s) == result@ })]
pub fn g(s: S) -> u32 { s.a }
