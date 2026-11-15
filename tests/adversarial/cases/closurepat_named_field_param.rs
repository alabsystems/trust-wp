//@ expect: reject
//@ verdict: failed
//@ fixed-by: 0d0aaba9 (refusal), D-100 (a closure parameter pattern is the `let` it spells)
//@ mechanism: a named-field pattern as a pearlite CLOSURE PARAMETER, `|(S { a: aa, b: _bb }, z)|`.
//@ mechanism: The parser flattened closure-parameter patterns into a flat parameter list,
//@ mechanism: discarding the constructor name, so `aa` was the parameter at written index 0;
//@ mechanism: 0d0aaba9 refused the shape by name. Since D-100 the closure takes one fresh parameter
//@ mechanism: and its body destructures it with the `let` the pattern spells, so `aa` is placed from
//@ mechanism: the declaration exactly as structpat_let_destructure_ensures_reorder places it.
//@ accept-means: a closure parameter denotes the field declared first, not the one it names.
//@ WHY THE CONTRACT IS FALSE: the ensures says `result == a` (5); `g` returns `b` (0).
//@ teeth: NO END-TO-END TEETH, and none were ever measured: a pearlite closure applied through
//@ teeth: `Mapping::get` is not proved in either direction (its control
//@ teeth: closurepat_match_in_body_control fails too), so this verdict cannot tell a misreading
//@ teeth: from the right reading. MEASURED on 55ffd8f7: error, the 0d0aaba9 refusal; on the D-100
//@ teeth: tree: failed. The lowering is pinned by the parser unit test
//@ teeth: `a_constructor_in_a_closure_parameter_is_matched_as_a_let_is`, and the placement it
//@ teeth: reuses by the structpat_let_destructure_* reorder cases and their controls.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub struct S { pub b: u32, pub a: u32 }

#[requires(s.a@ == 5 && s.b@ == 0)]
#[ensures({ let f = |(S { a: aa, b: _bb }, z)| aa@ == z; f.get((s, result@)) })]
pub fn g(s: S) -> u32 { s.b }
