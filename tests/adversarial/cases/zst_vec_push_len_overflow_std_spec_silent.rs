//@ expect: reject
//@ mechanism: `Vec::push` (and `insert`, `extend_from_slice`, `append`, `VecDeque::push_back`
//@ mechanism: and `push_front`) panics with "capacity overflow" when it must grow past the most
//@ mechanism: the allocation can hold. For an element type with a size that needs an allocation
//@ mechanism: larger than any 64-bit address space, which fails first; for a zero-sized type the
//@ mechanism: capacity is `usize::MAX` and nothing is allocated, so a push onto a vector of
//@ mechanism: `usize::MAX` elements panics. The std spec states no precondition. `len <
//@ mechanism: usize::MAX` owed for every element type would refuse any push onto a vector nothing
//@ mechanism: bounds; owed for zero-sized ones only, it needs the call site to know the size, and a
//@ mechanism: generic element has none there.
//@ accept-means: a growth of a zero-sized-element vector at `usize::MAX` elements is trusted.
//@ fixed-by: OPEN — committed RED rather than hidden (D-121).
//@ WHY THE CONTRACT IS FALSE: `f` admits a `Vec<()>` of `usize::MAX` elements (reached by
//@ WHY THE CONTRACT IS FALSE: `usize::MAX` pushes, or `vec![(); usize::MAX]`), and pushing onto it
//@ WHY THE CONTRACT IS FALSE: panics with "capacity overflow".
//@ teeth: MEASURED as ACCEPTED, exit 0, `f verified ✓`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(true)]
pub fn f(v: &mut Vec<()>) {
    v.push(());
}
