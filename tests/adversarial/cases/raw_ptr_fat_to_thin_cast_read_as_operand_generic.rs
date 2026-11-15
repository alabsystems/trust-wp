//@ expect: reject
//@ mechanism: the generic spelling of raw_ptr_fat_to_thin_cast_read_as_operand: `*const [T]` cast
//@ mechanism: to `*const T` drops the length whatever `T` is, so the classification may not depend
//@ mechanism: on a concrete element type.
//@ fixed-by: D-145
//@ accept-means: a metadata-dropping cast over a generic element is read as the identity.
//@ WHY THE CONTRACT IS FALSE: two `*const [T]` with one address and different lengths meet the
//@ WHY THE CONTRACT IS FALSE: precondition and have equal thin casts, so the function returns false.
//@ teeth: ACCEPTED (`thin_differs verified`) before the cast was classified.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(p1 != p2)]
#[ensures(result)]
pub fn thin_differs<T>(p1: *const [T], p2: *const [T]) -> bool {
    p1 as *const T != p2 as *const T
}
