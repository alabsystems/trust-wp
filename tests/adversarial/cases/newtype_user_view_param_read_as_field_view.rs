//@ expect: reject
//@ mechanism: the parameter spelling of newtype_user_view_result_read_as_field_view: a by-value
//@ mechanism: single-field struct parameter is collapsed onto its scalar field, so `x.0@` and the
//@ mechanism: struct's own `x@` are one term and the clause is closed as `x@ == x@`, with no body.
//@ accept-means: a struct's own view was identified with its field's view.
//@ WHY THE CONTRACT IS FALSE: for every `x`, `x@` is `x.0@ + 1`, never `x.0@`.
//@ fixed-by: OPEN: committed RED, with newtype_user_view_result_read_as_field_view.
//@ teeth: LIVE: ACCEPTED, `same verified` at exit 0, on the campaign driver with wp-s152's
//@ teeth: Option-carrier change. The `x: &Shift` spelling is refuted.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct Shift(u32);

impl View for Shift {
    type ViewTy = Int;
    #[logic(open)]
    fn view(self) -> Int {
        pearlite! { self.0@ + 1 }
    }
}

#[ensures(x.0@ == x@)]
pub fn same(x: Shift) {}
