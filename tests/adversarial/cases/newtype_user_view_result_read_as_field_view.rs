//@ expect: reject
//@ mechanism: the single-field-struct collapse (build_newtype_param_set, then
//@ mechanism: simplify_newtype_field_access_expr) rewrites `tuple_get_0(result)` to `result` for a
//@ mechanism: struct whose one field is a scalar, so the field's view `result.0@` and the struct's
//@ mechanism: own view `result@` become one term, read at the field's sort. The struct's `View`
//@ mechanism: impl, whose view is the field's view plus one, is never consulted: the clause is
//@ mechanism: closed as `result@ == result@` with no solver query. A two-field struct keeps its
//@ mechanism: projection and the same clause is refuted; a `&Shift` parameter is not collapsed and
//@ mechanism: is refuted too.
//@ accept-means: a struct's own view was identified with its field's view.
//@ WHY THE CONTRACT IS FALSE: `make()` is `Shift(4)`: `result.0@` is 4 and `result@` is 5.
//@ fixed-by: OPEN: committed RED, with newtype_user_view_param_read_as_field_view.
//@ teeth: LIVE: ACCEPTED, `make verified` at exit 0, on the campaign driver with wp-s152's
//@ teeth: Option-carrier change (the collapse is older than both). The true `result@ == 5` is
//@ teeth: refuted there as well: a struct's user view is not unfolded at either arity.
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

#[ensures(result.0@ == result@)]
pub fn make() -> Shift {
    Shift(4)
}
