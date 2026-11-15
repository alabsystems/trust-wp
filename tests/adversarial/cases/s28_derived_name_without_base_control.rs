//@ expect: verify
//@ mechanism: a name spelled with a derived suffix is refused only when its base is also a source value name.
//@ fixed-by: wp-s28 (creusot_frontend_checks::validate_derived_name_aliases)
//@ teeth: control for s28_derived_current_param.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

#[ensures(result == x_current)]
pub fn g(y: &mut u32, x_current: u32) -> u32 { *y = x_current; x_current }
