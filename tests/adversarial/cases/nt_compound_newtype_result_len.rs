//@ expect: reject
//@ mechanism: compound single-field struct newtype collapse on the result side only (see nt_compound_newtype_control_identity)
//@ accept-means: the result projection result.0 was identified with a different term than the parameter projection w.0
//@ teeth: regression guard; rejected at df47962 and after (review probe nt1::a_id), no false-accept revision known
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct W(pub Vec<u64>);

#[ensures(result.0@.len() != w.0@.len())]
pub fn id_len_differs(w: W) -> W {
    w
}
