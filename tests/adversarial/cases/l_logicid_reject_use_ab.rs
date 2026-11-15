//@ expect: reject
//@ mechanism: logic-fn identity — `use crate::b::k` must resolve through the module's imports, not to the first-registered `k` (definition order ab)
//@ fixed-by: s35 logic-fn identity (unique ids + owner-scope resolution + receiver dispatch)
//@ accept-means: a clause was checked against another definition that shares the short name
//@ teeth: accepted with exit 0 on wp-campaign fd7534d in at least one definition order (see s35 progress.md)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub mod a {
    use creusot_std::prelude::*;
    #[logic(open)] pub fn k() -> Int { pearlite!{0} }
}
pub mod b {
    use creusot_std::prelude::*;
    #[logic(open)] pub fn k() -> Int { pearlite!{10} }
}
pub mod c {
    use creusot_std::prelude::*;
    use crate::b::k;
    #[ensures(result@ == k())]
    pub fn f() -> u32 { 0 }
}
