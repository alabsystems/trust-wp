//@ expect: reject
//@ mechanism: logic-fn identity — two opaque `k` with different ensures shared one symbol (contradictory spec axioms) (definition order ba)
//@ fixed-by: s35 logic-fn identity (unique ids + owner-scope resolution + receiver dispatch)
//@ accept-means: a clause was checked against another definition that shares the short name
//@ teeth: accepted with exit 0 on wp-campaign fd7534d in at least one definition order (see s35 progress.md)
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;
pub mod b {
    use creusot_std::prelude::*;
    #[logic(opaque)] #[ensures(result == 10)] pub fn k() -> Int { dead }
}
pub mod a {
    use creusot_std::prelude::*;
    #[logic(opaque)] #[ensures(result == 0)] pub fn k() -> Int { dead }
    pub fn h() { proof_assert!(k() == 10); }
}
