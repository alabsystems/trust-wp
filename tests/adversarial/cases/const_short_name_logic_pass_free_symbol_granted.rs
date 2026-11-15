//@ expect: reject
//@ verdict: unknown
//@ refused-with: `__lfidU__ambiguous__constant__K` was not resolved to one definition by the driver
//@ mechanism: the logic pass checks logic-function postconditions before the constant table is
//@ mechanism: substituted into logic functions, so there a bare `K` is a free symbol. `a::p` claims
//@ mechanism: `result == K` (`a::K`, 0) and is `b::kb()`, whose body spells `K` in module `b` (10): one
//@ mechanism: free symbol stood for both constants and the postcondition was a tautology.
//@ accept-means: `a::p` claims `result == a::K`, which is 0, and is `b::K`, which is 10.
//@ fixed-by: D-111 (the table's refusals reach logic functions before the logic pass)
//@ teeth: MEASURED with the constant table fixed and the logic pass not reading it: ACCEPTED, exit 0, `creusot_test::a::p verified ✓`. The logic pass never read the table, so the parent commit accepts it too. At the fix both logic functions are refused and nothing is credited.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod a {
    use creusot_std::prelude::*;
    pub const K: u32 = 0;
    #[logic(open)]
    #[ensures(result == K)]
    pub fn p() -> u32 {
        crate::b::kb()
    }
}

pub mod b {
    use creusot_std::prelude::*;
    pub const K: u32 = 10;
    #[logic(open)]
    pub fn kb() -> u32 {
        K
    }
}
