//@ expect: verify
//@ mechanism: the TRUE twin of closure_spec_call_requires_violated, identical but for the argument.
//@ mechanism: The shape of Creusot's bug/463: a clause-free function calls a closure whose own
//@ mechanism: `requires` it meets. The call lane charges the closure's OWN spec at the site
//@ mechanism: (`resolve_effective_spec`, keyed on `extract_closure_def_id_from_fn_call` and the user
//@ mechanism: spec table), and `unchecked_panic_sites` accounts the same site through the same
//@ mechanism: resolver and the same table, so the body is `verified` rather than capped.
//@ accept-means: n/a (control) — this contract is TRUE.
//@ fixed-by: n/a (control)
//@ teeth: control — `f::{closure#0} verified ✓`, `f verified ✓`, exit 0 with D-103; `f unknown
//@ teeth: (partial: panic paths unchecked (call to std::ops::Fn::call))` without it.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub fn f() {
    let c = #[requires(x@ < 1000)]
    #[ensures(result@ == x@ + 1)]
    |x: usize| x + 1;
    let _y = c(999);
}
