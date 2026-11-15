//@ expect: reject
//@ mechanism: The contract parser lowers `s[i]` to the method call `s.index_logic(i)`
//@ mechanism: (`contract_parser::unspanned::postfix`), the same term as an explicit `s.index_logic(i)`. On
//@ mechanism: `S`, which has an inherent `index_logic` and an `IndexLogic<Int>` impl, Rust reads `s[0]` as
//@ mechanism: `<S as IndexLogic<Int>>::index_logic(s, 0)` and `s.index_logic(0)` as the inherent method: the
//@ mechanism: method probe takes an inherent method before a trait's. The typed lookup reads neither
//@ mechanism: (`resolved=None`), so both stay one method-call term, and the postcondition's reflexive check
//@ mechanism: reads `e == e` as `true` with no solver query: the call the encoder would refuse is never
//@ mechanism: encoded. D-164 gave each REFUSED call a symbol of its own for this reason; a lowering that
//@ mechanism: makes two calls one term before any resolution is not reached by it.
//@ accept-means: a postcondition equating two different logic functions' values is credited with no query.
//@ WHY IT IS FALSE: `s[0]` is `2` and `s.index_logic(0)` is `1`; Creusot's `vc_prog` is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0 (`prog verified ✓`, no solver query) with D-163 and D-164 in force, and
//@ teeth: at the campaign tip: the typed lookup reads neither call (`resolved=None`), so neither D-163's
//@ teeth: confirmation nor D-164's refusal symbol is reached.
//@ fixed-by: OPEN — committed RED rather than hidden. Closing it means indexing is lowered to a term that
//@ fixed-by: no written call spells (or is read as `IndexLogic`'s method at the receiver), so the
//@ fixed-by: reflexive check cannot identify the two.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::logic::ops::IndexLogic;
use creusot_std::prelude::*;

pub struct S;

impl S {
    #[logic(open)]
    pub fn index_logic(self, i: Int) -> Int {
        1
    }
}

impl IndexLogic<Int> for S {
    type Item = Int;
    #[logic(open)]
    fn index_logic(self, i: Int) -> Int {
        2
    }
}

#[ensures(s[0] == s.index_logic(0))]
pub fn prog(s: S) {}
