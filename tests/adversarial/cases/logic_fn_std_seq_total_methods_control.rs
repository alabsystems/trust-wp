//@ expect: verify
//@ mechanism: control for the program-side standard table's preconditions: `trust_wp_std` implements Creusot's `Seq` as executable Rust, so its methods carry no logic marker, and the table gives `tail`, `subsequence`, `set`, `index_logic`, `pop_front` and `pop_back` the precondition their executable forms panic without. Creusot declares each `#[logic]` with no `requires` (creusot-std `logic/seq.rs`): out of range the value is unspecified, not a violation. The walk that read rustc's resolution and owed the program table refused these bodies although their Creusot vcs are valid (`bug/217.rs`'s `ex`, `syntax/06_logic_function_contracts.rs`'s `sum` and `all_zero`). `FMap::lookup` reaches the type-check vehicle's own helper and owes nothing either way. The reject twin, a standard PROGRAM method the table gives a precondition, is logic_fn_std_program_method_precondition.rs.
//@ accept-means: n/a (control) — every call is of a total logic function.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[logic]
#[ensures(true)]
pub fn tail_of(s: Seq<Int>) -> Seq<Int> {
    s.tail()
}

#[logic]
#[ensures(true)]
pub fn sub_of(s: Seq<Int>, i: Int, j: Int) -> Seq<Int> {
    s.subsequence(i, j)
}

#[logic]
#[ensures(true)]
pub fn set_of(s: Seq<Int>, i: Int) -> Seq<Int> {
    s.set(i, 0)
}

#[logic]
#[ensures(true)]
pub fn index_of(s: Seq<Int>, i: Int) -> Int {
    s.index_logic(i)
}

#[logic]
#[ensures(true)]
pub fn ends_of(s: Seq<Int>) -> Seq<Int> {
    s.pop_front().pop_back()
}

#[logic]
#[ensures(true)]
pub fn lookup_of(m: FMap<Int, Int>, k: Int) -> Int {
    m.lookup(k)
}
