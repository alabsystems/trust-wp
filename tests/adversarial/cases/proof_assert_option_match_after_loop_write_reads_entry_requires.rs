//@ expect: reject
//@ mechanism: the `Option`/`Result`-match spellings of
//@ mechanism: proof_assert_reads_entry_requires_of_a_by_value_param_a_loop_writes.rs: a by-value parameter
//@ mechanism: pinned by `#[requires(x.is_none())]` (or `r.is_ok()`) and written inside a loop, then a
//@ mechanism: `proof_assert!` that matches it after the loop, or inside the loop above the write. The
//@ mechanism: proof_assert lane reads the precondition, a fact about the ENTRY value under the same name.
//@ mechanism: The match reads a constant the phantom upgrade split from the one the precondition's
//@ mechanism: `is_none()` constrains, so the stale fact does not reach the arms; a link of the two reads
//@ mechanism: (which D-218 refuses) let it prove each assertion. The `proof_assert!(x.is_none())`
//@ mechanism: spelling is credited with or without the link. Each function's own lane stays unknown (it
//@ mechanism: injects a fail-closed `false` for the loop).
//@ accept-means: an assertion about a parameter's entry value is credited `verified` after a loop
//@ accept-means: overwrote the parameter.
//@ WHY THE CONTRACT IS FALSE: every loop runs at least twice and stores `Some(i)` (or `Err(i)`), so each
//@ WHY THE CONTRACT IS FALSE: assertion after the loop reads `Some(2)` (`Err(2)`), and the in-loop assertion
//@ WHY THE CONTRACT IS FALSE: reads `Some(5)` from the second iteration on.
//@ fixed-by: the hole is OPEN in its other spelling,
//@ fixed-by: proof_assert_reads_entry_requires_of_a_by_value_param_a_loop_writes.rs; this spelling is
//@ fixed-by: rejected while the split is not linked (D-218).
//@ teeth: MEASURED with the link on this tree: `proof_assert in creusot_test::<fn> verified` for
//@ teeth: `after_loop`, `after_loop_payload` and `after_loop_result`, each beside a function verdict of
//@ teeth: unknown; `in_loop_above_the_write` is unknown with the link too (D-187 reads a local the loop
//@ teeth: changes at the loop head). With D-218 `after_loop`, `in_loop_above_the_write` and
//@ teeth: `after_loop_payload` are `unknown (refutation withheld)` and `after_loop_result` is unknown (the
//@ teeth: sort-coercion bridge); with neither, the case is rejected as `failed`.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x.is_none())]
pub fn after_loop(mut x: Option<u32>) {
    let mut i = 0u32;
    #[invariant(i <= 2u32)]
    while i < 2u32 {
        i += 1u32;
        x = Some(i);
    }
    proof_assert!(match x { Some(_) => false, None => true });
}

#[requires(x.is_none())]
pub fn in_loop_above_the_write(mut x: Option<u32>) {
    let mut i = 0u32;
    #[invariant(i <= 3u32)]
    while i < 3u32 {
        proof_assert!(match x { Some(_) => false, None => true });
        x = Some(5);
        i += 1u32;
    }
}

#[requires(x.is_none())]
pub fn after_loop_payload(mut x: Option<u32>) {
    let mut i = 0u32;
    #[invariant(i <= 2u32)]
    while i < 2u32 {
        i += 1u32;
        x = Some(i);
    }
    proof_assert!(match x { Some(v) => v == 7u32, None => true });
}

#[requires(r.is_ok())]
pub fn after_loop_result(mut r: Result<u32, u32>) {
    let mut i = 0u32;
    #[invariant(i <= 2u32)]
    while i < 2u32 {
        i += 1u32;
        r = Err(i);
    }
    proof_assert!(match r { Ok(_) => true, Err(_) => false });
}
