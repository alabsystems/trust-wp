//@ expect: reject
//@ mechanism: the callee-precondition hole of closure_callee_requires_through_iterator_map_uncharged
//@ mechanism: through the other closure-taking `Iterator` methods whose builtin specs state no
//@ mechanism: closure precondition: `for_each`, `fold`, `any`, `all`, `find`, `position` and
//@ mechanism: `filter`. Each contract-free host hands `needs_nonzero` an unconstrained slice element
//@ mechanism: through a contract-free closure; one host per adapter. The hosts carry no contract:
//@ mechanism: a contracted host of these adapters crashes the process-isolated verifier (signal 4)
//@ mechanism: before and after D-118, a refusal that would hide the closure's verdict.
//@ accept-means: the crate exits 0 although calling any host with `&[0]` divides by zero in
//@ accept-means: `needs_nonzero`, reached through the closure the adapter runs.
//@ fixed-by: D-118
//@ teeth: every adapter here left its closure examined by nobody on the binary before D-118,
//@ teeth: measured one host per crate (exit 0, the host named in no verdict line). After it each
//@ teeth: closure is refuted on `needs_nonzero`'s precondition.
//@ also-verified: needs_nonzero
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[requires(x@ != 0)]
#[ensures(result@ == 10 / x@)]
pub fn needs_nonzero(x: u32) -> u32 {
    10 / x
}

pub fn via_for_each(v: &[u32]) -> u32 {
    v.iter().for_each(|&x| {
        needs_nonzero(x);
    });
    1
}

pub fn via_fold(v: &[u32]) -> u32 {
    let _ = v.iter().fold(0u32, |_a, &x| needs_nonzero(x));
    1
}

pub fn via_any(v: &[u32]) -> u32 {
    let _ = v.iter().any(|&x| needs_nonzero(x) == 1);
    1
}

pub fn via_all(v: &[u32]) -> u32 {
    let _ = v.iter().all(|&x| needs_nonzero(x) == 1);
    1
}

pub fn via_find(v: &[u32]) -> u32 {
    let _ = v.iter().find(|&&x| needs_nonzero(x) == 1);
    1
}

pub fn via_position(v: &[u32]) -> u32 {
    let _ = v.iter().position(|&x| needs_nonzero(x) == 1);
    1
}

pub fn via_filter(v: &[u32]) -> u32 {
    let _ = v.iter().filter(|&&x| needs_nonzero(x) == 1).next();
    1
}
