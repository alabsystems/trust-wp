//@ expect: reject
//@ mechanism: a `proof_assert!` in a loop body reads a plain local the loop carries round its back
//@ mechanism: edge: `let mut y = 0; while i < n { proof_assert!(y == 0); y = 5; i += 1; }` (lp4), a
//@ mechanism: conditional write (l3b), a local computed from the counter (luniql), the counter
//@ mechanism: itself (lcount), a value a branch on the counter picks (lbranch), a `for` loop (lfor),
//@ mechanism: `loop` with `break` (lloop), a copy (lcopy), a call result (lcall, lcall2), a
//@ mechanism: `snapshot!` (lsnap), a ghost block (lghost), a write through `&mut y` handed to a
//@ mechanism: call (lmutcall), a by-`mut` parameter (lparam), a tuple field (ltuple), a `bool` a
//@ mechanism: call computes from the counter (lbool), an `Option` (lopt) and a `Vec` (lvec). The
//@ mechanism: program-point walk follows each acyclic path from the entry once, so it reached the
//@ mechanism: assertion on the FIRST iteration and read every local the loop writes at its
//@ mechanism: first-iteration value.
//@ accept-means: an assertion in a loop body is credited from the values the first iteration
//@ accept-means: sees, not from the loop head of an arbitrary iteration.
//@ also-verified: id, inc, is_zero
//@ WHY THE CONTRACT IS FALSE: with n = 2 the second iteration reads 5 (lp4, l3b, lcall2, lsnap,
//@ WHY THE CONTRACT IS FALSE: lghost), 1 (luniql, lcount, lcall, lmutcall), 2 (lbranch), 7
//@ WHY THE CONTRACT IS FALSE: (lfor), 3 (lloop, lparam), 7 for `z` (lcopy) and 5 (ltuple); lbool's
//@ WHY THE CONTRACT IS FALSE: `z` is false, lopt's `o` is `Some(0)` and lvec's length is 1.
//@ fixed-by: D-187 (on entering the header of a loop the assertion lies in, the walk re-binds
//@ fixed-by: every local the loop may change to its loop-head symbol; the loop's invariants and
//@ fixed-by: condition are stated about the same symbols)
//@ teeth: MEASURED (debug driver, store targo 9192 --unverified, ay db768acbd, clean ae4c8f59e):
//@ teeth: on 5f9337a5 (D-186) every proof_assert here was VERIFIED, and the functions lp4, l3b,
//@ teeth: luniql, lcount, lbranch, lloop, lcall, lcall2, lparam, ltuple, lbool and lopt too; with
//@ teeth: D-187 none is: each assertion is unknown, its counterexample ranging over a loop-head
//@ teeth: value (ltuple's and lopt's for their own reasons), and no function is verified.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result == x)]
pub fn id(x: u32) -> u32 {
    x
}

#[requires(*y < 1000i32)]
#[ensures(^y == *y + 1i32)]
pub fn inc(y: &mut i32) {
    *y += 1i32;
}

pub fn lp4(n: u32) {
    let mut y = 0i32;
    let mut i = 0u32;
    while i < n {
        proof_assert!(y == 0i32);
        y = 5i32;
        i += 1;
    }
}

pub fn l3b(n: u32) {
    let mut y = 0i32;
    let mut i = 0u32;
    while i < n {
        proof_assert!(y == 0i32);
        if i == 0u32 {
            y = 5i32;
        }
        i += 1;
    }
}

pub fn luniql(n: u32) {
    let mut i = 0u32;
    while i < n {
        let y = i as i32;
        proof_assert!(y == 0i32);
        i += 1;
    }
}

pub fn lcount(n: u32) {
    let mut i = 0u32;
    while i < n {
        proof_assert!(i == 0u32);
        i += 1;
    }
}

pub fn lbranch(n: u32) {
    let mut i = 0u32;
    let mut y;
    while i < n {
        if i == 0u32 {
            y = 1i32;
        } else {
            y = 2i32;
        }
        proof_assert!(y == 1i32);
        i += 1;
    }
}

pub fn lfor(n: u32) {
    let mut y = 0i32;
    for _k in 0..n {
        proof_assert!(y == 0i32);
        y = 7i32;
    }
}

pub fn lloop(n: u32) {
    let mut y = 0i32;
    let mut i = 0u32;
    loop {
        if i >= n {
            break;
        }
        proof_assert!(y == 0i32);
        y = 3i32;
        i += 1;
    }
}

pub fn lcopy(n: u32) {
    let mut y = 0i32;
    let mut i = 0u32;
    while i < n {
        let z = y + 1i32;
        proof_assert!(z == 1i32);
        y = 6i32;
        i += 1;
    }
}

pub fn lcall(n: u32) {
    let mut i = 0u32;
    while i < n {
        let r = id(i);
        proof_assert!(r == 0u32);
        i += 1;
    }
}

pub fn lcall2(n: u32) {
    let mut y = 0u32;
    let mut i = 0u32;
    while i < n {
        let r = id(y);
        proof_assert!(r == 0u32);
        y = 5u32;
        i += 1;
    }
}

pub fn lsnap(n: u32) {
    let mut y = 0i32;
    let mut i = 0u32;
    while i < n {
        let s = snapshot!(y);
        proof_assert!(*s == 0i32);
        y = 5i32;
        i += 1;
    }
}

pub fn lghost(n: u32) {
    let mut y = 0i32;
    let mut i = 0u32;
    while i < n {
        ghost! {
            proof_assert!(y == 0i32);
        };
        y = 5i32;
        i += 1;
    }
}

pub fn lmutcall(n: u32) {
    let mut y = 0i32;
    let mut i = 0u32;
    while i < n && i < 10u32 {
        proof_assert!(y == 0i32);
        inc(&mut y);
        i += 1;
    }
}

pub fn lparam(mut m: u32, n: u32) {
    let mut i = 0u32;
    m = 0u32;
    while i < n {
        proof_assert!(m == 0u32);
        m = 3u32;
        i += 1;
    }
}

pub fn ltuple(n: u32) {
    let mut t = (0i32, 0i32);
    let mut i = 0u32;
    while i < n {
        proof_assert!(t.0 == 0i32);
        t.0 = 5i32;
        i += 1;
    }
}

#[ensures(result == (x == 0u32))]
pub fn is_zero(x: u32) -> bool {
    x == 0u32
}

pub fn lbool(n: u32) {
    let mut i = 0u32;
    while i < n {
        let z = is_zero(i);
        proof_assert!(z);
        i += 1;
    }
}

pub fn lopt(n: u32) {
    let mut o: Option<u32> = None;
    let mut i = 0u32;
    while i < n {
        proof_assert!(o == None);
        o = Some(i);
        i += 1;
    }
}

pub fn lvec(n: u32) {
    let mut v: Vec<u32> = Vec::new();
    let mut i = 0u32;
    while i < n {
        proof_assert!(v@.len() == 0);
        v.push(1u32);
        i += 1;
    }
}
