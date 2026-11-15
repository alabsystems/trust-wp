// demo/03_loops.rs — loops, without unrolling anything.
//
//   trust-wp demo/03_loops.rs
//
// A bounded model checker would unroll these loops to some depth and report
// "no bug found up to N". trust-wp does not unroll: you supply the inductive
// argument and it discharges the obligations that make it a proof for every N.

use trust_wp::{ensures, invariant, requires, variant};

/// Four obligations come out of an annotated loop:
///
///   initialization  the precondition establishes the invariant on entry
///   preservation    the invariant survives one arbitrary iteration
///   postcondition   invariant + loop exit imply the `#[ensures]`
///   termination     `#[variant]` strictly decreases and stays non-negative
///
/// Arithmetic inside the loop is checked too: `total += i` must not overflow
/// `i32` on any iteration the invariant admits. `total >= 0` alone admits
/// `total == i32::MAX`, so the invariant also carries a bound on `total`.
/// Since ay reasons linearly, the bound is linear in `i` — and then the
/// largest `n` it closes is `46_340`, because `46_340 * 46_340 <= i32::MAX`.
#[requires(n >= 0 && n <= 46_340)]
#[ensures(result >= 0)]
#[invariant(total >= 0 && i >= 0 && i <= n && total <= 46_340 * i)]
#[variant(n - i)]
pub fn sum_to(n: i32) -> i32 {
    let mut total = 0;
    let mut i = 0;
    while i < n {
        total += i;
        i += 1;
    }
    total
}

/// The invariant is the induction hypothesis, so it has to be strong enough to
/// prove *itself* — not merely true.
///
/// `acc >= 1` survives `acc *= 2` because doubling is linear, but it does not
/// keep `acc * 2` inside `i32`: on its own it admits `acc == i32::MAX` at the
/// loop head, and the overflow obligation for `acc *= 2` fails. `acc <= 2 * limit`
/// closes it: the loop only doubles while `acc < limit`, so the doubled value
/// stays below `2 * limit`, and the precondition keeps `2 * limit` in range.
/// Try deleting that conjunct and re-running.
#[requires(limit >= 1 && limit <= 1_000_000_000)]
#[ensures(result >= limit)]
#[invariant(acc >= 1 && acc <= 2 * limit)]
#[variant(2 * limit - acc)]
pub fn next_power_of_two(limit: i32) -> i32 {
    let mut acc = 1;
    loop {
        if acc >= limit {
            break;
        }
        acc *= 2;
    }
    acc
}
