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
#[requires(n >= 0 && n <= 100_000)]
#[ensures(result >= 0)]
#[invariant(total >= 0 && i >= 0)]
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
/// `acc >= 1` survives `acc *= 2` because doubling is linear. Try changing the
/// body to `acc *= j` and re-running: preservation fails, because
/// `acc >= 1 && j >= 0` does not give `acc * j >= 1` when `j` is 0.
#[requires(k >= 0 && k <= 30)]
#[ensures(result >= 1)]
#[invariant(acc >= 1 && j >= 0)]
#[variant(k - j)]
pub fn power_of_two(k: i32) -> i32 {
    let mut acc = 1;
    let mut j = 0;
    while j < k {
        acc *= 2;
        j += 1;
    }
    acc
}
