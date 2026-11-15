// demo/01_contracts.rs — the two clauses everything else is built from.
//
//   trust-wp demo/01_contracts.rs                 # verify every function
//   trust-wp --filter midpoint demo/01_contracts.rs
//   trust-wp --emit-smt --filter midpoint demo/01_contracts.rs

use trust_wp::{ensures, requires};

/// `#[requires]` is the caller's obligation; `#[ensures]` is what trust-wp
/// proves in return, for **every** input satisfying the precondition. `result`
/// names the return value.
///
/// The upper bound earns its place: **every** input means `i32::MAX` too, and
/// there `x + 1` overflows. Drop `x < 1_000_000` and re-run — trust-wp hands
/// back exactly that input rather than proving the postcondition.
#[requires(x > 0 && x < 1_000_000)]
#[ensures(result > x)]
pub fn increment(x: i32) -> i32 {
    x + 1
}

/// Several clauses of each kind are allowed; they conjoin.
///
/// The precondition is what makes the postcondition provable: without
/// `lo <= hi` the midpoint need not lie between them, and trust-wp would hand
/// back the pair that breaks it.
#[requires(lo <= hi)]
#[requires(lo >= 0 && hi <= 1000)]
#[ensures(result >= lo)]
#[ensures(result <= hi)]
pub fn midpoint(lo: i32, hi: i32) -> i32 {
    lo + (hi - lo) / 2
}

/// A proof covers every branch a test suite forgets — and every clause,
/// including the one saying the answer came from the inputs rather than out of
/// thin air. No precondition: this holds for all of `i32`.
#[ensures(result >= a && result >= b)]
#[ensures(result == a || result == b)]
pub fn max_of(a: i32, b: i32) -> i32 {
    if a > b {
        a
    } else {
        b
    }
}
