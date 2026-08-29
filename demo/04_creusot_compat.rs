// demo/04_creusot_compat.rs — the Creusot-compatible attribute lane.
//
//   trust-wp demo/04_creusot_compat.rs
//
// trust-wp ships `creusot_contracts` and `creusot_std` shims that re-export its
// own macros and std specs under the names Creusot users already type, so a
// file written against Creusot's attribute surface verifies unchanged. The
// front door links the shim for a lone `.rs` file exactly as it links
// `trust_wp`, so nothing about the invocation changes either.
//
// trust-wp is an independent ALab tool: not affiliated with, derived from, or
// endorsed by the Creusot project.

use creusot_contracts::{ensures, invariant, requires, variant};

#[requires(x > 0 && x < 1_000_000)]
#[ensures(result > x)]
pub fn increment(x: i32) -> i32 {
    x + 1
}

#[requires(n >= 0 && n <= 100_000)]
#[ensures(result == 0)]
#[invariant(c >= 0)]
#[variant(c)]
pub fn count_down(n: i32) -> i32 {
    let mut c = n;
    while c > 0 {
        c -= 1;
    }
    c
}
