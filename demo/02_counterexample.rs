// demo/02_counterexample.rs — a contract that is FALSE, and how trust-wp says so.
//
//   trust-wp demo/02_counterexample.rs      # exits 1

use trust_wp::{ensures, requires};

/// Clamp `x` into `[lo, hi]`.
///
/// The postcondition is what the author *meant*. The body has an off-by-one:
/// the upper branch returns `hi - 1`, so the result can fall below `lo` when
/// the window is a single point. trust-wp does not need a test that hits that
/// case — it reports the counterexample directly.
#[requires(lo <= hi)]
#[ensures(result >= lo && result <= hi)]
pub fn clamp(x: i32, lo: i32, hi: i32) -> i32 {
    if x < lo {
        lo
    } else if x > hi {
        hi - 1
    } else {
        x
    }
}
