//@ expect: reject
//@ verdict: error
//@ refused-with: as Deref>` runs outside ghost!(...) and snapshot!(...)
//@ mechanism: D-133 refuses, in program code, a call whose bounds ask a type holding a `Ghost` or
//@ mechanism: `Snapshot` for `PartialEq`, `PartialOrd`, `Eq`, `Ord` or `Hash`, because std's code then
//@ mechanism: runs the ghost's own run-time body. The same holds for `Deref` and `DerefMut`, which are
//@ mechanism: not in its list: `Option::as_deref` (`T: Deref`) and `as_deref_mut` (`T: DerefMut`) call
//@ mechanism: `<Ghost<T> as Deref>::deref` / `deref_mut` or `<Snapshot<T> as Deref>::deref` inside std,
//@ mechanism: and each panics. The deref is std's, not one rustc inserts in the caller's body, so the
//@ mechanism: implicit-deref check does not see it either. The verifier reads the call through the
//@ mechanism: `Option` spec as a `Some` of the ghost's value.
//@ accept-means: program bodies that hand an `Option` of a ghost to `as_deref`/`as_deref_mut` are
//@ accept-means: reported verified and the crate exits 0, though each call panics.
//@ fixed-by: D-193: a call whose bounds, the callee's or the selected impl's, ask `Deref`, `DerefMut`,
//@ fixed-by: `Borrow` or `BorrowMut` of a `Ghost` or `Snapshot` itself is refused in code that runs;
//@ fixed-by: trust-wp-std's own permission APIs, whose bodies never borrow, stay open.
//@ WHY THE CONTRACT IS FALSE: each function panics on every call ("Ghost deref called at runtime",
//@ WHY THE CONTRACT IS FALSE: "Ghost deref_mut called at runtime", "Snapshot deref called at runtime").
//@ teeth: ACCEPTED (all three verified, exit 0) at the campaign base 4c832882 and at wp-s140 598eed1d.
//@ teeth: Natively each function built against trust-wp-std panics inside std's `as_deref`. The
//@ teeth: `Result::as_deref` spelling is refused (a fail-closed `false`) and is not here. Refused at
//@ teeth: wp-s150; ghost_holder_box_deref_bound_control, `as_deref` on an `Option<Box<Ghost<i32>>>`,
//@ teeth: verifies at both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(result)]
pub fn ghost_as_deref() -> bool {
    let g: Ghost<i32> = ghost!(5i32);
    let o = Some(g);
    o.as_deref().is_some()
}

#[ensures(result)]
pub fn ghost_as_deref_mut() -> bool {
    let g: Ghost<i32> = ghost!(5i32);
    let mut o = Some(g);
    o.as_deref_mut().is_some()
}

#[ensures(result)]
pub fn snapshot_as_deref() -> bool {
    let s: Snapshot<i32> = snapshot!(5i32);
    let o = Some(s);
    o.as_deref().is_some()
}
