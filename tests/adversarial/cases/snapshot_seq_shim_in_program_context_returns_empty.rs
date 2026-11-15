//@ expect: reject
//@ verdict: error
//@ refused-with: `Snapshot::push_back` runs outside ghost!(...) and snapshot!(...)
//@ mechanism: trust-wp-std gives `Snapshot<Seq<T>>` inherent `push_back` and `concat` shims for
//@ mechanism: Creusot's `snapshot!(s.push_back(x))` spelling. Each takes the snapshot by value and, at
//@ mechanism: run time, returns `Seq::empty()`, since a snapshot carries no value. Nothing keeps them
//@ mechanism: inside a snapshot: called in program code, their result is a real `Seq` the program reads,
//@ mechanism: and the verifier reads the call as the logical `push_back`/`concat` of the snapshot's
//@ mechanism: value. The program-context validator refuses a snapshot's deref and extraction
//@ mechanism: (`into_inner`, `inner`), not these. `Snapshot<FSet<T>>::insert`,
//@ mechanism: `Snapshot<FMap<K, V>>::insert` and `Snapshot<Mapping<A, B>>::set` rebuild their result
//@ mechanism: from an empty value the same way (read in the source, not probed).
//@ accept-means: program bodies that read a `Seq` built by the shims are reported verified and the crate
//@ accept-means: exits 0, while at run time the `Seq` is empty and each function returns `true`.
//@ fixed-by: D-193: a `Snapshot` inherent method other than a capture, `from_fn`, `new_phantom` and
//@ fixed-by: `into_ghost` is refused in code that runs, as a logic type's own methods are.
//@ WHY THE CONTRACT IS FALSE: at run time `t` is `Seq::empty()`, so each function returns `true`.
//@ teeth: ACCEPTED (both verified, exit 0) at the campaign base 4c832882 and at wp-s140 598eed1d.
//@ teeth: Natively, built against trust-wp-std, each function returns `true`. Refused at wp-s150;
//@ teeth: snapshot_seq_shim_in_snapshot_control, the same shims inside `snapshot!`, verifies at both.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

#[ensures(!result)]
pub fn push_back_read() -> bool {
    let s: Snapshot<Seq<i32>> = snapshot!(Seq::empty());
    let t = s.push_back(1);
    t.is_empty()
}

#[ensures(!result)]
pub fn concat_read() -> bool {
    let s: Snapshot<Seq<i32>> = snapshot!(Seq::singleton(2));
    let t = s.concat(Seq::singleton(1));
    t.is_empty()
}
