//@ expect: verify
//@ mechanism: declare-collision degrade — the over-refusal direction, which is the direction the
//@ mechanism: defect actually moved: the collision fallback left the ADT as an opaque twin, the
//@ mechanism: field premises were lost, and the obligation degraded to Unknown/ICE
//@ fixed-by: 0012a91 + 2ea36a1
//@ accept-means: n/a (control). This is THE case with teeth for the collision mechanism:
//@ accept-means: a fail-closed degrade cannot produce an accept, only a refusal, so the accept
//@ accept-means: side is unfalsifiable by construction and the refusal side is what regressed
//@ accept-means: (tests/should_succeed/mutex.rs, recovered by 2ea36a1).
//@ teeth: UNVERIFIED (honest). Same two knobs; this control kept verifying under both. See the
//@ teeth: adversarial twin for the full account.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::prelude::*;

// A parent whose name sorts BEFORE its own field's type: with the dependency-first ordering
// removed, `Alpha` is declared first, which registers `Zeta` as an opaque sort on sight, and the
// later `declare-datatype Zeta` collides with its own opaque twin (0012a91's RawVecInner ICE).
pub struct Zeta(pub i32);
pub struct Alpha(pub Zeta, pub i32);

// A path-qualified field sort sharing a BARE name with a sibling user ADT — the spurious Kahn
// cycle that deadlocked the topo order into the same collision fallback (2ea36a1, mutex.rs).
struct GuardInner<'a>(std::sync::MutexGuard<'a, i32>);
pub struct MutexGuard<'a>(GuardInner<'a>, pub i32);

impl Alpha {
    #[ensures(result == self.1)]
    pub fn tag(&self) -> i32 {
        self.1
    }
}

impl MutexGuard<'_> {
    #[ensures(result == self.1)]
    pub fn tag(&self) -> i32 {
        self.1
    }
}
