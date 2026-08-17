//@ expect: reject
//@ mechanism: declare-collision degrade — a path-qualified field sort (std::sync::MutexGuard)
//@ mechanism: sharing a bare name with a sibling user ADT manufactures a false dependency cycle,
//@ mechanism: deadlocking the dependency-first Kahn order into the collision fallback, where a
//@ mechanism: datatype is declared over its own already-registered opaque twin
//@ fixed-by: 0012a91 (dependency-first ADT declaration + panic degrade) and 2ea36a1 (bare-name
//@ fixed-by: dependency requires rust_path identity; UF signatures canonicalize declare-first)
//@ accept-means: the collision stopped being fail-closed. Today a residual collision degrades to
//@ accept-means: Unknown(SolverPanic); if it ever degrades to "skip the obligation" or to an
//@ accept-means: assumed axiom instead, this false contract is accepted on a crate whose ADT
//@ accept-means: graph merely LOOKS ordinary.
//@
//@ WHY THE CONTRACT IS FALSE: `tag` returns `self.1`, and the contract claims it returns
//@ `self.1 + 1`. There is no input for which both hold.
//@ teeth: UNVERIFIED (honest). Method (ii): TWO independent knobs — the dependency-first ADT ordering
//@ teeth: (0012a91) reduced to plain name order, and the bare-name rust_path identity condition
//@ teeth: (2ea36a1) removed. Neither produced an accept at ay 153665fb9. Consistent with the degrade
//@ teeth: being fail-closed by construction (a collision yields Unknown(SolverPanic) or an ICE, and
//@ teeth: both are rejections); the ay 0.4 'register unknown field sorts on sight' behaviour the fixes
//@ teeth: targeted may also no longer be reachable at ay 0.5. Standing SHAPE gate.
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
    #[ensures(result == self.1 + 1i32)]
    pub fn tag(&self) -> i32 {
        self.1
    }
}

impl MutexGuard<'_> {
    #[ensures(result == self.1 + 1i32)]
    pub fn tag(&self) -> i32 {
        self.1
    }
}
