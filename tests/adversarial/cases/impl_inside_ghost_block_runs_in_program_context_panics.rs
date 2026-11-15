//@ expect: reject
//@ mechanism: `ghost!` keeps its block under `cfg(trust_wp)`, and behind `if false` in every other
//@ mechanism: build, so the block's statements never run; an item written in it is still an item.
//@ mechanism: An `impl S { .. }` or `impl Run for S { .. }` inside `ghost! { .. }` is compiled natively
//@ mechanism: and its methods are callable from program code anywhere, but the program-context
//@ mechanism: validator exempts every expression whose span lies inside a ghost block's span
//@ mechanism: (`ProgramContextGhostApiValidator::is_in_ghost_context`, over the ghost spans of every
//@ mechanism: body owner), so the method's `*g` on a `Ghost` is never checked, and the verifier reads
//@ mechanism: the deref as the ghost's value. The exemption is meant for closures a ghost block holds,
//@ mechanism: which run only with it. Found probing D-193's "what runs is what trust-wp's macros
//@ mechanism: wrote" sideways: the macro wrote the `if false`, not the item's reach.
//@ also-verified: define_inherent, define_trait
//@ fixed-by: OPEN — committed RED rather than hidden. Closing it means a ghost block's span exempts
//@ fixed-by: only the body it is written in and the closures that share its typeck root, never an
//@ fixed-by: item's own body.
//@ accept-means: a method defined inside a ghost block that dereferences a ghost is credited
//@ accept-means: `verified`, and so is a program function calling it, and the crate exits 0, though the
//@ accept-means: call panics.
//@ WHY THE CONTRACT IS FALSE: `S::bad`, `<S as Run>::run`, `caller_inherent` and `caller_trait` panic
//@ WHY THE CONTRACT IS FALSE: on every call ("Ghost deref called at runtime").
//@ teeth: MEASURED ACCEPTED, exit 0, on the debug driver of wp-s150 with D-193: every function
//@ teeth: verified, the trait method's refinement too. Natively, built against trust-wp-std,
//@ teeth: `caller_inherent` exits 101 with that panic. The span exemption is older than D-193, so the
//@ teeth: campaign tip credits it too (not run).
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub struct S;

pub trait Run {
    #[ensures(result)]
    fn run(&self) -> bool;
}

#[ensures(result)]
pub fn define_inherent() -> bool {
    let _g = ghost! {
        impl S {
            #[ensures(result)]
            pub fn bad(&self) -> bool {
                let g: Ghost<i32> = Ghost::conjure();
                let v: i32 = *g;
                v == v
            }
        }
        0i32
    };
    true
}

#[ensures(result)]
pub fn define_trait() -> bool {
    let _g = ghost! {
        impl Run for S {
            #[ensures(result)]
            fn run(&self) -> bool {
                let g: Ghost<i32> = Ghost::conjure();
                let v: i32 = *g;
                v == v
            }
        }
        0i32
    };
    true
}

#[ensures(result)]
pub fn caller_inherent() -> bool {
    S.bad()
}

#[ensures(result)]
pub fn caller_trait() -> bool {
    S.run()
}
