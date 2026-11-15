//@ expect: reject
//@ verdict: failed
//@ mechanism: the false twin of method_call_box_receiver_trait_in_scope_control.rs: the same two impls, both traits declared in the call's module, so `b.holds()` is `<Box<S> as Other>::holds` (`true`), found at the box before any deref. Binding the pointee's `<S as AssocTrait>::holds` (`false`) instead -- a lookup that skips the box level, or reads the deeper level first -- makes `!b.holds()` provable.
//@ accept-means: a method call on a box was bound to the pointee's method where Rust selects the box's own, in-scope trait method, and the function was credited on it.
//@ WHY IT IS FALSE: `b.holds()` is `<Box<S> as Other>::holds`, which is `true`, so `f`'s postcondition `!b.holds()` is `false`. Creusot's `vc_f` is invalid.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait AssocTrait {
    #[logic]
    fn holds(self) -> bool;
}

pub trait Other {
    #[logic]
    fn holds(self) -> bool;
}

pub struct S;
impl AssocTrait for S {
    #[logic(open)]
    fn holds(self) -> bool {
        false
    }
}

impl Other for Box<S> {
    #[logic(open)]
    fn holds(self) -> bool {
        true
    }
}

// WRONG: `b.holds()` is <Box<S> as Other>::holds, found before the deref, which is true.
#[ensures(!b.holds())]
pub fn f(b: Box<S>) {}
