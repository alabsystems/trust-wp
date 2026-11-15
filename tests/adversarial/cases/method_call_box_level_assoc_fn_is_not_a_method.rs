//@ expect: reject
//@ mechanism: `b.holds()` on `b: Box<S>`, where `Other::holds(x: Self)` has no `self` parameter and is implemented for `Box<S>`, and `AssocTrait::holds(self)` for `S`, both traits declared in the call's module. Rust's method probe never selects an associated function for a method call (only an item with a `self` parameter is a method candidate), so it passes the box by, derefs, and selects `<S as AssocTrait>::holds`. The collision family marks a member receiver-style when its FIRST PARAMETER has type `Self` (`identity::family_member`'s `receiver_is_self`), whatever the parameter is called, so the typed receiver lookup (`identity_typed::resolve_family_on_type`) counts `<Box<S> as Other>::holds` as the box level's one certain candidate, and D-162's own-module rule (`trait_certainly_in_scope`) binds it.
//@ accept-means: a method call was bound to an associated function Rust never selects for it, and the function was credited on it.
//@ WHY IT IS FALSE: `b.holds()` is `<S as AssocTrait>::holds`, which is `false`, so `f`'s postcondition is `false`. Creusot's `vc_f` is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0: `f verified ✓`, the trace binding `b.holds()` to `<Box<S> as Other>::holds`. Its control is method_call_box_receiver_trait_in_scope_control.rs, the same crate with `Other::holds(self)`, where Rust does select the box's method and `f` is true: both are credited, so the verdict does not depend on whether the box's item is a method. Also ACCEPTED built before D-160, D-161 and D-162: the hole predates them. There a box-level impl stopped the peel at the box. At D-163: rejected (`unknown`) with that refusal; the control verifies.
//@ fixed-by: D-163. rustc's type check of `f`'s `ensures` resolves `b.holds()` past the box to `<S as AssocTrait>::holds`, not the lookup's associated function `<Box<S> as Other>::holds`, so the call is refused (`logic function call `__lfidU__holds_N<site>_` was not resolved to one definition by the driver`). Its control method_call_box_receiver_trait_in_scope_control.rs, where rustc does select the box's method, still verifies.
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
    fn holds(x: Self) -> bool;
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
    fn holds(x: Self) -> bool {
        true
    }
}

// WRONG: `Other::holds` has no `self`, so it is no method; `b.holds()` derefs to <S as AssocTrait>::holds, which is false.
#[ensures(b.holds())]
pub fn f(b: Box<S>) {}
