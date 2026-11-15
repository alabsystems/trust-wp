//@ expect: reject
//@ mechanism: `w.holds()` on `w: W`, where `W: Deref<Target = S>`, `Other::holds(x: Self)` (no `self` parameter) is implemented for `W` and `AssocTrait::holds(self)` for `S`. Rust's method probe never selects an associated function for a method call, so it finds nothing at `W`, derefs through `W`'s `Deref`, and selects `<S as AssocTrait>::holds`. The collision family marks a member receiver-style when its first parameter has type `Self` (`identity::family_member`'s `receiver_is_self`), and the typed receiver lookup (`identity_typed::resolve_family_on_type`) peels only references and boxes, so at `W` its one candidate is `<W as Other>::holds` and it binds that. The box spelling is method_call_box_level_assoc_fn_is_not_a_method.rs.
//@ accept-means: a method call was bound to an associated function Rust never selects for it, and the function was credited on it.
//@ WHY IT IS FALSE: `w.holds()` is `<S as AssocTrait>::holds` of the deref target, which is `false`, so `f`'s postcondition is `false`. Creusot's `vc_f` is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0: `f verified ✓`. Also ACCEPTED built before D-160, D-161 and D-162: the hole predates them. At D-163: rejected (`unknown`) with that refusal.
//@ fixed-by: D-163. rustc's type check of `f`'s `ensures` resolves `w.holds()` through the deref to `<S as AssocTrait>::holds`, not the lookup's associated function `<W as Other>::holds`, so the call is refused (`logic function call `__lfidU__holds_N<site>_` was not resolved to one definition by the driver`).
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

#[derive(Clone, Copy)]
pub struct S;
impl AssocTrait for S {
    #[logic(open)]
    fn holds(self) -> bool {
        false
    }
}

pub struct W(pub S);
impl std::ops::Deref for W {
    type Target = S;
    fn deref(&self) -> &S {
        &self.0
    }
}

impl Other for W {
    #[logic(open)]
    fn holds(x: Self) -> bool {
        true
    }
}

// WRONG: `Other::holds` is no method; `w.holds()` derefs `W` to `S` and is <S as AssocTrait>::holds, which is false.
#[ensures(w.holds())]
pub fn f(w: W) {}
