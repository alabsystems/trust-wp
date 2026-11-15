//@ expect: reject
//@ mechanism: `w.holds()` on `w: W`, where `W: Deref<Target = S>`. `other::Other` is implemented for `W` but is not in scope where the call is written, so Rust's method probe passes `W` by, derefs through `W`'s `Deref`, and selects `<S as AssocTrait>::holds`. The typed receiver lookup (`identity_typed::resolve_family_on_type`) reads the autoderef levels only through `Box` (`peel_transparent_boxes`), so the one level it reads is `W`, its one candidate there is `<W as other::Other>::holds`, and it binds that. The user-`Deref` spelling of method_call_box_receiver_other_trait_out_of_scope.rs, which D-162 closed for `Box` only.
//@ accept-means: a method call was bound to a trait not in scope at the receiver, where Rust derefs and selects the in-scope trait's method on the target, and the function was credited on it.
//@ WHY IT IS FALSE: `w.holds()` is `<S as AssocTrait>::holds`, which is `false`, so `f`'s postcondition is `false`. Creusot's `vc_f` is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0: `f verified ✓`. Its control method_call_user_deref_other_trait_in_scope_control.rs differs only in `use other::Other;`, which makes `<W as other::Other>::holds` (`true`) what Rust selects: both are credited, so the verdict does not depend on whether the trait is in scope. Also ACCEPTED built before D-160, D-161 and D-162: the hole predates them. At D-163: rejected (`unknown`) with that refusal; method_call_user_deref_other_trait_in_scope_control.rs verifies.
//@ fixed-by: D-163. rustc's type check of `f`'s `ensures` resolves `w.holds()` through the deref to `<S as AssocTrait>::holds`, not the lookup's `<W as other::Other>::holds`, so the call is refused (`logic function call `__lfidU__holds_N<site>_` was not resolved to one definition by the driver`). The control, where `use other::Other;` makes the lookup's answer rustc's, still verifies.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait AssocTrait {
    #[logic]
    fn holds(self) -> bool;
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

pub mod other {
    use creusot_std::prelude::*;

    pub trait Other {
        #[logic]
        fn holds(self) -> bool;
    }

    impl Other for super::W {
        #[logic(open)]
        fn holds(self) -> bool {
            true
        }
    }
}

// WRONG: `other::Other` is not in scope here, so `w.holds()` derefs to <S as AssocTrait>::holds, which is false.
#[ensures(w.holds())]
pub fn f(w: W) {}
