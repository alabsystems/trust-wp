//@ expect: reject
//@ mechanism: `t.holds()` on `t: T` with `T: AssocTrait`, where `AssocTrait::holds(&self)` takes its receiver by reference and `Other`, in scope, has a blanket `impl<U> Other for U` whose `holds(self)` takes it by value. Rust's method probe tries every candidate by value before any autoref: the bound's method needs `&T` and does not apply there, the blanket one does, so the call is `<T as Other>::holds`. The typed receiver lookup (`identity_typed::resolve_family_on_type`) answers a generic receiver without counting any candidate (`innermost_special`), and `decl_for_generic_param` reads it as the declaration of `T`'s one bound trait declaring `holds`: `AssocTrait::holds`, whose grant `result` then proves `f`.
//@ accept-means: a method call on a generic receiver was bound to its bound trait's declaration where Rust selects another in-scope trait's method, and the function was credited on it.
//@ WHY IT IS FALSE: `t.holds()` is the blanket `<T as Other>::holds`, which is `false` at every `T`, so `f`'s postcondition is `false` (at `T = S`, say). Creusot's `vc_f` is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0: `f verified ✓`, with the identical verdict for its twin method_call_generic_receiver_by_value_blanket_over_ref_bound_true_control.rs (blanket `holds` is `true`). Also ACCEPTED built before D-160, D-161 and D-162: the hole predates them. At D-163: rejected (`unknown`) with that refusal; its twin is refused the same way (xfail, the price).
//@ fixed-by: D-163. rustc's type check of `f`'s `ensures` resolves `t.holds()` to `Other::holds`, not the lookup's `AssocTrait::holds`, so the call is refused (`logic function call `__lfidU__holds_N<site>_` was not resolved to one definition by the driver`). `<S as AssocTrait>::holds`'s own `ensures(result)` over its body `true` is true and stays credited.
//@ also-verified: creusot_test::<S as AssocTrait>::holds
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub trait AssocTrait {
    #[logic]
    #[ensures(result)]
    fn holds(&self) -> bool;
}

pub trait Other {
    #[logic]
    fn holds(self) -> bool;
}

impl<U> Other for U {
    #[logic(open)]
    fn holds(self) -> bool {
        false
    }
}

pub struct S;
impl AssocTrait for S {
    #[logic(open)]
    #[ensures(result)]
    fn holds(&self) -> bool {
        true
    }
}

#[ensures(t.holds())]
pub fn f<T: AssocTrait>(t: T) {}
