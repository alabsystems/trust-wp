//@ expect: reject
//@ mechanism: the logic-grant spelling of refinement_self_receiver_by_value_blanket_over_ref_trait_method.rs. `Outer::check`'s grant `result ==> x.holds()` has `x: Self`, and `uses_grant`'s clause `o.holds()` has `o: T`; `Outer::holds(&self)` takes its receiver by reference and the in-scope `Other` has a blanket `holds(self)` taken by value, so Rust selects `Other::holds` in both. `identity_typed::decl_for_generic_param` reads both as `Outer::holds`, the declaration of the parameter's one bound trait; D-156's discharge instantiates the grant at `O` as `<O as Outer>::holds` (`true`), credits `<O as Outer>::check` with it, and `uses_grant` is verified on the grant.
//@ accept-means: an implementation was credited with discharging a trait logic grant read with the trait's own method where Rust selects an in-scope blanket impl, and a generic caller was verified on that grant.
//@ WHY IT IS FALSE: `uses_grant` claims `T::check(o) ==> <T as Other>::holds(o)` for every `T: Outer`; at `T = O`, `check` is `true` and the blanket `holds` is `false`. Creusot's `vc_uses_grant` holds only on the grant, whose discharge at `O` is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0: `<O as Outer>::check establishes the postcondition of trait logic method `Outer::check`` and `uses_grant verified ✓`, with the identical verdict for its twin trait_logic_grant_self_receiver_by_value_blanket_over_ref_true_control.rs (blanket `holds` is `true`). Built before D-156 the same case is rejected (`unknown`): the discharge refused the grant's declaration call, the grant was withdrawn, and `uses_grant` was left unknown. D-156's instantiation of the declaration call is what turned the misreading below it into a credit. At D-163: rejected (`unknown`); its twin is refused the same way (xfail, the price).
//@ fixed-by: D-163. rustc's type check of the grant's clause and of `uses_grant`'s resolves the calls to `Other::holds`, not the lookup's `Outer::holds`, so both are refused: the grant is withdrawn and `uses_grant` is left unproved.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

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

pub trait Outer: Sized {
    #[logic]
    fn holds(&self) -> bool;

    #[logic]
    #[ensures(result ==> x.holds())]
    fn check(x: Self) -> bool;
}

pub struct O;

impl Outer for O {
    #[logic(open)]
    fn holds(&self) -> bool {
        true
    }

    #[logic(open)]
    fn check(_x: Self) -> bool {
        true
    }
}

#[ensures(T::check(o) ==> o.holds())]
pub fn uses_grant<T: Outer>(o: T) {}
