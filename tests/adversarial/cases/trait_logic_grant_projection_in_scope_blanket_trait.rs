//@ expect: reject
//@ mechanism: the logic-grant spelling of refinement_projection_in_scope_blanket_trait.rs. `Outer::check`'s grant `result ==> assoc.holds()` has `assoc: Self::Assoc` with `type Assoc: a::AssocTrait`; `a::AssocTrait` is not in scope there and the in-scope `Other` has a blanket impl, so Rust selects `<Self::Assoc as Other>::holds`, in the grant and in `uses_grant`'s clause alike. `identity_typed::decl_for_projection` reads both as `a::AssocTrait::holds`; D-156's discharge instantiates the grant at `O` as `<AssocStruct as a::AssocTrait>::holds` (`true`), credits `<O as Outer>::check` with it, and `uses_grant` is verified on the grant.
//@ accept-means: an implementation was credited with discharging a trait logic grant read with a trait Rust does not select, and a generic caller was verified on that grant.
//@ WHY IT IS FALSE: `uses_grant` claims `o.check(i) ==> <T::Assoc as Other>::holds(i)` for every `T: Outer`; at `T = O` `o.check(i)` is `true` and the blanket `holds` is `false`. Creusot's `vc_uses_grant` holds only on the grant, whose discharge at `O` is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0: `<O as Outer>::check establishes the postcondition of trait logic method `Outer::check`` and `uses_grant verified ✓`, with the identical verdict for its twin trait_logic_grant_projection_in_scope_blanket_trait_true_control.rs (blanket `holds` is `true`). Built before D-156 the same case is rejected (`unknown`): the discharge refused the grant's declaration call, the grant was withdrawn, and `uses_grant` was left unknown. D-156's instantiation of the declaration call is what turned the misreading below it into a credit. At D-163: rejected (`unknown`); its twin is refused the same way (xfail, the price).
//@ fixed-by: D-163. The grant's `assoc.holds()` and `uses_grant`'s `i.holds()` are each read against rustc's type check of their own clause, which resolves both to `Other::holds`; the lookup's `a::AssocTrait::holds` is refused in the grant (so the discharge owes nothing it can credit) and in `uses_grant`'s clause alike.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;
use creusot_std::prelude::*;

pub mod a {
    use creusot_std::prelude::*;

    pub trait AssocTrait {
        #[logic]
        fn holds(self) -> bool;
    }
}

pub trait Other {
    #[logic]
    fn holds(self) -> bool;
}

impl<T> Other for T {
    #[logic(open)]
    fn holds(self) -> bool {
        false
    }
}

pub trait Outer {
    type Assoc: a::AssocTrait;

    #[logic]
    #[ensures(result ==> assoc.holds())]
    fn check(self, assoc: Self::Assoc) -> bool;
}

pub struct AssocStruct;
impl a::AssocTrait for AssocStruct {
    #[logic(open)]
    fn holds(self) -> bool {
        true
    }
}

pub struct O;

impl Outer for O {
    type Assoc = AssocStruct;

    #[logic(open)]
    fn check(self, _assoc: AssocStruct) -> bool {
        true
    }
}

#[ensures(o.check(i) ==> i.holds())]
pub fn uses_grant<T: Outer>(o: T, i: T::Assoc) {}
