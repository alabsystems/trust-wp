//@ expect: reject
//@ mechanism: the trait clause `x.holds()` has `x: Self` in a trait whose own `holds(&self)` takes its receiver by reference, and `Other`, in scope, has a blanket `impl<U> Other for U` whose `holds(self)` takes it by value. Rust's method probe tries every candidate by value before any autoref, so the clause is `<Self as Other>::holds`. The refinement reads the trait's clause in the trait's scope (D-160's `ResolveMode::TraitMethodCalls`), where `Self` is a generic parameter and `identity_typed::decl_for_generic_param` answers the one bound trait of `Self` declaring `holds` (`Trait::holds`), blind to the blanket impl; D-156's instantiation makes it `<Struct as Trait>::holds` at the impl, D-155's admission lets the id through the scope closure, and the refinement is checked against the wrong definition. The `Self`-receiver spelling of refinement_projection_in_scope_blanket_trait.rs.
//@ accept-means: a trait clause read at an impl was bound to the trait's own method where Rust selects an in-scope blanket impl by value, and the refinement was credited on it.
//@ WHY IT IS FALSE: at `Struct`, the trait promises `result ==> <Struct as Other>::holds(x)`, the blanket `holds` is `false`, and `check` returns `true`. Creusot's `refines` goal for `check` is invalid.
//@ teeth: MEASURED ACCEPTED, exit 0: `<Struct as Trait>::check refinement verified ✓`, with the identical verdict for its twin refinement_self_receiver_by_value_blanket_over_ref_trait_method_true_control.rs (blanket `holds` is `true`). Built before D-155 the same case is rejected (`unknown`): the scope closure refused every logic-function call in a refinement clause (`trait ensures clause names method call `.holds(..)`, which cannot be resolved in the clause's own scope`). D-155's admission of an instantiated id is what turned the misreading below it into a credit. At D-163: rejected (`unknown`) with that refusal; its twin is refused the same way (xfail, the price).
//@ fixed-by: D-163. The trait clause's `x.holds()` is kept as the lookup read it only where rustc's type check of that clause (its type-check body, tagged with the clause's kind and text) resolved it to the same definition. rustc resolved it to `Other::holds`, the lookup read `Trait::holds`, so the call is refused and the scope closure refuses the refinement (`trait ensures clause names call `__lfidU__holds_N<site>_(..)`, which cannot be resolved in the clause's own scope`).
//@ also-verified: <Struct as Trait>::check
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

pub trait Trait: Sized {
    #[logic]
    fn holds(&self) -> bool;

    #[ensures(result ==> x.holds())]
    fn check(x: Self) -> bool;
}

pub struct Struct;

impl Trait for Struct {
    #[logic(open)]
    fn holds(&self) -> bool {
        true
    }

    #[ensures(result)]
    fn check(x: Self) -> bool {
        true
    }
}
