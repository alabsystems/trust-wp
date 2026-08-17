//@ expect: reject
//@ mechanism: singleton-carrier collapse — a ghost-identity token whose only payload is
//@ mechanism: PhantomData gets a datatype decl with a nullary constructor, making the SMT carrier
//@ mechanism: cardinality 1, which FORCES x == y (and hence id(x) == id(y)) for all tokens
//@ fixed-by: a224bb2 (resfid — opaque uninterpreted sort for ghost-identity tokens via a
//@ fixed-by: path-gated AdtDecl skip in collect_adt_decls_from_ty)
//@ accept-means: the ghost-identity tokens are SMT singletons again. Every resource-algebra
//@ accept-means: separation law is then vacuous: distinct resources are provably the same
//@ accept-means: resource, so exclusivity, agreement and authority contracts all become
//@ accept-means: unfalsifiable. memory/resource-fidelity-design.md called this exact program out:
//@ accept-means: "`#[ensures(x == y)]` over two arbitrary Resources verifies today, a standing FA".
//@
//@ WHY THE CONTRACT IS FALSE: `x` and `y` are distinct `Excl` resources — an exclusive resource
//@ algebra forbids two owners sharing an id (that is what `valid_op_lemma` derives a
//@ contradiction from). Their ids are provably DIFFERENT; claiming they coincide is refutable.
//@ teeth: ★VERIFIED. Method (ii): the resfid path gate (`is_ghost_identity_token`) disabled in-tree,
//@ teeth: A/B'd in one build. Result: ACCEPTED — trust-wp proves that two distinct exclusive
//@ teeth: resources have the same id. The standing false accept named in the resfid design memo
//@ teeth: reproduces on demand.
// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

extern crate creusot_std;

use creusot_std::{ghost::resource::Resource, logic::ra::excl::Excl, prelude::*};

#[ensures(x.id() == y.id())]
pub fn ids_forced_equal(x: &mut Resource<Excl<i32>>, y: &Resource<Excl<i32>>) {
    let _ = (x, y);
}
