// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

#![allow(clippy::trivially_copy_pass_by_ref)]

#[allow(dead_code)]
mod contracts_surface {
    use creusot_contracts::*;

    pub struct DummyProtocol;

    impl Protocol for DummyProtocol {
        type Public = i32;
    }

    pub fn typecheck(
        _perm: Perm<i32>,
        _resource: Resource<i32>,
        _invariant: NonAtomicInvariant<DummyProtocol>,
    ) {
        fn require_well_founded<T: WellFounded>() {}

        require_well_founded::<i32>();
    }
}

#[allow(dead_code)]
mod contracts_default_surface {
    use creusot_contracts::*;

    // Rust's prelude also exposes `Default`; `self::Default` proves the
    // glob-imported facade export resolved in this module.
    #[derive(self::Default)]
    enum Wrapper {
        #[default]
        A(i32, bool),
        B,
    }

    fn typecheck() -> Wrapper {
        Wrapper::default()
    }
}

#[allow(dead_code)]
mod contracts_prelude_default_surface {
    use creusot_contracts::prelude::*;

    // Rust's prelude also exposes `Default`; `self::Default` proves the
    // prelude facade forwarded the derive macro into this module.
    #[derive(self::Default)]
    enum Wrapper {
        #[default]
        A(i32, bool),
        B,
    }

    fn typecheck() -> Wrapper {
        Wrapper::default()
    }
}

#[allow(dead_code)]
mod std_root_surface {
    use creusot_std::{NonAtomicInvariant, Perm, Protocol, Resource, WellFounded};

    pub struct DummyProtocol;

    impl Protocol for DummyProtocol {
        type Public = i32;
    }

    pub fn typecheck(
        _perm: Perm<i32>,
        _resource: Resource<i32>,
        _invariant: NonAtomicInvariant<DummyProtocol>,
    ) {
        fn require_well_founded<T: WellFounded>() {}

        require_well_founded::<i32>();
    }
}

#[allow(dead_code)]
mod std_prelude_surface {
    use creusot_std::prelude::*;

    pub struct DummyProtocol;

    impl Protocol for DummyProtocol {
        type Public = i32;
    }

    pub fn typecheck(
        _perm: Perm<i32>,
        _resource: Resource<i32>,
        _invariant: NonAtomicInvariant<DummyProtocol>,
    ) {
        fn require_well_founded<T: WellFounded>() {}

        require_well_founded::<i32>();
    }
}

#[allow(dead_code)]
mod contracts_resolve_surface {
    use creusot_contracts::*;

    #[allow(clippy::trivially_copy_pass_by_ref)] // Testing resolve(&T) API surface
    pub fn typecheck(x: &i32) -> bool {
        resolve(x)
    }
}

#[allow(dead_code)]
mod std_prelude_resolve_surface {
    use creusot_std::prelude::*;

    #[allow(clippy::trivially_copy_pass_by_ref)] // Testing resolve(&T) API surface
    pub fn typecheck(x: &i32) -> bool {
        resolve(x)
    }
}

#[allow(dead_code)]
mod prelude_clone_surface {
    use creusot_std::prelude::{Clone, *};

    #[derive(Clone)]
    pub struct Wrapper(i32);

    pub fn typecheck(value: &Wrapper) -> Wrapper {
        let _ghost: Ghost<i32> = ghost!(value.0);
        value.clone()
    }
}

#[allow(dead_code)]
mod bitwise_proof_surface {
    use creusot_std::prelude::*;

    #[bitwise_proof]
    fn dummy_bitwise_fn(x: u32) -> u32 {
        x & 0xFF
    }
}

#[allow(dead_code)]
mod maintains_surface {
    use creusot_std::prelude::*;

    #[predicate]
    fn is_positive(x: i32) -> bool {
        x > 0
    }

    #[maintains(is_positive(*v))]
    fn keep_positive(_v: &mut i32) {}
}

#[allow(dead_code)]
mod open_inv_result_prelude_surface {
    use creusot_std::prelude::*;

    #[open_inv_result]
    fn make_value() -> u64 {
        42
    }
}

#[allow(dead_code)]
mod open_inv_result_macros_surface {
    use creusot_std::macros::*;

    #[open_inv_result]
    fn make_value() -> u64 {
        42
    }
}

#[allow(dead_code)]
mod contracts_bitwise_proof_surface {
    use creusot_contracts::*;

    #[bitwise_proof]
    fn dummy_bitwise_fn(x: u32) -> u32 {
        x & 0xFF
    }
}

#[allow(dead_code)]
mod contracts_maintains_surface {
    use creusot_contracts::*;

    #[predicate]
    fn is_positive(x: i32) -> bool {
        x > 0
    }

    #[maintains(is_positive(*v))]
    fn keep_positive(_v: &mut i32) {}
}

#[allow(dead_code, unused_variables, unused_imports)]
mod ra_view_surface {
    use creusot_std::{
        ghost::Ghost,
        logic::ra::{
            update::Update,
            view::{View as ViewRA, ViewRel, ViewUpdateInsert},
            UnitRA,
        },
        prelude::*,
        Resource,
    };

    /// Compile-surface check: the `fmap_view_view.rs` import cluster compiles.
    ///
    /// This function is never called — its purpose is to verify that the
    /// public type/method surface used by `fmap_view_view.rs` resolves
    /// through the `creusot_std` re-export layer.
    #[allow(clippy::needless_pass_by_value)] // API surface check: testing that owned ViewRA resolves
    fn typecheck_view_surface<R: ViewRel>(
        res: &mut Resource<ViewRA<R>>,
        shared: &Resource<ViewRA<R>>,
        upd: ViewUpdateInsert<R>,
        val: ViewRA<R>,
    ) {
        // Resource::alloc
        let _alloc: Ghost<Resource<ViewRA<R>>> = Resource::alloc(snapshot!(val));
        // Resource::core
        let _core: Resource<ViewRA<R>> = shared.core();
        // Resource::split_off
        let _split: Resource<ViewRA<R>> = res.split_off(
            snapshot!(ViewRA::<R>::unit()),
            snapshot!(ViewRA::<R>::unit()),
        );
        // Resource::update
        let _ = res.update(upd);
        // Resource::join_shared
        let _joined: &Resource<ViewRA<R>> = shared.join_shared(shared);
    }
}

#[allow(dead_code)]
mod prelude_partial_eq_surface {
    use creusot_std::prelude::PartialEq;

    #[derive(PartialEq)]
    pub struct Wrapper(i32);

    pub fn typecheck(a: &Wrapper, b: &Wrapper) -> bool {
        a == b
    }
}

#[allow(dead_code)]
mod prelude_deep_model_surface {
    use creusot_std::prelude::*;

    #[derive(self::DeepModel)]
    struct Wrapper<T: DeepModel>(T, bool);

    #[derive(self::DeepModel)]
    enum Either<T: DeepModel> {
        Left(T),
        Right { ok: bool },
    }

    fn require_deep_model<T: DeepModel>() {}

    pub fn typecheck() {
        require_deep_model::<i32>();
        let _ = core::mem::size_of::<Wrapper<i32>>();
        let _ = core::mem::size_of::<Either<i32>>();
        let _ = 1i32.deep_model();
    }
}

#[allow(dead_code)]
mod prelude_enumerate_surface {
    use creusot_std::prelude::*;

    fn typecheck() {
        let iter = (0..5).enumerate();
        let _: std::ops::Range<i32> = iter.iter();

        let iter = (0..5).enumerate();
        let _: usize = iter.n();
    }
}

#[allow(dead_code)]
mod prelude_rev_surface {
    use creusot_std::prelude::*;

    fn typecheck() {
        let iter = vec![1i32, 2, 3].into_iter().rev();
        let _: std::vec::IntoIter<i32> = iter.iter();
    }
}

#[allow(dead_code)]
mod prelude_skip_surface {
    use creusot_std::prelude::*;

    fn typecheck() {
        let iter = (0..5).skip(3);
        let _: std::ops::Range<i32> = iter.iter();

        let iter = (0..5).skip(3);
        let _: usize = iter.n();
    }
}

#[allow(dead_code)]
mod prelude_zip_surface {
    use creusot_std::prelude::*;

    fn typecheck() {
        let iter = (0..3).zip(3..6);
        let _: std::ops::Range<i32> = iter.itera();

        let iter = (0..3).zip(3..6);
        let _: std::ops::Range<i32> = iter.iterb();
    }
}

#[allow(dead_code)]
mod prelude_iterator_spec_surface {
    use creusot_std::prelude::*;

    pub fn typecheck_double_ended_iter_spec(iter: std::vec::IntoIter<i32>) -> bool {
        iter.produces_back(Seq::from(vec![1_i32]), Vec::<i32>::new().into_iter())
    }

    pub fn typecheck_from_iter_spec(result: &Vec<i32>) -> bool {
        result.from_iter_post(Seq::from(vec![1_i32, 2_i32]))
    }

    pub fn typecheck_cloned_ext<'a>(
        iter: std::iter::Cloned<std::slice::Iter<'a, i32>>,
    ) -> std::slice::Iter<'a, i32> {
        iter.iter()
    }

    pub fn typecheck_copied_ext<'a>(
        iter: std::iter::Copied<std::slice::Iter<'a, i32>>,
    ) -> std::slice::Iter<'a, i32> {
        iter.iter()
    }

    pub fn typecheck_fuse_ext(
        iter: std::iter::Fuse<std::vec::IntoIter<i32>>,
    ) -> std::vec::IntoIter<i32> {
        iter.iter()
    }

    pub fn typecheck_take_ext(
        iter: std::iter::Take<std::vec::IntoIter<i32>>,
    ) -> std::vec::IntoIter<i32> {
        iter.iter()
    }

    pub fn typecheck_take_n(iter: std::iter::Take<std::vec::IntoIter<i32>>) -> usize {
        iter.n()
    }

    pub fn typecheck_skip_ext(
        iter: std::iter::Skip<std::vec::IntoIter<i32>>,
    ) -> std::vec::IntoIter<i32> {
        iter.iter()
    }

    pub fn typecheck_skip_n(iter: std::iter::Skip<std::vec::IntoIter<i32>>) -> usize {
        iter.n()
    }

    pub fn typecheck_rev_ext(
        iter: std::iter::Rev<std::vec::IntoIter<i32>>,
    ) -> std::vec::IntoIter<i32> {
        iter.iter()
    }

    pub fn typecheck_take_iter_mut() {
        let mut iter = vec![1_i32, 2_i32].into_iter().take(1);
        let _: &mut std::vec::IntoIter<i32> = iter.iter_mut();
    }

    pub fn typecheck_filter_iterator_spec() {
        fn require_iterator_spec<I: IteratorSpec>(_iter: I) {}

        let iter = vec![1_i32, 2_i32].into_iter().filter(|x| *x > 1);
        require_iterator_spec(iter);
    }

    pub fn typecheck_iterator_spec_for_mut_ref() {
        fn require_iterator_spec<I: IteratorSpec>(_iter: I) {}

        let mut iter = vec![1_i32, 2_i32].into_iter();
        require_iterator_spec(&mut iter);
    }

    pub fn typecheck_sized_pointer_ext(ptr: *const i32) -> *const i32 {
        ptr.offset_logic(Int::from(1_usize))
    }
}

#[allow(dead_code)]
mod snapshot_module_surface {
    // Verify that `creusot_std::snapshot::Snapshot` resolves (Part of #1804).
    // In Creusot, Snapshot is available at both `creusot_std::Snapshot` and
    // `creusot_std::snapshot::Snapshot`.
    use creusot_std::snapshot::Snapshot;

    fn typecheck() {
        let _: Snapshot<i32> = Snapshot::capture(&42);
    }
}

#[allow(dead_code)]
mod perm_from_ref_mut_surface {
    use creusot_std::prelude::*;

    // Verify that `Perm::from_ref` and `Perm::from_mut` resolve on
    // `Perm<*const T>` (Part of #1804).
    fn typecheck_from_ref(x: &i32) {
        let (_ptr, _perm): (*const i32, Ghost<&Perm<*const i32>>) = Perm::from_ref(x);
    }

    fn typecheck_from_mut(x: &mut i32) {
        let (_ptr, _perm): (*mut i32, Ghost<&mut Perm<*const i32>>) = Perm::from_mut(x);
    }

    fn typecheck_from_box(x: Box<i32>) {
        let (_ptr, _perm): (*mut i32, Ghost<Box<Perm<*const i32>>>) = Perm::from_box(x);
    }
}

// --- Surface parity tests for #2682 types (atomics, peano, sync_view) ---

#[allow(dead_code)]
mod atomic_invariant_surface {
    use creusot_std::prelude::*;

    // Verify that AtomicInvariant and AtomicInvariantSC resolve through
    // creusot_std::prelude (Part of #2682 AC1).
    struct DummyProto;

    impl Protocol for DummyProto {
        type Public = u64;
    }

    fn typecheck_atomic_invariant(_inv: &Ghost<AtomicInvariant<DummyProto>>) {
        // Type resolves through the prelude.
    }

    fn typecheck_atomic_invariant_sc(_inv: &Ghost<AtomicInvariantSC<DummyProto>>) {
        // SC variant also resolves.
    }

    fn typecheck_tokens() {
        // Tokens is available via creusot_std (not prelude, since it's
        // ghost-internal). Tests that import creusot_std::Tokens work.
        fn require_tokens<'a>(_t: creusot_std::Tokens<'a>) {}
        let _ = require_tokens;
    }
}

#[allow(dead_code)]
mod atomic_relacq_surface {
    // Verify that release-acquire atomics resolve through creusot_std::std::sync
    // (Part of #2682 AC1, #2697 AC1).
    use creusot_std::std::sync::atomic_relacq;

    fn typecheck_types() {
        let _ = core::mem::size_of::<atomic_relacq::AtomicBool>();
        let _ = core::mem::size_of::<atomic_relacq::AtomicUsize>();
        let _ = core::mem::size_of::<atomic_relacq::AtomicI32>();
        let _ = core::mem::size_of::<atomic_relacq::AtomicU32>();
        let _ = core::mem::size_of::<atomic_relacq::AtomicU64>();
        // Committer types
        let _ =
            core::mem::size_of::<atomic_relacq::LoadCommitter<bool, atomic_relacq::AtomicBool>>();
        let _ =
            core::mem::size_of::<atomic_relacq::StoreCommitter<bool, atomic_relacq::AtomicBool>>();
        let _ =
            core::mem::size_of::<atomic_relacq::UpdateCommitter<u32, atomic_relacq::AtomicU32>>();
    }
}

#[allow(dead_code)]
mod atomic_sc_surface {
    // Verify that sequentially-consistent atomics resolve through creusot_std::std::sync
    // (Part of #2682 AC1, #2697 AC1).
    use creusot_std::std::sync::atomic_sc;

    fn typecheck_types() {
        let _ = core::mem::size_of::<atomic_sc::AtomicBool>();
        let _ = core::mem::size_of::<atomic_sc::AtomicUsize>();
        let _ = core::mem::size_of::<atomic_sc::AtomicI32>();
        let _ = core::mem::size_of::<atomic_sc::AtomicU32>();
        let _ = core::mem::size_of::<atomic_sc::AtomicU64>();
        // Committer types
        let _ = core::mem::size_of::<atomic_sc::LoadCommitter<atomic_sc::AtomicBool>>();
        let _ = core::mem::size_of::<atomic_sc::StoreCommitter<atomic_sc::AtomicBool>>();
        let _ = core::mem::size_of::<atomic_sc::UpdateCommitter<atomic_sc::AtomicU32>>();
    }
}

#[allow(dead_code)]
mod peano_surface {
    // Verify PeanoInt resolves through creusot_std (Part of #2682 AC4).
    use creusot_std::PeanoInt;

    fn typecheck() {
        let p = PeanoInt::new();
        let _: PeanoInt = p.incr();
        let _: u64 = p.to_u64();
    }
}

#[allow(dead_code)]
mod sync_view_surface {
    // Verify SyncView, AtView, and Timestamp resolve through creusot_std
    // (Part of #2682 AC4).
    use creusot_std::{sync_view::Timestamp, AtView, SyncView};

    fn typecheck_types() {
        let _ = core::mem::size_of::<SyncView>();
        let _ = core::mem::size_of::<AtView<u64>>();
        let _: fn() -> Timestamp = || panic!("spec-only");
    }
}

#[allow(dead_code)]
mod resolve_coherence_surface {
    use creusot_std::prelude::*;

    // Verify that resolve() works on reference types without explicit Resolve
    // bounds — confirms resolve_coherence is available (Part of #2682 AC3).
    fn typecheck_resolve_ref(x: &i32) -> bool {
        resolve(x)
    }

    fn typecheck_resolve_mut(x: &mut i32) -> bool {
        resolve(x)
    }
}

#[allow(dead_code)]
mod contracts_atomic_surface {
    use creusot_contracts::*;

    // Verify AtomicInvariant resolves through creusot_contracts::* glob
    // (the contracts shim re-exports from trust_wp::ghost::invariant).
    struct DummyProto;

    impl Protocol for DummyProto {
        type Public = u64;
    }

    fn typecheck(_inv: &Ghost<AtomicInvariant<DummyProto>>) {}
    fn typecheck_sc(_inv: &Ghost<AtomicInvariantSC<DummyProto>>) {}
}

// --- Surface parity tests for import paths used by compat tests ---

#[allow(dead_code)]
mod logic_ops_surface {
    // Verify that AddLogic, NthBitLogic, and IndexLogic resolve through
    // creusot_std::logic::ops (used by should_fail/impure_functions.rs
    // via logic::*, bitvector tests, slice/vector indexing tests).
    // These are trait definitions — we verify the import path resolves
    // by binding generic functions that reference the traits.
    use creusot_std::logic::ops::{AddLogic, IndexLogic, NthBitLogic};

    fn _require_add_logic<T: AddLogic>() {}
    fn _require_nth_bit_logic<T: NthBitLogic>() {}
    fn _require_index_logic<T: IndexLogic<usize>>() {}
}

#[allow(dead_code)]
mod std_mem_surface {
    use creusot_std::{
        logic::Int,
        std::mem::{align_of_logic, size_of_logic},
    };

    // Verify that size_of_logic and align_of_logic resolve through
    // creusot_std::std::mem (used by lang/size_of.rs).
    fn typecheck() {
        let _: Int = size_of_logic::<i32>();
        let _: Int = align_of_logic::<u64>();
    }
}

#[allow(dead_code)]
mod structural_resolve_surface {
    use creusot_std::resolve::structural_resolve;

    // Verify that structural_resolve resolves through creusot_std::resolve
    // (used by tests with explicit structural_resolve imports).
    fn typecheck(x: i32) -> bool {
        structural_resolve(x)
    }
}

#[allow(dead_code)]
mod fn_ghost_surface {
    use creusot_std::ghost::FnGhost;

    // Verify that FnGhost resolves through creusot_std::ghost
    // (used by ghost/ghost_let.rs and similar tests).
    fn require_fn_ghost<T: FnGhost>() {}

    fn typecheck() {
        require_fn_ghost::<fn() -> i32>();
    }
}

#[allow(dead_code)]
mod pred_cell_surface {
    use creusot_std::{cell::PredCell, ghost::Snapshot};

    // Verify that PredCell resolves through creusot_std::cell
    // (used by cell/01_basic.rs, cell/02_fib.rs, etc.).
    fn typecheck() {
        let cell = PredCell::new(42_i32, Snapshot::capture(&true));
        let _ = cell.get();
    }
}

#[allow(dead_code)]
mod logic_glob_surface {
    // Verify that `use creusot_std::logic::*` resolves and brings in
    // core types (used by should_fail/impure_functions.rs).
    use creusot_std::logic::*;

    fn typecheck() {
        let _: Int = Int::from(42_i32);
        let _: Seq<i32> = Seq::new();
        let _: FMap<i32, i32> = FMap::empty();
        let _: FSet<i32> = FSet::empty();
    }
}

#[allow(dead_code)]
mod logic_such_that_surface {
    use creusot_std::logic::such_that;

    // Verify that such_that resolves through creusot_std::logic
    // (used by tests importing creusot_std::logic::such_that).
    fn typecheck() -> i32 {
        such_that(|x: i32| x > 0)
    }
}

// --- Surface parity tests for Creusot examples lane imports (#2697) ---

#[allow(dead_code, unused_imports)]
mod examples_parallel_add_surface {
    // Exercises the exact import cluster from examples/parallel_add.rs
    use creusot_std::{
        declare_namespace,
        ghost::{
            invariant::{AtomicInvariantSC, Protocol, Tokens},
            perm::Perm,
            resource::{Authority, Fragment},
        },
        logic::{ra::excl::Excl, Id},
        prelude::*,
        std::{
            sync::atomic_sc::{AtomicI32, UpdateCommitter},
            thread::JoinHandleExt,
        },
    };

    declare_namespace! { TEST_PARALLEL_ADD }

    struct TestInv {
        _own: Box<Perm<AtomicI32>>,
        _auth: Authority<Option<Excl<bool>>>,
        _frag: Fragment<Option<Excl<bool>>>,
    }

    impl Protocol for TestInv {
        type Public = (AtomicI32, Id, Id);
    }

    fn typecheck(_tokens: Ghost<Tokens<'_>>) {
        let _ = Id(0);
        let _ = core::mem::size_of::<UpdateCommitter<AtomicI32>>();
    }
}

#[allow(dead_code, unused_imports)]
mod examples_message_passing_sc_surface {
    // Exercises the exact import cluster from examples/message_passing_sc.rs.
    // Part of #2697: verifies compile-error-free resolution for all paths.
    use creusot_std::{
        cell::PermCell,
        declare_namespace,
        ghost::{
            invariant::{AtomicInvariantSC, Protocol, Tokens},
            perm::Perm,
            resource::Resource,
        },
        logic::{ra::excl::Excl, Id},
        prelude::*,
        std::{
            sync::atomic_sc::{AtomicBool, LoadCommitter, StoreCommitter},
            thread::JoinHandleExt,
        },
    };

    declare_namespace! { TEST_MSG_SC }

    struct TestInv {
        _atomic_own: Box<Perm<AtomicBool>>,
        _cell_own: Option<Box<Perm<PermCell<i32>>>>,
        _res: Resource<Excl<()>>,
    }

    impl Protocol for TestInv {
        type Public = (AtomicBool, PermCell<i32>, Id);
    }

    fn typecheck() {
        let _ = core::mem::size_of::<LoadCommitter<AtomicBool>>();
        let _ = core::mem::size_of::<StoreCommitter<AtomicBool>>();
    }

    fn typecheck_open_borrowed<'a>(inv: Ghost<&'a AtomicInvariantSC<TestInv>>, tokens: Tokens<'a>) {
        inv.open(tokens, |state: &mut TestInv| {
            let _ = state;
        });
    }
}

#[allow(dead_code, unused_imports)]
mod examples_message_passing_relacq_surface {
    // Exercises the exact import cluster from examples/message_passing_relacq.rs.
    // Part of #2697: verifies compile-error-free resolution for all paths.
    use creusot_std::{
        cell::PermCell,
        declare_namespace,
        ghost::{
            invariant::{AtomicInvariant, Protocol, Tokens},
            perm::Perm,
            resource::Resource,
        },
        logic::{ra::excl::Excl, Id},
        prelude::*,
        std::sync::atomic_relacq::{AtomicBool, LoadCommitter, StoreCommitter},
        sync_view::{AtView, SyncView},
    };

    declare_namespace! { TEST_MSG_RELACQ }

    struct TestInv {
        _atomic_own: Box<Perm<AtomicBool>>,
        _at_view: Option<AtView<Box<Perm<PermCell<i32>>>>>,
        _res: Resource<Excl<()>>,
    }

    impl Protocol for TestInv {
        type Public = (AtomicBool, PermCell<i32>, Id);
    }

    fn typecheck() {
        // Relacq committers take <T, C> where T is value type, C is container.
        let _ = core::mem::size_of::<LoadCommitter<bool, AtomicBool>>();
        let _ = core::mem::size_of::<StoreCommitter<bool, AtomicBool>>();
        let _ = core::mem::size_of::<SyncView>();
    }

    fn typecheck_open_borrowed<'a>(inv: Ghost<&'a AtomicInvariant<TestInv>>, tokens: Tokens<'a>) {
        inv.open(tokens, |state: &mut TestInv| {
            let _ = state;
        });
    }
}

#[allow(dead_code, unused_imports)]
mod examples_persistent_array_surface {
    // Exercises the exact import cluster from examples/persistent_array.rs.
    // Part of #2697: verifies compile-error-free resolution for all paths.
    //
    // Note: Ag<T> does not implement UnitRA, so Authority<Ag<T>> and
    // Fragment<Ag<T>> cannot be used directly in struct fields here.
    // Persistent-array-style FMap resources should also type-check without
    // forcing the element type to satisfy runtime Clone/PartialEq bounds.
    use std::rc::Rc;

    use creusot_std::{
        cell::PermCell,
        declare_namespace,
        ghost::{
            invariant::{NonAtomicInvariant, NonAtomicInvariantExt as _, Protocol, Tokens},
            perm::Perm,
            resource::{Authority, Fragment},
        },
        logic::{
            ra::{agree::Ag, excl::Excl, fmap::FMapInsertLocalUpdate, update::LocalUpdate, RA},
            FMap, Id, Mapping,
        },
        prelude::*,
    };

    declare_namespace! { TEST_PARRAY }

    struct TestProto {
        _fmap: FMap<u32, i32>,
    }

    impl Protocol for TestProto {
        type Public = (PermCell<i32>, Id);
    }

    enum Inner<T> {
        Direct(Vec<T>),
    }

    struct NotClone;

    type PersistentArrayMap<T> = FMap<PermCell<Inner<T>>, Ag<Seq<T>>>;
    type PersistentArrayUpdate<T> = FMapInsertLocalUpdate<PermCell<Inner<T>>, Ag<Seq<T>>>;

    fn require_local_update<R: RA, U: LocalUpdate<R>>() {}

    fn persistent_array_fmap_surface<T>() {
        require_local_update::<PersistentArrayMap<T>, PersistentArrayUpdate<T>>();
        let _ = core::mem::size_of::<Authority<PersistentArrayMap<T>>>();
        let _ = core::mem::size_of::<Fragment<PersistentArrayMap<T>>>();
    }

    fn persistent_array_non_atomic_invariant_surface<'a>(
        inv: Ghost<Rc<NonAtomicInvariant<TestProto>>>,
        tokens: Ghost<Tokens<'a>>,
        token_ref: &'a Ghost<Tokens<'a>>,
    ) {
        let (_cell, _perm) = PermCell::new(0);
        let _created: Ghost<NonAtomicInvariant<TestProto>> = NonAtomicInvariant::new(
            ghost!(TestProto {
                _fmap: FMap::empty(),
            }),
            snapshot!((_cell, Id::fresh())),
            snapshot!(TEST_PARRAY()),
        );

        inv.open(tokens, |pa| {
            let _: Ghost<&mut TestProto> = pa;
        });

        let _: Ghost<&TestProto> = ghost!(inv.open_const(*token_ref));
        let _: Snapshot<(PermCell<i32>, Id)> = snapshot!(inv@.public());
    }

    fn typecheck() {
        let _ = core::mem::size_of::<Ag<u32>>();
        let _ = core::mem::size_of::<Mapping<u32, i32>>();
        let _ = core::mem::size_of::<FMapInsertLocalUpdate<u32, i32>>();
        let _ = core::mem::size_of::<Authority<Option<Excl<bool>>>>();
        let _ = core::mem::size_of::<Fragment<Option<Excl<bool>>>>();
        persistent_array_fmap_surface::<NotClone>();
    }
}

#[allow(dead_code, unused_imports)]
mod examples_parallel_add_n_surface {
    // Exercises the exact import cluster from examples/parallel_add_n.rs.
    // Part of #2697: verifies compile-error-free resolution for all paths.
    use creusot_std::{
        declare_namespace,
        ghost::{
            invariant::{AtomicInvariantSC, Protocol, Tokens},
            perm::Perm,
            resource::{Authority, Fragment},
        },
        logic::{ra::option::OptionLocalUpdate, real::PositiveReal, Id},
        prelude::{vec, *},
        std::{
            sync::atomic_sc::{AtomicI32, UpdateCommitter},
            thread::JoinHandleExt,
        },
    };

    declare_namespace! { TEST_PARALLEL_ADD_N }

    struct TestInv {
        _own: Box<Perm<AtomicI32>>,
        _auth: Authority<Option<PositiveReal>>,
    }

    impl Protocol for TestInv {
        type Public = (AtomicI32, Id);
    }

    fn typecheck() {
        let _ = core::mem::size_of::<OptionLocalUpdate<PositiveReal>>();
        let _ = core::mem::size_of::<UpdateCommitter<AtomicI32>>();
        let _v: Vec<i32> = vec![1, 2, 3];
    }
}

#[test]
#[allow(clippy::assertions_on_constants)]
fn compatibility_shims_expose_shared_types() {
    assert!(true);
}
