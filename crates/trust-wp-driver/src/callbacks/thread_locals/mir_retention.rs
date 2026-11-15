// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Borrow-checked MIR retained across compiler workers, owned by one live context.

use std::{
    collections::HashMap,
    marker::PhantomData,
    sync::{Arc, LazyLock, Mutex, MutexGuard},
};

use rustc_borrowck::consumers::{BodyWithBorrowckFacts, BorrowSet, ConsumerOptions};
use rustc_hir::def_id::LocalDefId;
use rustc_middle::{mir::Body, ty::TyCtxt};

/// The exact borrow-check result read by extraction. The region-inference
/// context contains an Rc and must be dropped on its producing compiler worker.
pub(crate) struct RetainedBorrowckBody<'tcx> {
    origin: ContextKey,
    pub(crate) body: Body<'tcx>,
    pub(crate) borrow_set: BorrowSet<'tcx>,
    #[cfg(test)]
    captured_on: std::thread::ThreadId,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
struct ContextKey {
    global: usize,
    session: usize,
}

impl ContextKey {
    fn of(tcx: TyCtxt<'_>) -> Self {
        Self {
            global: std::ptr::from_ref(*tcx) as usize,
            session: std::ptr::from_ref(tcx.sess) as usize,
        }
    }
}

struct SessionBodies {
    generation: u64,
    bodies: HashMap<LocalDefId, Arc<RetainedBorrowckBody<'static>>>,
}

#[derive(Default)]
struct Registry {
    generation: u64,
    sessions: HashMap<ContextKey, SessionBodies>,
}

// The projected fields implement ordinary Send + Sync on the compiler SDK;
// no thread-safety implementation or dynamic-mode assumption is supplied here.
static REGISTRY: LazyLock<Mutex<Registry>> = LazyLock::new(|| Mutex::new(Registry::default()));

fn registry() -> MutexGuard<'static, Registry> {
    // A compiler panic must not leave an unusable retention registry behind.
    REGISTRY
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

/// Registers capture before analysis and releases only this context's entries
/// before its arenas disappear. The lifetime prevents keeping the guard past tcx.
/// Multiple live contexts are distinct, while reentering one context is refused.
struct MirSessionGuard<'tcx> {
    key: ContextKey,
    generation: u64,
    context: PhantomData<TyCtxt<'tcx>>,
}

impl<'tcx> MirSessionGuard<'tcx> {
    fn new(tcx: TyCtxt<'tcx>) -> Self {
        let key = ContextKey::of(tcx);
        let mut registry = registry();
        assert!(
            !registry.sessions.contains_key(&key),
            "MIR context already registered"
        );
        registry.generation = registry
            .generation
            .checked_add(1)
            .expect("MIR session generation exhausted");
        let generation = registry.generation;
        registry.sessions.insert(
            key,
            SessionBodies {
                generation,
                bodies: HashMap::new(),
            },
        );
        Self {
            key,
            generation,
            context: PhantomData,
        }
    }
}

impl Drop for MirSessionGuard<'_> {
    fn drop(&mut self) {
        let mut registry = registry();
        if registry
            .sessions
            .get(&self.key)
            .is_some_and(|session| session.generation == self.generation)
        {
            registry.sessions.remove(&self.key);
        }
    }
}

/// Clone an owned handle under the registry lock, then release it before any
/// consumer can run compiler queries. Rehashing and cleanup cannot move its body.
pub(crate) fn try_get_body_with_context<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> Option<Arc<RetainedBorrowckBody<'tcx>>> {
    let registry = registry();
    let session = registry.sessions.get(&ContextKey::of(tcx))?;
    let body = Arc::clone(session.bodies.get(&def_id)?);
    // SAFETY: the exact GlobalCtxt and Session are still registered by a guard
    // whose lifetime is bounded by this tcx. The stored type erases only that
    // arena lifetime; the returned owned Arc restores the caller's actual tcx
    // lifetime. No reference into the hash map escapes, and each Arc owns its
    // body even if the guard subsequently drops or another body is inserted.
    Some(unsafe {
        std::mem::transmute::<Arc<RetainedBorrowckBody<'static>>, Arc<RetainedBorrowckBody<'tcx>>>(
            body,
        )
    })
}

/// Capture once while mir_borrowck still owns the pre-steal body. Nested bodies
/// retain the same regenerated region identifiers as their own BorrowSet.
pub(crate) fn copy_mir_bodies<'tcx>(tcx: TyCtxt<'tcx>, def_id: LocalDefId) {
    let key = ContextKey::of(tcx);
    let generation = {
        let registry = registry();
        let Some(session) = registry.sessions.get(&key) else {
            return;
        };
        session.generation
    };
    let bodies = rustc_borrowck::consumers::get_bodies_with_borrowck_facts(
        tcx,
        def_id,
        ConsumerOptions::RegionInferenceContext,
    );
    for (def_id, with_facts) in bodies {
        let BodyWithBorrowckFacts {
            body, borrow_set, ..
        } = with_facts;
        // The unused Rc-bearing fields are dropped on this producer thread.
        let retained = Arc::new(RetainedBorrowckBody {
            origin: key,
            body,
            borrow_set,
            #[cfg(test)]
            captured_on: std::thread::current().id(),
        });
        insert_retained(tcx, generation, def_id, retained);
    }
}

fn insert_retained<'tcx>(
    tcx: TyCtxt<'tcx>,
    generation: u64,
    def_id: LocalDefId,
    retained: Arc<RetainedBorrowckBody<'tcx>>,
) -> bool {
    let key = ContextKey::of(tcx);
    if retained.origin != key || retained.body.source.def_id().as_local() != Some(def_id) {
        return false;
    }
    let mut registry = registry();
    let Some(session) = registry
        .sessions
        .get_mut(&key)
        .filter(|session| session.generation == generation)
    else {
        return false;
    };
    // SAFETY: the exact origin and still-live registration were checked while
    // holding the insertion lock. Its hidden guard drops every registry Arc
    // before tcx's arenas end; external owned handles carry the actual lifetime.
    // Only the ordinary Send + Sync projection is transported across workers.
    let retained = unsafe {
        std::mem::transmute::<Arc<RetainedBorrowckBody<'tcx>>, Arc<RetainedBorrowckBody<'static>>>(
            retained,
        )
    };
    session.bodies.entry(def_id).or_insert(retained);
    true
}

/// Keep the registration guard private so a safe caller cannot forget it and
/// leave erased arena references alive beyond the compiler context.
pub(crate) fn with_mir_session<'tcx, R>(tcx: TyCtxt<'tcx>, f: impl FnOnce() -> R) -> R {
    let _guard = MirSessionGuard::new(tcx);
    f()
}

#[cfg(test)]
mod tests;
