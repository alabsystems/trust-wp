// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! In-process rustc harness for the logic-identity decision tests.
//!
//! The decisions under test (`impl_self_may_apply`, `impl_self_covers_all`,
//! `peel_transparent_boxes`, the match-arm / `let` type carry and
//! `body_local_type`) all read real `rustc_middle` types, so a unit test of
//! one is a real compilation of a few lines of Rust plus a direct call to the
//! decision. Everything runs inside `after_analysis`, where the `TyCtxt` and
//! the thread-local member->`DefId` map both exist.

use std::{
    fs,
    sync::{Mutex, MutexGuard, PoisonError},
};

use rustc_driver::{run_compiler, Callbacks, Compilation};
use rustc_hir::def_id::DefId;
use rustc_interface::interface::Compiler;
use rustc_middle::ty::{Ty, TyCtxt};
use trust_wp_core::logic::identity::{
    logic_fn_identity_registry, LogicFnFamilyMember, LogicFnIdentityRegistry,
};

/// The logic-function identity REGISTRY is process-global (the encoder shares
/// it), while the member->`DefId` map is thread-local. Two probes installing
/// registries at once would hand one of them the other's families, so probes
/// run one at a time. `families_for` additionally checks the registry it reads
/// is its own, so a race with some other test's compilation fails loudly
/// instead of quietly testing the wrong crate.
static PROBE_LOCK: Mutex<()> = Mutex::new(());

/// Hold the registry for a test that runs the identity assignment outside
/// `probe` and reads the result: without it a concurrent probe replaces the
/// registry between the assignment and the resolution that reads it, and a
/// call resolved against another crate's families is refused.
pub(crate) fn registry_guard() -> MutexGuard<'static, ()> {
    PROBE_LOCK.lock().unwrap_or_else(PoisonError::into_inner)
}

struct ProbeCallbacks<F, R> {
    probe: Option<F>,
    out: Option<R>,
}

impl<F, R> Callbacks for ProbeCallbacks<F, R>
where
    F: for<'tcx> FnOnce(TyCtxt<'tcx>) -> R + Send,
    R: Send,
{
    #[allow(clippy::elidable_lifetime_names)]
    fn after_analysis<'tcx>(&mut self, _compiler: &Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let probe = self.probe.take().expect("probe closure runs exactly once");
        self.out = Some(probe(tcx));
        Compilation::Stop
    }
}

/// Compile `source` as a library crate named `crate_name` and run `probe`
/// against its `TyCtxt`.
pub(crate) fn probe<R: Send>(
    crate_name: &str,
    source: &str,
    probe: impl for<'tcx> FnOnce(TyCtxt<'tcx>) -> R + Send,
) -> R {
    let _guard = PROBE_LOCK.lock().unwrap_or_else(PoisonError::into_inner);

    let temp_dir = std::env::temp_dir().join(format!(
        "trust_wp_logic_identity_probe_{}_{crate_name}",
        std::process::id()
    ));
    fs::create_dir_all(&temp_dir).expect("create logic-identity probe temp dir");
    let source_path = temp_dir.join("test.rs");
    fs::write(&source_path, source).expect("write logic-identity probe source");

    let args = vec![
        "rustc".to_string(),
        source_path.to_string_lossy().into_owned(),
        "--crate-name".to_string(),
        crate_name.to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--edition=2021".to_string(),
        "-A".to_string(),
        "warnings".to_string(),
        "--out-dir".to_string(),
        temp_dir.to_string_lossy().into_owned(),
    ];

    let mut callbacks = ProbeCallbacks {
        probe: Some(probe),
        out: None,
    };
    run_compiler(&args, &mut callbacks);

    let _ = fs::remove_file(&source_path);
    let _ = fs::remove_dir_all(&temp_dir);

    callbacks
        .out
        .expect("after_analysis should have run the probe")
}

/// Run the real identity assignment over the crate and hand back the collision
/// family sharing `short_name`, cloned out of the installed registry.
///
/// Panics if the registry that comes back is not this crate's: that is the
/// process-global registry having been replaced by a concurrent compilation,
/// and every assertion after it would be about someone else's crate.
pub(crate) fn families_for(
    tcx: TyCtxt<'_>,
    crate_name: &str,
    short_name: &str,
) -> Vec<LogicFnFamilyMember> {
    let _defs = super::extract_logic_fn_defs(tcx);
    let registry: std::sync::Arc<LogicFnIdentityRegistry> =
        logic_fn_identity_registry().expect("identity assignment installs a registry");
    let family: Vec<LogicFnFamilyMember> = registry
        .family(short_name)
        .unwrap_or_else(|| panic!("no logic-fn family named `{short_name}`"))
        .to_vec();
    for member in &family {
        assert!(
            member.full_path.starts_with(crate_name),
            "registry raced: family `{short_name}` carries `{}`, which is not from `{crate_name}`",
            member.full_path
        );
    }
    family
}

/// The one member of `family` whose crate-qualified path ends with `suffix`.
pub(crate) fn member<'a>(
    family: &'a [LogicFnFamilyMember],
    suffix: &str,
) -> &'a LogicFnFamilyMember {
    let hits: Vec<&LogicFnFamilyMember> = family
        .iter()
        .filter(|member| member.full_path.ends_with(suffix))
        .collect();
    assert_eq!(
        hits.len(),
        1,
        "expected exactly one family member ending in `{suffix}`, got {:?}",
        family
            .iter()
            .map(|m| m.full_path.as_str())
            .collect::<Vec<_>>()
    );
    hits[0]
}

/// The `DefId` of the one item whose def path ends with `suffix`.
pub(crate) fn def_id_of(tcx: TyCtxt<'_>, suffix: &str) -> DefId {
    let hits: Vec<DefId> = tcx
        .iter_local_def_id()
        .map(rustc_hir::def_id::LocalDefId::to_def_id)
        .filter(|def_id| tcx.def_path_str(*def_id).ends_with(suffix))
        .collect();
    assert_eq!(
        hits.len(),
        1,
        "expected exactly one item ending in `{suffix}`, got {:?}",
        hits.iter()
            .map(|id| tcx.def_path_str(*id))
            .collect::<Vec<_>>()
    );
    hits[0]
}

/// The type of the first parameter of the function whose def path ends with
/// `suffix`, dereferenced and region-erased — the shape a receiver reaches the
/// decisions in.
pub(crate) fn first_param_ty<'tcx>(tcx: TyCtxt<'tcx>, suffix: &str) -> Ty<'tcx> {
    let def_id = def_id_of(tcx, suffix);
    let sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
    let ty = *sig
        .inputs()
        .first()
        .unwrap_or_else(|| panic!("`{suffix}` should take a parameter"));
    tcx.erase_and_anonymize_regions(ty.peel_refs())
}
