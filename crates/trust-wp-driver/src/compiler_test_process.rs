// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fresh-process compiler tests preserve owned inherited resource custody.

use std::{
    os::fd::{AsRawFd, FromRawFd, OwnedFd},
    process::Command,
    sync::OnceLock,
};

use jobserver_utils::InheritedJobserver;

struct ChildCustody {
    scheduler: InheritedJobserver,
    sdk: Option<OwnedFd>,
}

static INHERITED: OnceLock<ChildCustody> = OnceLock::new();
const CHILD: &str = "TRUST_WP_ISOLATED_COMPILER_TEST";

/// Called only by the native test entry, immediately after compiler capture.
///
/// # Safety
/// Call exactly once on the single-threaded native entry path. No arbitrary
/// IO, callback, or descriptor close/reuse may precede this call.
/// The two fixed SDK/GNU importers retain originals and only duplicate owned
/// descriptions; their source slots remain open throughout both captures.
pub(crate) unsafe fn capture_child_custody() -> Result<(), String> {
    if INHERITED.get().is_some() {
        return Err("compiler test child custody already captured".to_string());
    }
    // SAFETY: the native entry enforces the startup ordering documented above.
    let inherited = unsafe { InheritedJobserver::from_env() }.map_err(|error| error.to_string())?;
    let advertised = [
        "CARGO_MAKEFLAGS",
        "MAKEFLAGS",
        "MFLAGS",
        "CARGO_JOBSERVER_HANDOFF",
    ]
    .iter()
    .any(|name| std::env::var_os(name).is_some());
    if advertised && !inherited.is_present() {
        return Err("compiler test child has no inherited GNU scheduler".to_string());
    }
    let sdk = std::env::var_os("ATERM_SDK_LEASE_V3")
        .map(|value| -> Result<OwnedFd, String> {
            let value = value.to_str().ok_or("SDK lease locator is not UTF-8")?;
            let raw: i32 = value
                .parse()
                .map_err(|_| "SDK lease locator is not a descriptor")?;
            if raw < 3 || raw.to_string() != value {
                return Err("SDK lease locator is not canonical".to_string());
            }
            // SAFETY: the fixed SDK82 sdk.rs::capture only F_DUPFD_CLOEXECs
            // this validated inherited source; it never owns or closes the
            // original slot. No other Rust owner exists at native entry, and
            // only the fixed non-closing importers ran since. Adopt that exact
            // source once and retain it through every child wait. Its numeric
            // slot is part of SDK Context equality, so it must not be remapped.
            Ok(unsafe { OwnedFd::from_raw_fd(raw) })
        })
        .transpose()?;
    INHERITED
        .set(ChildCustody {
            scheduler: inherited,
            sdk,
        })
        .map_err(|_| "compiler test child custody already captured".to_string())
}

/// rustc's threading mode is fixed once per process. Run explicit parallel
/// compiler cases in a fresh process without changing other fixtures' options.
pub(crate) fn run_isolated(name: &str, check: impl FnOnce()) {
    // module_path! includes the crate; libtest's exact names start at its modules.
    let name = name.split_once("::").expect("fully qualified test name").1;
    let completed = format!("TRUST_WP_COMPILER_TEST_COMPLETED:{name}");
    if std::env::var(CHILD).as_deref() == Ok(name) {
        check();
        eprintln!("{completed}");
        return;
    }
    let mut command = Command::new(std::env::current_exe().expect("test executable"));
    command
        .args(["--exact", name, "--nocapture"])
        .env(CHILD, name);
    let custody = INHERITED
        .get()
        .expect("native-entry child custody captured");
    custody.scheduler.configure(&mut command);
    if let Some(sdk) = &custody.sdk {
        // SDK82's explicit-inheritance primitive forwards the held original
        // slot and its original OFD. Context validation retains the same
        // numeric locator; no reopen, relock, or renumbering grants custody.
        trust_resource_controller::client::inherit_descriptions(&mut command, &[sdk.as_raw_fd()])
            .expect("owned original SDK lease forwarded");
        command.env("ATERM_SDK_LEASE_V3", sdk.as_raw_fd().to_string());
    } else {
        assert!(
            std::env::var_os("ATERM_SDK_LEASE_V3").is_none(),
            "SDK locator appeared after native-entry custody capture"
        );
    }
    let output = command
        .output()
        .expect("isolated compiler test child starts");
    let stderr = String::from_utf8_lossy(&output.stderr);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        output.status.success() && stderr.lines().any(|line| line == completed),
        "isolated compiler test {name} did not complete: status={}\nstdout={stdout}\nstderr={stderr}",
        output.status
    );
}
