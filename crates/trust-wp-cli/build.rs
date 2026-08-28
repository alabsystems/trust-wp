//! Stamp the commit this binary was built from into `--version`.
//!
//! `CARGO_PKG_VERSION` alone is not an identity. The workspace version moves
//! on a minor-bump cadence, so at any moment dozens of distinct builds all
//! call themselves the same number, and a bug report naming one of them can
//! not be traced to a tree. The repository's versioning policy already has a
//! slot for this — SemVer build metadata, `MAJOR.MINOR.0+g<short-sha>` — and
//! it is deliberately not the patch slot, because a hash there makes versions
//! sort backwards and Cargo reads later builds as downgrades.
//!
//! Absent git, this emits nothing and `--version` prints the bare version.
//! That is the correct outcome for a build from a published tarball, where
//! the version *is* the identity.

use std::{path::Path, process::Command};

fn main() {
    // Re-run when HEAD moves. Both files matter: `HEAD` changes on checkout,
    // and the ref it names changes on commit.
    let git_dir = Path::new("../../.git");
    if git_dir.join("HEAD").exists() {
        println!("cargo:rerun-if-changed=../../.git/HEAD");
        if let Ok(head) = std::fs::read_to_string(git_dir.join("HEAD")) {
            if let Some(reference) = head.strip_prefix("ref: ").map(str::trim) {
                println!("cargo:rerun-if-changed=../../.git/{reference}");
            }
        }
    }

    let Some(sha) = git(&["rev-parse", "--short=8", "HEAD"]) else {
        return;
    };
    // A dirty tree is not a commit, and saying so is the whole point: the
    // difference between "this is c1645cf" and "this is c1645cf plus
    // uncommitted edits" is the difference between a reproducible report and
    // a wild goose chase. Dots are legal in SemVer build metadata.
    let dirty =
        git(&["status", "--porcelain", "--untracked-files=no"]).is_some_and(|out| !out.is_empty());
    let suffix = if dirty { ".dirty" } else { "" };
    println!("cargo:rustc-env=TRUST_WP_BUILD=g{sha}{suffix}");

    // The manual page's date. Convention is the date the content last
    // changed, which is the commit date — not the build date, which would
    // make the same commit render a different page every time it is built.
    if let Some(date) = git(&["log", "-1", "--format=%cs"]) {
        println!("cargo:rustc-env=TRUST_WP_COMMIT_DATE={date}");
    }
}

/// Run a git command, or `None` if git is missing, fails, or we are not in a
/// repository. A build must never fail because of this file.
fn git(args: &[&str]) -> Option<String> {
    let out = Command::new("git").args(args).output().ok()?;
    if !out.status.success() {
        return None;
    }
    Some(String::from_utf8(out.stdout).ok()?.trim().to_string())
}
