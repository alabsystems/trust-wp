// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! The compiled dependencies of a test executable, for a rustc the test starts.
//!
//! Cargo used to write every unit of a profile to `<profile>/deps/`. Its
//! build-dir layout, always on since cargo 1.100, writes each unit to its own
//! `<profile>/build/<package>/<hash>/out/` and keeps no `deps/`. A test that
//! hands rustc its workspace's compiled crates reads both, so it works under
//! either cargo.

use std::{
    ffi::OsStr,
    fs,
    path::{Path, PathBuf},
    time::SystemTime,
};

/// The directories holding a profile's compiled units: `deps/` when it
/// exists, then each unit's `build/<package>/<hash>/out/`.
pub fn profile_unit_dirs(profile_dir: &Path) -> Vec<PathBuf> {
    let mut dirs = Vec::new();
    let deps = profile_dir.join("deps");
    if deps.is_dir() {
        dirs.push(deps);
    }
    let Ok(packages) = fs::read_dir(profile_dir.join("build")) else {
        return dirs;
    };
    let mut units: Vec<PathBuf> = packages
        .flatten()
        .filter_map(|package| fs::read_dir(package.path()).ok())
        .flat_map(|hashes| hashes.flatten().map(|hash| hash.path().join("out")))
        .filter(|out| out.is_dir())
        .collect();
    units.sort();
    dirs.extend(units);
    dirs
}

/// The profile directory the running executable was built into: the parent
/// of its `deps/` (the old layout) or of its `build/` (the build-dir layout).
///
/// # Panics
///
/// Panics when the executable sits under neither.
pub fn current_exe_profile_dir() -> PathBuf {
    let exe = std::env::current_exe().expect("current test executable path");
    exe.ancestors()
        .skip(1)
        .find(|dir| {
            matches!(
                dir.file_name().and_then(OsStr::to_str),
                Some("deps" | "build")
            )
        })
        .and_then(Path::parent)
        .unwrap_or_else(|| panic!("{} is not under a cargo profile directory", exe.display()))
        .to_path_buf()
}

/// The running executable's profile's compiled units, with the newest build
/// of a crate found by name.
pub struct UnitDirs {
    dirs: Vec<PathBuf>,
}

impl UnitDirs {
    /// The units of the profile the running executable was built into.
    pub fn of_current_exe() -> Self {
        Self {
            dirs: profile_unit_dirs(&current_exe_profile_dir()),
        }
    }

    /// The directories, in the order rustc is given them.
    pub fn dirs(&self) -> &[PathBuf] {
        &self.dirs
    }

    /// `-L dependency=<dir>` for every directory, so rustc resolves the
    /// crates an `--extern` artifact depends on.
    pub fn search_args(&self) -> Vec<String> {
        self.dirs
            .iter()
            .flat_map(|dir| ["-L".to_string(), format!("dependency={}", dir.display())])
            .collect()
    }

    /// The compiled `lib<crate_name>-<hash>.<ext>` with one of `extensions`
    /// that the newest build wrote: a linkable artifact before metadata, then
    /// the newest. Another hash is a build of other features or an older
    /// compiler, and rustc refuses it as "can't find crate".
    ///
    /// # Panics
    ///
    /// Panics when no unit holds one.
    pub fn artifact(&self, crate_name: &str, extensions: &[&str]) -> PathBuf {
        let prefix = format!("lib{crate_name}-");
        let mut candidates: Vec<PathBuf> = self
            .dirs
            .iter()
            .filter_map(|dir| fs::read_dir(dir).ok())
            .flat_map(|entries| entries.flatten().map(|entry| entry.path()))
            .filter(|path| {
                path.file_name()
                    .and_then(OsStr::to_str)
                    .is_some_and(|name| name.starts_with(&prefix))
                    && path
                        .extension()
                        .and_then(OsStr::to_str)
                        .is_some_and(|ext| extensions.contains(&ext))
                    && fs::metadata(path).is_ok_and(|meta| meta.len() > 0)
            })
            .collect();
        candidates.sort_by_key(|path| {
            let metadata_only = path.extension() == Some(OsStr::new("rmeta"));
            let mtime = fs::metadata(path)
                .and_then(|meta| meta.modified())
                .unwrap_or(SystemTime::UNIX_EPOCH);
            (metadata_only, std::cmp::Reverse(mtime))
        });
        candidates.into_iter().next().unwrap_or_else(|| {
            panic!(
                "missing dependency artifact for {crate_name} under {} unit directories",
                self.dirs.len()
            )
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn both_layouts_are_read_and_the_newest_linkable_build_wins() {
        let temp = tempfile::TempDir::new().unwrap();
        let profile = temp.path().join("debug");
        let old = profile.join("deps");
        let new_a = profile
            .join("build")
            .join("trust-wp")
            .join("a1")
            .join("out");
        let new_b = profile
            .join("build")
            .join("trust-wp")
            .join("b2")
            .join("out");
        // A build script's output dir of the old layout holds no units.
        let script = profile.join("build").join("ay-sys-c3").join("out");
        for dir in [&old, &new_a, &new_b, &script] {
            fs::create_dir_all(dir).unwrap();
        }
        let written = |path: PathBuf, bytes: &[u8], age_secs: u64| {
            fs::write(&path, bytes).unwrap();
            let mtime =
                SystemTime::UNIX_EPOCH + std::time::Duration::from_secs(1_000_000 - age_secs);
            fs::File::options()
                .write(true)
                .open(&path)
                .unwrap()
                .set_modified(mtime)
                .unwrap();
        };
        written(old.join("libtrust_wp-a0.rmeta"), b"m", 0);
        written(new_a.join("libtrust_wp-a1.rlib"), b"r", 20);
        written(new_b.join("libtrust_wp-b2.rlib"), b"r", 10);
        written(new_b.join("libtrust_wp-b2.rmeta"), b"", 0);

        let units = UnitDirs {
            dirs: profile_unit_dirs(&profile),
        };
        assert_eq!(units.dirs(), [old, new_a, new_b.clone()]);
        assert_eq!(
            units.artifact("trust_wp", &["rmeta", "rlib"]),
            new_b.join("libtrust_wp-b2.rlib")
        );
        assert_eq!(units.search_args().len(), 6);
    }
}
