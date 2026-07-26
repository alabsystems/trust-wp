// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

use std::{
    fs, io,
    path::{Path, PathBuf},
    time::SystemTime,
};

pub(super) fn trust_wp_rustc_needs_build(binary_path: &Path) -> io::Result<bool> {
    let source_roots = trust_wp_rustc_source_roots();
    binary_is_missing_or_stale(binary_path, &source_roots)
}

fn trust_wp_rustc_source_roots() -> Vec<PathBuf> {
    let root = super::workspace_root();
    vec![
        root.join("Cargo.toml"),
        root.join("Cargo.lock"),
        root.join("crates").join("trust-wp"),
        root.join("crates").join("trust-wp-core"),
        root.join("crates").join("trust-wp-driver"),
        root.join("crates").join("trust-wp-macros"),
        root.join("crates").join("trust-wp-std"),
        root.join("crates").join("trust-wp-ay"),
    ]
}

fn binary_is_missing_or_stale(binary_path: &Path, source_roots: &[PathBuf]) -> io::Result<bool> {
    let binary_mtime = match fs::metadata(binary_path) {
        Ok(metadata) => metadata.modified()?,
        Err(err) if err.kind() == io::ErrorKind::NotFound => return Ok(true),
        Err(err) => return Err(err),
    };

    for root in source_roots {
        if !root.exists() {
            continue;
        }
        let source_mtime = latest_mtime(root)?;
        if source_mtime > binary_mtime {
            return Ok(true);
        }
    }

    Ok(false)
}

fn latest_mtime(path: &Path) -> io::Result<SystemTime> {
    let metadata = fs::metadata(path)?;
    let mut latest = metadata.modified()?;
    if metadata.is_dir() {
        for entry in fs::read_dir(path)? {
            let entry = entry?;
            let entry_latest = latest_mtime(&entry.path())?;
            if entry_latest > latest {
                latest = entry_latest;
            }
        }
    }
    Ok(latest)
}

#[cfg(test)]
mod tests {
    use tempfile::TempDir;

    use super::*;

    #[test]
    fn binary_is_missing_or_stale_true_when_binary_missing() {
        let temp = TempDir::new().unwrap();
        let source = temp.path().join("source.rs");
        fs::write(&source, "// source").unwrap();

        let stale = binary_is_missing_or_stale(
            &temp.path().join("missing-bin"),
            std::slice::from_ref(&source),
        )
        .unwrap();
        assert!(stale, "missing binary should require rebuild");
    }

    #[test]
    fn binary_is_missing_or_stale_true_when_source_is_newer() {
        let temp = TempDir::new().unwrap();
        let binary = temp.path().join("trust-wp-rustc");
        let source = temp.path().join("source.rs");

        fs::write(&binary, "binary").unwrap();
        std::thread::sleep(std::time::Duration::from_millis(20));
        fs::write(&source, "// newer source").unwrap();

        let stale = binary_is_missing_or_stale(&binary, std::slice::from_ref(&source)).unwrap();
        assert!(stale, "newer source should mark binary stale");
    }

    #[test]
    fn binary_is_missing_or_stale_false_when_binary_is_newer() {
        let temp = TempDir::new().unwrap();
        let binary = temp.path().join("trust-wp-rustc");
        let source = temp.path().join("source.rs");

        fs::write(&source, "// source").unwrap();
        std::thread::sleep(std::time::Duration::from_millis(20));
        fs::write(&binary, "binary").unwrap();

        let stale = binary_is_missing_or_stale(&binary, std::slice::from_ref(&source)).unwrap();
        assert!(!stale, "newer binary should not rebuild");
    }
}
