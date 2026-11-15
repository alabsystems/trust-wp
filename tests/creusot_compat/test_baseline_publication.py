"""A committed baseline census must not invalidate its unchanged source snapshot."""
# Copyright 2026 Andrew Yates
# Licensed under the Apache License, Version 2.0

from __future__ import annotations

import hashlib
import json
import subprocess
from pathlib import Path

import pytest

from tests.creusot_compat import harness, harness_cli, harness_provenance, harness_targets


CANONICAL_PATHS = (
    "tests/creusot_compat/results.json",
    "tests/creusot_compat/results-should-fail.json",
    "tests/creusot_compat/results-examples.json",
)
LANES = ("should_succeed", "should_fail", "examples")


def _git(repo: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", "-C", str(repo), *args], text=True, stderr=subprocess.DEVNULL
    ).strip()


@pytest.fixture
def baseline_repo(tmp_path):
    _git(tmp_path, "init", "-q")
    _git(tmp_path, "config", "user.name", "Baseline Test")
    _git(tmp_path, "config", "user.email", "baseline@test.invalid")
    (tmp_path / "source.rs").write_text("pub fn identity(n: i32) -> i32 { n }\n")
    for path in CANONICAL_PATHS:
        output = tmp_path / path
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text("{}\n")
    _git(tmp_path, "add", ".")
    _git(tmp_path, "commit", "-q", "-m", "initial source")
    _git(tmp_path, "commit", "--allow-empty", "-q", "-m", "source snapshot")
    return tmp_path, _git(tmp_path, "rev-parse", "HEAD")


def _publish(repo: Path, source: str, *, extra_path: str | None = None):
    for path in CANONICAL_PATHS:
        (repo / path).write_text(json.dumps({"metadata": {"git_commit": source}}) + "\n")
    if extra_path:
        path = repo / extra_path
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text("changed verification input\n")
    _git(repo, "add", ".")
    _git(repo, "commit", "-q", "-m", "publish generated census")


def _freshness(repo: Path, source: str | None = None):
    return harness.check_baseline_freshness(
        repo,
        max_age_commits=0,
        commit_overrides={lane: source for lane in LANES} if source else None,
    )


def test_direct_baseline_publication_keeps_honest_source_commit_fresh(baseline_repo, capsys):
    repo, source = baseline_repo
    fingerprint_before = harness_targets._git_source_state(repo)
    _publish(repo, source)
    original_outputs = {path: (repo / path).read_bytes() for path in CANONICAL_PATHS}

    freshness = _freshness(repo)

    assert freshness["status"] == "fresh"
    for lane in freshness["lanes"].values():
        assert lane["git_commit"] == source
        assert lane["resolved_commit"] == source
        assert lane["evaluated_head"] == _git(repo, "rev-parse", "HEAD")
        assert lane["is_ancestor"] is True
        assert lane["age_commits"] == 1
        assert lane["source_equivalent_to_head"] is True
        assert set(lane["publication_changed_paths"]) == set(CANONICAL_PATHS)
    assert {path: (repo / path).read_bytes() for path in CANONICAL_PATHS} == original_outputs
    assert harness._commit_distance_to_head(repo, source) == 1
    assert harness_targets._git_source_state(repo) != fingerprint_before

    harness_cli._print_baseline_freshness_report(freshness, 0)
    output = capsys.readouterr().out
    assert "1 commits behind HEAD" in output
    assert "source unchanged across the direct canonical-baseline publication commit" in output


@pytest.mark.parametrize("path", CANONICAL_PATHS)
def test_each_exact_canonical_path_can_be_published(baseline_repo, path):
    repo, source = baseline_repo
    (repo / path).write_text("generated census\n")
    _git(repo, "add", ".")
    _git(repo, "commit", "-q", "-m", "publish one census")
    relation = harness_provenance._baseline_commit_relation(repo, source)
    assert relation["is_ancestor"] is True
    assert relation["age_commits"] == 1
    assert relation["source_equivalent_to_head"] is True
    assert relation["publication_changed_paths"] == [path]


@pytest.mark.parametrize(
    "path",
    [
        "source.rs",
        "crates/trust-wp-driver/src/rustc_driver.rs",
        "tests/creusot_compat/harness.py",
        "Cargo.toml",
        "Cargo.lock",
        ".cargo/config.toml",
        "tests/creusot_compat/REFERENCE.pin",
        "docs/DECISIONS.md",
        "reports/census.json",
        "tests/creusot_compat/results-partial.json",
    ],
)
def test_publication_with_any_other_changed_path_is_stale(baseline_repo, path):
    repo, source = baseline_repo
    _publish(repo, source, extra_path=path)
    freshness = _freshness(repo)
    assert freshness["status"] == "stale"
    for lane in freshness["lanes"].values():
        assert lane["is_ancestor"] is True
        assert lane["age_commits"] == 1
        assert lane["source_equivalent_to_head"] is False
        assert path in lane["publication_changed_paths"]


def test_multi_commit_publication_does_not_extend_the_exception(baseline_repo):
    repo, source = baseline_repo
    _publish(repo, source)
    (repo / CANONICAL_PATHS[0]).write_text("generated follow-up census\n")
    _git(repo, "add", ".")
    _git(repo, "commit", "-q", "-m", "another publication")
    freshness = _freshness(repo, source)
    assert freshness["status"] == "stale"
    assert freshness["lanes"]["should_succeed"]["age_commits"] == 2


def test_empty_commit_is_not_a_baseline_publication(baseline_repo):
    repo, source = baseline_repo
    _git(repo, "commit", "--allow-empty", "-q", "-m", "unrelated empty commit")
    freshness = _freshness(repo, source)
    assert freshness["status"] == "stale"
    assert freshness["lanes"]["should_succeed"]["publication_changed_paths"] == []


def test_merge_cannot_be_treated_as_direct_publication(baseline_repo):
    repo, source = baseline_repo
    ancestor = _git(repo, "rev-parse", "HEAD^")
    _publish(repo, source)
    tree = _git(repo, "rev-parse", "HEAD^{tree}")
    merge = _git(repo, "commit-tree", tree, "-p", source, "-p", ancestor, "-m", "merge census")
    _git(repo, "checkout", "-q", "--detach", merge)
    assert harness._commit_distance_to_head(repo, source) == 1
    freshness = _freshness(repo)
    assert freshness["status"] == "stale"
    assert "single-parent" in freshness["lanes"]["should_succeed"]["reason"]


@pytest.mark.parametrize("kind", ["future", "unrelated", "missing", "branch"])
def test_baseline_commit_must_exist_and_be_an_immutable_ancestor(baseline_repo, kind):
    repo, source = baseline_repo
    tree = _git(repo, "rev-parse", "HEAD^{tree}")
    if kind == "future":
        commit = _git(repo, "commit-tree", tree, "-p", source, "-m", "future census")
        assert harness._commit_distance_to_head(repo, commit) == 0
    elif kind == "unrelated":
        commit = _git(repo, "commit-tree", tree, "-m", "unrelated history")
    elif kind == "missing":
        commit = "0" * 40
    else:
        _git(repo, "branch", "moving-baseline", source)
        commit = "moving-baseline"
    freshness = _freshness(repo, commit)
    assert freshness["status"] == "invalid"
    for lane in freshness["lanes"].values():
        assert lane["is_ancestor"] is False
        assert lane["source_equivalent_to_head"] is False
        assert lane["age_commits"] is None


@pytest.mark.parametrize("prefix_len", [7, 9, 40])
def test_short_unambiguous_ancestor_still_resolves(baseline_repo, prefix_len):
    repo, source = baseline_repo
    _publish(repo, source)
    freshness = _freshness(repo, source[:prefix_len])
    assert freshness["status"] == "fresh"
    assert freshness["lanes"]["should_succeed"]["resolved_commit"] == source


@pytest.mark.parametrize("ref_len", [7, 39])
def test_hex_named_moving_ref_is_not_an_immutable_object_prefix(baseline_repo, ref_len):
    repo, source = baseline_repo
    ref = "d" * ref_len if not source.startswith("d" * ref_len) else "e" * ref_len
    _git(repo, "branch", ref, source)
    assert _git(repo, "rev-parse", "--verify", ref + "^{commit}") == source
    assert _git(repo, "rev-parse", "--disambiguate=" + ref) == ""
    freshness = _freshness(repo, ref)
    assert freshness["status"] == "invalid"
    assert freshness["lanes"]["should_succeed"]["is_ancestor"] is False


def test_hex_named_ref_cannot_override_a_real_object_prefix(baseline_repo):
    repo, source = baseline_repo
    _git(repo, "commit", "--allow-empty", "-q", "-m", "later source snapshot")
    later = _git(repo, "rev-parse", "HEAD")
    prefix = source[:9]
    _git(repo, "branch", prefix, later)
    assert _git(repo, "rev-parse", "--disambiguate=" + prefix) == source
    assert _git(repo, "rev-parse", "--verify", prefix + "^{commit}") == later
    freshness = _freshness(repo, prefix)
    assert freshness["status"] == "invalid"
    assert "does not bind" in freshness["lanes"]["should_succeed"]["reason"]


def test_ref_cannot_disambiguate_colliding_commit_object_prefixes(baseline_repo):
    repo, source = baseline_repo
    tree = _git(repo, "rev-parse", "HEAD^{tree}")
    header = (
        f"tree {tree}\nparent {source}\n"
        "author Baseline Test <baseline@test.invalid> 1000000000 +0000\n"
        "committer Baseline Test <baseline@test.invalid> 1000000000 +0000\n\n"
    )
    seen = {}
    # Find an abbreviation collision without creating thousands of Git objects.
    for nonce in range(200000):
        payload = (header + f"candidate {nonce}\n").encode()
        digest = hashlib.sha1(b"commit " + str(len(payload)).encode() + b"\0" + payload).hexdigest()
        prefix = digest[:7]
        if prefix in seen:
            payloads = (seen[prefix], payload)
            break
        seen[prefix] = payload
    else:
        pytest.fail("could not construct an abbreviated commit collision")
    commits = [
        subprocess.check_output(
            ["git", "-C", str(repo), "hash-object", "-t", "commit", "-w", "--stdin"],
            input=payload,
        ).decode().strip()
        for payload in payloads
    ]
    assert commits[0] != commits[1]
    assert all(commit.startswith(prefix) for commit in commits)
    _git(repo, "checkout", "-q", "--detach", commits[0])
    _git(repo, "branch", prefix, commits[0])
    assert _git(repo, "rev-parse", "--verify", prefix + "^{commit}") == commits[0]
    assert set(_git(repo, "rev-parse", "--disambiguate=" + prefix).split()) == set(commits)
    freshness = _freshness(repo, prefix)
    assert freshness["status"] == "invalid"
    assert "unambiguous" in freshness["lanes"]["should_succeed"]["reason"]


def test_dirty_metadata_is_not_rehabilitated_by_publication(baseline_repo):
    repo, source = baseline_repo
    _publish(repo, source)
    freshness = _freshness(repo, source + "-dirty")
    assert freshness["status"] == "stale"
    assert freshness["lanes"]["should_succeed"]["age_commits"] is None


def test_worktree_cleanliness_remains_the_separate_review_boundary(baseline_repo):
    repo, source = baseline_repo
    _publish(repo, source)
    (repo / "source.rs").write_text("uncommitted verification change\n")
    assert _freshness(repo)["status"] == "fresh"
    assert _git(repo, "status", "--porcelain")

    review = (Path(__file__).resolve().parents[2] / "scripts/creusot_replacement_review.sh").read_text()
    start = review.index("repo_dirty_count() {")
    end = review.index("\nresolve_commit() {", start)
    result = subprocess.run(
        [
            "bash", "-c",
            'set -euo pipefail\nfail() { echo "$*" >&2; exit 1; }\n'
            + review[start:end]
            + '\nrequire_clean_repo "$1" trust-wp\n',
            "review-cleanliness", str(repo),
        ],
        capture_output=True, text=True,
    )
    assert result.returncode != 0
    assert "uncommitted path" in result.stderr


def test_publication_does_not_change_nonzero_age_budget_semantics(baseline_repo):
    repo, source = baseline_repo
    _publish(repo, source, extra_path="source.rs")
    freshness = harness.check_baseline_freshness(repo, max_age_commits=1)
    assert freshness["status"] == "fresh"
    assert freshness["lanes"]["should_succeed"]["source_equivalent_to_head"] is False

