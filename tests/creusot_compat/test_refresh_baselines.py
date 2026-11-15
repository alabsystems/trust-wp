"""Run refresh's real source admission before a sentinel lane collector."""

from __future__ import annotations

import shutil
import subprocess
from pathlib import Path

import pytest


SCRIPT = Path(__file__).resolve().parents[2] / "scripts" / "refresh-baselines.sh"


def git(root: Path, *args: str) -> str:
    return subprocess.check_output(
        ["git", "-C", str(root), *args], text=True, stderr=subprocess.DEVNULL
    ).strip()


def initialize(root: Path) -> str:
    root.mkdir(parents=True, exist_ok=True)
    git(root, "init", "-q")
    git(root, "config", "user.name", "Refresh Test")
    git(root, "config", "user.email", "refresh@test.invalid")
    (root / "source.txt").write_text("original source\n")
    git(root, "add", ".")
    git(root, "commit", "-q", "-m", "fixture source")
    return git(root, "rev-parse", "HEAD")


@pytest.fixture
def refresh_tree(tmp_path, request):
    project = tmp_path / "trust-wp"
    (project / "scripts").mkdir(parents=True)
    shutil.copyfile(SCRIPT, project / "scripts" / SCRIPT.name)
    harness = project / "tests" / "creusot_compat" / "harness.py"
    harness.parent.mkdir(parents=True)
    harness.write_text(
        "from pathlib import Path\n"
        "Path('collector-entered').write_text('admitted')\n"
        "raise SystemExit(27)\n"
    )
    initialize(project)
    seed = tmp_path / "seed"
    head = initialize(seed)
    references = [tmp_path / "ay", project / "reference" / "creusot"]
    for root in references:
        root.parent.mkdir(parents=True, exist_ok=True)
        if getattr(request, "param", True):
            git(seed, "worktree", "add", "--detach", str(root), head)
            assert (root / ".git").is_file()
        else:
            git(seed, "clone", "--quiet", "--no-hardlinks", str(seed), str(root))
            assert (root / ".git").is_dir()
    # Reference checkouts are verification inputs, not tracked project files.
    git_dir = Path(git(project, "rev-parse", "--absolute-git-dir"))
    (git_dir / "info" / "exclude").write_text("reference/\n")
    return project, references, head


def refresh(project: Path, head: str, *extra: str):
    return subprocess.run(
        [
            "bash", str(project / "scripts" / SCRIPT.name),
            "--expect-ay-ref", head, "--expect-creusot-ref", head, *extra,
        ],
        capture_output=True, text=True, check=False,
    )


@pytest.mark.parametrize("refresh_tree", [True, False], indirect=True)
def test_clean_references_reach_collection(refresh_tree):
    project, _, head = refresh_tree
    result = refresh(project, head)
    assert result.returncode == 27, result.stderr
    assert (project / "collector-entered").read_text() == "admitted"
    assert not (project / "tests" / "creusot_compat" / "results.json").exists()


@pytest.mark.parametrize("index", [0, 1])
def test_dirty_linked_reference_refuses_before_collection(refresh_tree, index):
    project, references, head = refresh_tree
    (references[index] / "source.txt").write_text("modified input\n")
    result = refresh(project, head)
    assert result.returncode == 3, result.stderr
    assert "worktree is dirty" in result.stderr
    assert not (project / "collector-entered").exists()


@pytest.mark.parametrize("option", ["--expect-ay-ref", "--expect-creusot-ref"])
def test_wrong_reference_pin_refuses_before_collection(refresh_tree, option):
    project, _, head = refresh_tree
    result = refresh(project, head, option, "0" * 40)
    assert result.returncode == 3, result.stderr
    assert "expected " + "0" * 40 in result.stderr
    assert not (project / "collector-entered").exists()


def test_reference_directory_cannot_borrow_ancestor_repository(refresh_tree):
    project, references, head = refresh_tree
    reference = references[1]
    git(reference, "worktree", "remove", str(reference))
    reference.mkdir()
    result = refresh(project, head)
    assert result.returncode == 3, result.stderr
    assert "reference/creusot is not a git checkout" in result.stderr
    assert not (project / "collector-entered").exists()
