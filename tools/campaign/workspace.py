"""One git worktree per task, warm from the start.

The worktree is created from the task's base revision under
`.campaign/worktrees/<task>`, then every `.lake` directory of a warm checkout
is cloned into it: on APFS `cp -c` clones a 400 MB build in a tenth of a
second, on Linux `--reflink=auto` does the same on btrfs/xfs and copies
elsewhere. Lake then rebuilds only what the task changes."""

from __future__ import annotations

from pathlib import Path
import platform
import shutil
import subprocess

LAKE_DIRS = ("near-lean/.lake", "near-lean/*/.lake", "contracts/*/verification/.lake")


def git(path: Path, *args: str, check: bool = True) -> subprocess.CompletedProcess:
    return subprocess.run(["git", "-C", str(path), *args], capture_output=True, text=True, check=check)


def repo_root(start: Path) -> Path:
    return Path(git(start, "rev-parse", "--show-toplevel").stdout.strip())


def main_checkout(start: Path) -> Path:
    """The checkout whose `.git` is the real one (the worktrees share it)."""
    common = Path(git(start, "rev-parse", "--git-common-dir").stdout.strip())
    if not common.is_absolute():
        common = (start / common).resolve()
    return common.parent


def clone_tree(src: Path, dst: Path) -> None:
    dst.parent.mkdir(parents=True, exist_ok=True)
    if platform.system() == "Darwin":
        subprocess.run(["cp", "-Rc", str(src), str(dst)], check=True)
    else:
        subprocess.run(["cp", "-R", "--reflink=auto", str(src), str(dst)], check=True)


def warm(worktree: Path, source: Path) -> list[str]:
    """Clone every built `.lake` of `source` that `worktree` lacks."""
    cloned = []
    for pattern in LAKE_DIRS:
        for src in sorted(source.glob(pattern)):
            relative = src.relative_to(source)
            dst = worktree / relative
            if src.is_dir() and not dst.exists():
                clone_tree(src, dst)
                cloned.append(str(relative))
    return cloned


def create(root: Path, task_id: str, base: str, warm_from: Path | None = None) -> Path:
    """A fresh worktree on branch `campaign/<task>` at `base`, warmed."""
    path = root / ".campaign/worktrees" / task_id
    if path.exists():
        remove(root, path)
    git(root, "branch", "-D", f"campaign/{task_id}", check=False)
    path.parent.mkdir(parents=True, exist_ok=True)
    git(root, "worktree", "add", "-b", f"campaign/{task_id}", str(path), base)
    warm(path, warm_from or main_checkout(root))
    return path


def remove(root: Path, path: Path) -> None:
    git(root, "worktree", "remove", "--force", str(path), check=False)
    if path.exists():
        shutil.rmtree(path, ignore_errors=True)
    git(root, "worktree", "prune", check=False)


def changed_files(path: Path) -> list[str]:
    """Tracked changes and new files, relative to the worktree."""
    out = git(path, "status", "--porcelain", "--untracked-files=all").stdout
    files = []
    for line in out.splitlines():
        name = line[3:]
        if " -> " in name:
            name = name.split(" -> ", 1)[1]
        files.append(name.strip())
    return files


def commit_all(path: Path, message: str) -> str:
    """Commit everything; a task that changes nothing (a report) gets an empty commit,
    so every accepted task has one."""
    git(path, "add", "-A")
    git(path, "-c", "user.name=campaign", "-c", "user.email=campaign@local",
        "commit", "-q", "--allow-empty", "-m", message)
    return git(path, "rev-parse", "HEAD").stdout.strip()


def run_checks(path: Path, package: str, commands: list[str], timeout: float) -> tuple[bool, str]:
    """Each command in the package directory, in order; stop at the first failure."""
    log = []
    cwd = path / package
    for command in commands:
        log.append(f"$ {command}")
        try:
            run = subprocess.run(command, shell=True, cwd=cwd, capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired:
            log.append(f"timeout after {timeout:.0f}s")
            return False, "\n".join(log)
        output = (run.stdout + run.stderr).strip()
        if output:
            log.append("\n".join(output.splitlines()[-60:]))
        if run.returncode != 0:
            log.append(f"exit {run.returncode}")
            return False, "\n".join(log)
    return True, "\n".join(log)
