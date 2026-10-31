"""Run campaign tasks: brief an agent in a warm worktree, accept only what the
task's checks pass, escalate through the profile's tiers, switch backends when
one is exhausted, and record every attempt.

    python3 tools/campaign_driver.py run [--profile P] [--parallel N] [--task ID ...]
    python3 tools/campaign_driver.py status | results | auth | new | merge

A task is `campaign/tasks/<id>.json`:

    {"id": "parser-leaf-12", "role": "prover", "kind": "lean-proof",
     "title": "f81 closing reserve", "brief": "campaign/briefs/parser-leaf-12.md",
     "package": "contracts/w-near/verification",
     "files": ["Bridge/Functions/SerdeClose.lean"],
     "context": ["Bridge/Functions/SerdeIgn.lean"],
     "check": ["lake build Bridge.Functions.SerdeClose",
               "python3 ../../../tools/axiom-audit.py . --no-build --report /tmp/a.json"],
     "base": "origin/main", "timeout_minutes": 90, "rounds": 3}

`files` (relative to `package`) are the only files the agent may change; a
task without `files` may change nothing (a report). `context` files are sent
read-only to API models. `check` runs in `package`; all must pass. Accepted
work is committed on branch `campaign/<id>`; `merge` folds accepted branches
into a target branch one at a time, re-running the checks."""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import json
from pathlib import Path
import sys
import threading

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from campaign import backends as backends_module, workspace  # noqa: E402
from campaign.config import ROLES, Config, ConfigError, ExhaustionState  # noqa: E402

RULES = """You are an agent of the safe-near verification campaign, working alone in an
isolated git worktree at {worktree} (branch campaign/{id}). Task {id}, role {role}: {title}.

Rules:
- Change only these files, relative to {package}: {files}. Any other change is rejected.
- Never weaken a statement, a contract, a pinned statement (STATEMENTS.md) or the model to
  make a proof go through. If the task is impossible as stated, say exactly why and stop.
- No `sorry`, `native_decide`, `bv_decide` or new axioms in what you deliver.
- Before finishing, run these checks from {package} and make every one pass:
{checks}
- Do not commit, push, or touch anything outside this worktree.
- End with a short report: what is done, what remains, and anything suspicious about the
  statement you were given (a hypothesis that may be unsatisfiable, a bound that looks false).
"""

API_FORMAT = """You have no tools. Answer with the complete new content of every file you change,
each in a block of exactly this form (path relative to {package}):

<<<FILE path/To/File.lean>>>
...whole file...
<<<END>>>

Change only the files you are allowed to change. The checks are run for you after your
answer; if they fail you get the log and may answer again."""

_results_lock = threading.Lock()


def load_tasks(root: Path, ids: list[str] | None = None) -> list[dict]:
    tasks = []
    for path in sorted((root / "campaign/tasks").glob("*.json")):
        task = json.loads(path.read_text())
        task.setdefault("id", path.stem)
        if ids and task["id"] not in ids:
            continue
        validate_task(task)
        tasks.append(task)
    missing = set(ids or []) - {t["id"] for t in tasks}
    if missing:
        raise ConfigError(f"unknown tasks: {', '.join(sorted(missing))}")
    return tasks


def validate_task(task: dict) -> None:
    for key in ("id", "role", "kind", "title", "package", "check"):
        if key not in task:
            raise ConfigError(f"task {task.get('id', '?')}: missing {key!r}")
    if task["role"] not in ROLES:
        raise ConfigError(f"task {task['id']}: unknown role {task['role']!r}")
    if not isinstance(task["check"], list) or not task["check"]:
        raise ConfigError(f"task {task['id']}: check must be a non-empty list")
    if "brief" not in task and "brief_text" not in task:
        raise ConfigError(f"task {task['id']}: needs brief or brief_text")


def brief_text(root: Path, task: dict) -> str:
    if "brief_text" in task:
        return task["brief_text"]
    return (root / task["brief"]).read_text()


def allowed_files(task: dict) -> list[str]:
    return [f"{task['package']}/{f}".replace("//", "/") for f in task.get("files", [])]


def messages_for(root: Path, task: dict, worktree: Path, agentic: bool, feedback: list[tuple[str, str]]) -> list[dict]:
    files = ", ".join(task.get("files", [])) or "none (this task changes nothing)"
    checks = "\n".join(f"    {c}" for c in task["check"])
    rules = RULES.format(worktree=worktree, id=task["id"], role=task["role"], title=task["title"],
                         package=task["package"], files=files, checks=checks)
    brief = brief_text(root, task)
    if agentic:
        messages = [{"role": "user", "content": rules + "\n" + brief}]
    else:
        parts = [brief, ""]
        for kind, names in (("You may change", task.get("files", [])), ("Read-only context", task.get("context", []))):
            for name in names:
                path = worktree / task["package"] / name
                body = path.read_text() if path.exists() else "(new file)"
                parts.append(f"{kind}: {name}\n```\n{body}\n```\n")
        parts.append("Checks run after your answer, from " + task["package"] + ":\n" + checks)
        messages = [{"role": "system", "content": rules + "\n" + API_FORMAT.format(package=task["package"])},
                    {"role": "user", "content": "\n".join(parts)}]
    for answer, log in feedback:
        messages.append({"role": "assistant", "content": answer})
        messages.append({"role": "user", "content": "The checks failed. Fix it; answer with corrected whole files "
                                                    "(or, if the statement is wrong, say so).\n\n" + log})
    return messages


def reset(worktree: Path) -> None:
    workspace.git(worktree, "reset", "-q", "--hard")
    workspace.git(worktree, "clean", "-qfd")


def record(root: Path, entry: dict) -> None:
    path = root / "campaign/results.jsonl"
    path.parent.mkdir(parents=True, exist_ok=True)
    with _results_lock, path.open("a") as handle:
        handle.write(json.dumps(entry, sort_keys=True) + "\n")


def _attempt(root, task, worktree, backend, tier, config, log) -> tuple[bool, str, dict]:
    """One attempt on one tier: run the agent (with repair rounds for API
    models), guard the files, run the checks. Returns (accepted, detail, outcome)."""
    timeout = float(task.get("timeout_minutes", 60)) * 60
    rounds = 1 if backend.agentic else int(task.get("rounds", 3))
    feedback: list[tuple[str, str]] = []
    outcome = backends_module.Outcome()
    for round_index in range(rounds):
        messages = messages_for(root, task, worktree, backend.agentic, feedback)
        outcome = backend.run(messages, worktree, tier.model, timeout)
        if not outcome.ok:
            return False, ("exhausted" if outcome.exhausted else "agent failed: " + outcome.log[-500:]), outcome
        if not backend.agentic:
            try:
                written = backends_module.apply_file_blocks(outcome.text, worktree / task["package"])
            except ValueError as error:
                return False, str(error), outcome
            if not written and task.get("files"):
                return False, "the answer contained no file block", outcome
        changed = workspace.changed_files(worktree)
        outside = sorted(set(changed) - set(allowed_files(task)))
        if outside:
            return False, "changed files outside the task: " + ", ".join(outside), outcome
        ok, check_log = workspace.run_checks(worktree, task["package"], task["check"], timeout)
        log(f"{task['id']}: {tier.label} round {round_index + 1}: checks {'passed' if ok else 'failed'}")
        if ok:
            return True, check_log, outcome
        feedback.append((outcome.text, check_log))
        if round_index + 1 < rounds:
            reset(worktree)
    return False, "checks failed:\n" + feedback[-1][1] if feedback else "no attempt", outcome


def run_task(root: Path, task: dict, config: Config, profile: str, backend_pool: dict,
             keep: bool = False, log=print, warm_from: Path | None = None) -> dict | None:
    """Run one task through the profile's tiers. Returns the accepted record, or None.
    The worktree is warmed from `warm_from`, by default the checkout running the driver."""
    exhaustion = ExhaustionState(root / "campaign/.state/exhausted.json", config.reset_hours)
    worktree = workspace.create(root, task["id"], task.get("base", "origin/main"), warm_from or root)
    accepted = None
    tried: set = set()
    try:
        while accepted is None:
            chain = [t for t in config.chain(task["role"], profile, exhaustion.active()) if t not in tried]
            if not chain:
                log(f"{task['id']}: no tier left")
                break
            tier = chain[0]
            tried.add(tier)
            backend = backend_pool[tier.backend]
            for attempt in range(1, tier.attempts + 1):
                started = datetime.now(timezone.utc)
                ok, detail, outcome = _attempt(root, task, worktree, backend, tier, config, log)
                entry = {"task": task["id"], "kind": task["kind"], "role": task["role"], "profile": profile,
                         "backend": tier.backend, "model": tier.model, "attempt": attempt, "accepted": ok,
                         "exhausted": outcome.exhausted, "seconds": round(outcome.seconds, 1),
                         "cost_usd": outcome.cost_usd, "usage": outcome.usage, "time": started.isoformat(),
                         "detail": detail[-2000:]}
                if ok:
                    sha = workspace.commit_all(worktree, f"{task['id']}: {task['title']}\n\n"
                                               f"Accepted from {tier.label} on attempt {attempt}.")
                    entry["commit"] = sha
                    entry["branch"] = f"campaign/{task['id']}"
                    entry["report"] = outcome.text[-4000:]
                    record(root, entry)
                    accepted = entry
                    log(f"{task['id']}: accepted from {tier.label} ({sha[:8]})")
                    break
                record(root, entry)
                if outcome.exhausted:
                    until = exhaustion.mark(tier.backend)
                    log(f"{task['id']}: {tier.backend} exhausted until {until:%H:%M %Z}; switching")
                    break
                log(f"{task['id']}: {tier.label} attempt {attempt} rejected: {detail.splitlines()[0] if detail else ''}")
                reset(worktree)
    finally:
        if not keep:
            workspace.remove(root, worktree)
    return accepted


def accepted_tasks(root: Path) -> dict[str, dict]:
    latest = {}
    path = root / "campaign/results.jsonl"
    if path.exists():
        for line in path.read_text().splitlines():
            if line.strip():
                entry = json.loads(line)
                if entry.get("accepted"):
                    latest[entry["task"]] = entry
    return latest


def cmd_run(args, root: Path) -> int:
    config = Config.load(args.config)
    profile = args.profile or config.default_profile
    if profile not in config.profiles:
        raise ConfigError(f"unknown profile {profile!r}")
    done = accepted_tasks(root)
    tasks = [t for t in load_tasks(root, args.task) if args.again or t["id"] not in done]
    if not tasks:
        print("nothing to run")
        return 0
    pool = {name: backends_module.make(name, spec) for name, spec in config.backends.items()}
    if args.dry_run:
        exhausted = ExhaustionState(root / "campaign/.state/exhausted.json").active()
        for task in tasks:
            chain = config.chain(task["role"], profile, exhausted)
            print(f"== {task['id']} ({task['role']}): " + " -> ".join(f"{t.label} x{t.attempts}" for t in chain))
            agentic = pool[chain[0].backend].agentic if chain else True
            for message in messages_for(root, task, root, agentic, []):
                print(f"--- {message['role']}\n{message['content']}")
        return 0
    print(f"profile {profile}: {len(tasks)} task(s), {args.parallel} in parallel")

    def guarded(task: dict) -> dict | None:
        """A driver error on one task is recorded and does not stop the others."""
        try:
            return run_task(root, task, config, profile, pool, args.keep, warm_from=args.warm_from)
        except Exception as error:  # noqa: BLE001 - whatever it is, the run continues
            record(root, {"task": task["id"], "kind": task["kind"], "role": task["role"], "profile": profile,
                          "backend": None, "model": None, "attempt": 0, "accepted": False, "exhausted": False,
                          "seconds": 0, "time": datetime.now(timezone.utc).isoformat(),
                          "detail": f"driver error: {type(error).__name__}: {error}"[-2000:]})
            print(f"{task['id']}: driver error: {type(error).__name__}: {error}")
            return None

    accepted = 0
    with ThreadPoolExecutor(max_workers=args.parallel) as executor:
        for result in executor.map(guarded, tasks):
            accepted += result is not None
    print(f"{accepted}/{len(tasks)} accepted")
    return 0 if accepted == len(tasks) else 1


def cmd_status(args, root: Path) -> int:
    done = accepted_tasks(root)
    for task in load_tasks(root):
        state = done.get(task["id"])
        mark = f"accepted {state['commit'][:8]} from {state['backend']}:{state['model'] or 'default'}" if state else "pending"
        print(f"{task['id']:32} {task['role']:11} {mark}")
    exhausted = ExhaustionState(root / "campaign/.state/exhausted.json").active()
    if exhausted:
        print("exhausted:", ", ".join(sorted(exhausted)))
    return 0


def summarize(root: Path) -> list[tuple[str, str, int, int, float, float]]:
    """(kind, backend:model, attempts, accepted, mean seconds, cost) per task kind and model."""
    rows: dict[tuple[str, str], list[dict]] = {}
    path = root / "campaign/results.jsonl"
    if path.exists():
        for line in path.read_text().splitlines():
            if line.strip():
                entry = json.loads(line)
                rows.setdefault((entry["kind"], f"{entry['backend']}:{entry['model'] or 'default'}"), []).append(entry)
    table = []
    for (kind, model), entries in sorted(rows.items()):
        accepted = sum(1 for e in entries if e["accepted"])
        seconds = sum(e.get("seconds") or 0 for e in entries) / len(entries)
        cost = sum(e.get("cost_usd") or 0 for e in entries)
        table.append((kind, model, len(entries), accepted, seconds, cost))
    return table


def cmd_results(args, root: Path) -> int:
    table = summarize(root)
    if not table:
        print("no results yet")
        return 0
    print(f"{'kind':20} {'model':28} {'tries':>5} {'ok':>4} {'rate':>5} {'mean s':>7} {'cost $':>7}")
    for kind, model, tries, ok, seconds, cost in table:
        print(f"{kind:20} {model:28} {tries:5} {ok:4} {ok / tries:5.0%} {seconds:7.0f} {cost:7.2f}")
    return 0


def cmd_auth(args, root: Path) -> int:
    config = Config.load(args.config)
    exhausted = ExhaustionState(root / "campaign/.state/exhausted.json").active()
    for name, spec in config.backends.items():
        ok, detail = backends_module.make(name, spec).available()
        state = "exhausted" if name in exhausted else ("ready" if ok else "unavailable")
        print(f"{name:10} {spec['kind']:11} {state:11} {detail}")
    return 0


def cmd_new(args, root: Path) -> int:
    path = root / "campaign/tasks" / f"{args.id}.json"
    if path.exists():
        print(f"{path} exists")
        return 1
    task = {"id": args.id, "role": args.role, "kind": args.kind, "title": args.title,
            "brief": f"campaign/briefs/{args.id}.md", "package": args.package,
            "files": args.files or [], "context": [], "check": args.check or ["lake build"],
            "base": "origin/main", "timeout_minutes": 60, "rounds": 3}
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(task, indent=2) + "\n")
    brief = root / task["brief"]
    brief.parent.mkdir(parents=True, exist_ok=True)
    if not brief.exists():
        brief.write_text(f"# {args.title}\n\nGoal:\n\nFiles:\n\nWhat done looks like:\n")
    print(f"wrote {path} and {brief}")
    return 0


def cmd_merge(args, root: Path) -> int:
    """Fold accepted branches into `--into`, one at a time, re-running each task's checks."""
    done = accepted_tasks(root)
    tasks = {t["id"]: t for t in load_tasks(root)}
    ids = args.task or sorted(done)
    worktree = workspace.create(root, f"merge-{datetime.now(timezone.utc):%Y%m%d%H%M%S}", args.into, root)
    merged, failed = [], []
    try:
        for task_id in ids:
            if task_id not in done:
                print(f"{task_id}: not accepted; skipped")
                continue
            branch = done[task_id]["branch"]
            run = workspace.git(worktree, "merge", "--no-ff", "-q", "-m", f"Merge {branch}", branch, check=False)
            if run.returncode != 0:
                workspace.git(worktree, "merge", "--abort", check=False)
                failed.append((task_id, "merge conflict"))
                continue
            task = tasks[task_id]
            ok, log = workspace.run_checks(worktree, task["package"], task["check"],
                                           float(task.get("timeout_minutes", 60)) * 60)
            if ok:
                merged.append(task_id)
                print(f"{task_id}: merged")
            else:
                workspace.git(worktree, "reset", "-q", "--hard", "HEAD~1")
                failed.append((task_id, "checks failed after merge:\n" + log[-1500:]))
        if merged and args.push:
            head = workspace.git(worktree, "rev-parse", "HEAD").stdout.strip()
            workspace.git(root, "push", "origin", f"{head}:refs/heads/{args.into.split('/', 1)[-1]}")
            print(f"pushed {head[:8]} to {args.into}")
        elif merged:
            head = workspace.git(worktree, "rev-parse", "HEAD").stdout.strip()
            print(f"merged {len(merged)} task(s) at {head[:8]} in {worktree}; pass --push to publish")
    finally:
        if not merged or args.push:
            workspace.remove(root, worktree)
    for task_id, why in failed:
        print(f"{task_id}: {why.splitlines()[0]}")
    return 0 if not failed else 1


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--config", type=Path, default=Path(__file__).resolve().parent / "profiles.json")
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[2])
    commands = parser.add_subparsers(dest="command", required=True)
    run = commands.add_parser("run", help="run pending tasks")
    run.add_argument("--profile")
    run.add_argument("--parallel", type=int, default=4)
    run.add_argument("--task", action="append", help="only this task; repeatable")
    run.add_argument("--again", action="store_true", help="rerun tasks already accepted")
    run.add_argument("--keep", action="store_true", help="keep the worktrees")
    run.add_argument("--dry-run", action="store_true", help="print each task's tier chain and brief; run nothing")
    run.add_argument("--warm-from", type=Path, help="checkout whose .lake builds warm the worktrees (default: this one)")
    commands.add_parser("status", help="each task's state")
    commands.add_parser("results", help="success rate per task kind and model")
    commands.add_parser("auth", help="which backends can run")
    new = commands.add_parser("new", help="scaffold a task and its brief")
    new.add_argument("id")
    new.add_argument("--role", required=True, choices=ROLES)
    new.add_argument("--kind", required=True)
    new.add_argument("--title", required=True)
    new.add_argument("--package", default="contracts/w-near/verification")
    new.add_argument("--files", nargs="*")
    new.add_argument("--check", nargs="*")
    merge = commands.add_parser("merge", help="fold accepted branches into a branch, re-checking each")
    merge.add_argument("--into", default="origin/main")
    merge.add_argument("--task", action="append")
    merge.add_argument("--push", action="store_true")
    args = parser.parse_args(argv)
    root = args.root.resolve()
    try:
        return {"run": cmd_run, "status": cmd_status, "results": cmd_results, "auth": cmd_auth,
                "new": cmd_new, "merge": cmd_merge}[args.command](args, root)
    except (ConfigError, OSError) as error:
        print(f"campaign: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
