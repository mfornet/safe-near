"""The three ways to run a model, behind one interface.

- `claude-cli` and `codex-cli` run the installed command-line agents in the
  task's worktree. They edit files and run commands themselves. Billing is the
  subscription the CLI is logged into: the API key variables are removed from
  the environment so a stray key never switches billing.
- `openai-api` is a chat-completions endpoint (DeepSeek by default). It has no
  tools, so the driver runs the loop: the model answers with whole files in
  `<<<FILE path>>> … <<<END>>>` blocks, the driver writes them, runs the checks
  and sends the failures back.
- `fake` and `fake-agent` answer from a script, for the tests.

An outcome says whether the backend is exhausted (subscription or balance
over), which the driver records so the profile's fallbacks take over."""

from __future__ import annotations

from dataclasses import dataclass, field
import json
import os
from pathlib import Path
import re
import subprocess
import time
import urllib.error
import urllib.request

FILE_BLOCK = re.compile(r"<<<FILE (?P<path>[^\n>]+)>>>\n(?P<body>.*?)\n?<<<END>>>", re.S)
API_KEY_VARS = ("ANTHROPIC_API_KEY", "OPENAI_API_KEY", "ANTHROPIC_AUTH_TOKEN")
# What a proof task needs: reading and editing the tree, Lake, the repository's Python
# tools, and read-only git. No network, no package installs, no git writes.
DEFAULT_CLAUDE_TOOLS = ["Read", "Edit", "Write", "Glob", "Grep", "Bash(lake *)", "Bash(python3 *)",
                        "Bash(just *)", "Bash(git status*)", "Bash(git diff*)", "Bash(git log*)",
                        "Bash(ls *)", "Bash(cat *)", "Bash(grep *)", "Bash(wc *)", "Bash(head *)", "Bash(tail *)"]


@dataclass
class Outcome:
    text: str = ""
    ok: bool = True
    exhausted: bool = False
    seconds: float = 0.0
    cost_usd: float | None = None
    usage: dict = field(default_factory=dict)
    log: str = ""


def _matches(spec: dict, text: str) -> bool:
    return any(re.search(p, text, re.I) for p in spec.get("exhausted_patterns", []))


def _tail(text: str, lines: int = 80) -> str:
    return "\n".join(text.splitlines()[-lines:])


class Backend:
    agentic = False  # whether the model edits the worktree itself

    def __init__(self, name: str, spec: dict):
        self.name = name
        self.spec = spec

    def run(self, messages: list[dict], workdir: Path, model: str | None, timeout: float) -> Outcome:
        raise NotImplementedError

    def available(self) -> tuple[bool, str]:
        return True, "no check"


def _subscription_env(spec: dict) -> dict:
    env = dict(os.environ)
    if spec.get("billing", "subscription") == "subscription":
        for var in API_KEY_VARS:
            env.pop(var, None)
    return env


def _flatten(messages: list[dict]) -> str:
    """One prompt for a CLI agent: the brief, then any later feedback."""
    parts = []
    for m in messages:
        if m["role"] == "user":
            parts.append(m["content"])
        elif m["role"] == "assistant":
            parts.append("(your previous answer)\n" + m["content"])
    return "\n\n".join(parts)


class ClaudeCli(Backend):
    agentic = True

    def available(self) -> tuple[bool, str]:
        run = subprocess.run(["claude", "auth", "status"], capture_output=True, text=True)
        try:
            data = json.loads(run.stdout)
        except ValueError:
            return run.returncode == 0, (run.stdout + run.stderr).strip()[-80:] or "unknown"
        if data.get("loggedIn"):
            return True, f"logged in via {data.get('authMethod', '?')}"
        return False, "not logged in"

    def run(self, messages, workdir, model, timeout):
        # Least privilege by default: edits are accepted, and only the listed tools run
        # without a prompt. A prompt in `-p` mode is a denial, so the allowlist is what the
        # agent can use (`permission_mode` and `allowed_tools` in the backend's spec).
        command = ["claude", "-p", "--output-format", "json",
                   "--permission-mode", self.spec.get("permission_mode", "acceptEdits")]
        tools = self.spec.get("allowed_tools", DEFAULT_CLAUDE_TOOLS)
        if tools:
            command += ["--allowedTools", *tools]
        if model:
            command += ["--model", model]
        started = time.monotonic()
        try:
            run = subprocess.run(command, input=_flatten(messages), cwd=workdir, env=_subscription_env(self.spec),
                                 capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired as error:
            return Outcome(ok=False, seconds=time.monotonic() - started,
                           log=f"timeout after {timeout:.0f}s\n{_tail(str(error.stdout or ''))}")
        seconds = time.monotonic() - started
        text, cost, usage, is_error = run.stdout, None, {}, run.returncode != 0
        try:
            data = json.loads(run.stdout)
            text = str(data.get("result", ""))
            cost = data.get("total_cost_usd")
            usage = {"turns": data.get("num_turns"), "models": list((data.get("modelUsage") or {}).keys())}
            is_error = bool(data.get("is_error")) or data.get("subtype") not in (None, "success")
        except ValueError:
            pass
        exhausted = _matches(self.spec, text + "\n" + run.stderr) and (is_error or run.returncode != 0)
        return Outcome(text=text, ok=not is_error, exhausted=exhausted, seconds=seconds, cost_usd=cost,
                       usage=usage, log=_tail(run.stdout + "\n" + run.stderr))


class CodexCli(Backend):
    agentic = True

    def available(self) -> tuple[bool, str]:
        run = subprocess.run(["codex", "login", "status"], capture_output=True, text=True)
        return run.returncode == 0, (run.stdout or run.stderr).strip()

    def run(self, messages, workdir, model, timeout):
        last = workdir / ".campaign-last-message.txt"
        command = ["codex", "exec", "-C", str(workdir), "-s", self.spec.get("sandbox", "workspace-write"),
                   "--ephemeral", "--skip-git-repo-check", "--json", "-o", str(last)]
        if model:
            command += ["-m", model]
        command.append("-")
        started = time.monotonic()
        try:
            run = subprocess.run(command, input=_flatten(messages), cwd=workdir, env=_subscription_env(self.spec),
                                 capture_output=True, text=True, timeout=timeout)
        except subprocess.TimeoutExpired as error:
            return Outcome(ok=False, seconds=time.monotonic() - started,
                           log=f"timeout after {timeout:.0f}s\n{_tail(str(error.stdout or ''))}")
        seconds = time.monotonic() - started
        usage, failed = {}, run.returncode != 0
        for line in run.stdout.splitlines():
            try:
                event = json.loads(line)
            except ValueError:
                continue
            if event.get("type") == "turn.completed":
                usage = event.get("usage", {})
            elif event.get("type") in ("turn.failed", "error"):
                failed = True
        text = last.read_text() if last.exists() else ""
        if last.exists():
            last.unlink()
        exhausted = failed and _matches(self.spec, run.stdout + "\n" + run.stderr)
        return Outcome(text=text, ok=not failed, exhausted=exhausted, seconds=seconds, usage=usage,
                       log=_tail(run.stdout + "\n" + run.stderr))


class OpenAiApi(Backend):
    """Chat completions over HTTP; no tools. DeepSeek is OpenAI-compatible."""

    def available(self) -> tuple[bool, str]:
        var = self.spec.get("api_key_env", "")
        return bool(os.environ.get(var)), f"{var} {'set' if os.environ.get(var) else 'not set'}"

    def run(self, messages, workdir, model, timeout):
        key = os.environ.get(self.spec.get("api_key_env", ""), "")
        if not key:
            return Outcome(ok=False, log=f"{self.spec.get('api_key_env')} is not set")
        body = {"model": model or self.spec.get("default_model", "deepseek-chat"), "messages": messages,
                "temperature": self.spec.get("temperature", 0), "max_tokens": self.spec.get("max_tokens", 16000)}
        request = urllib.request.Request(
            self.spec.get("base_url", "https://api.deepseek.com").rstrip("/") + "/chat/completions",
            data=json.dumps(body).encode(), method="POST",
            headers={"Authorization": f"Bearer {key}", "Content-Type": "application/json"})
        started = time.monotonic()
        try:
            with urllib.request.urlopen(request, timeout=timeout) as response:
                data = json.loads(response.read())
        except urllib.error.HTTPError as error:
            detail = error.read().decode(errors="replace")
            exhausted = error.code in (402,) or _matches(self.spec, detail)
            return Outcome(ok=False, exhausted=exhausted, seconds=time.monotonic() - started,
                           log=f"HTTP {error.code}: {_tail(detail, 20)}")
        except (urllib.error.URLError, TimeoutError, OSError) as error:
            return Outcome(ok=False, seconds=time.monotonic() - started, log=f"request failed: {error}")
        text = data["choices"][0]["message"].get("content") or ""
        usage = data.get("usage", {})
        return Outcome(text=text, seconds=time.monotonic() - started, usage=usage, log=_tail(text))


class Fake(Backend):
    """Answers from `responses`, in order; `<<<EXHAUSTED>>>` reports exhaustion."""

    responses: dict[str, list[str]] = {}

    def run(self, messages, workdir, model, timeout):
        queue = Fake.responses.setdefault(self.name, [])
        if not queue:
            return Outcome(ok=False, log="fake backend has no response left")
        text = queue.pop(0)
        if text == "<<<EXHAUSTED>>>":
            return Outcome(ok=False, exhausted=True, text=text, log="limit reached")
        return Outcome(text=text, log=text, seconds=0.01, cost_usd=0.0)


class FakeAgent(Fake):
    """A fake that edits the worktree itself, like a CLI agent."""
    agentic = True

    def run(self, messages, workdir, model, timeout):
        outcome = super().run(messages, workdir, model, timeout)
        if outcome.ok:
            apply_file_blocks(outcome.text, workdir)
        return outcome


KINDS = {"claude-cli": ClaudeCli, "codex-cli": CodexCli, "openai-api": OpenAiApi,
         "fake": Fake, "fake-agent": FakeAgent}


def make(name: str, spec: dict) -> Backend:
    return KINDS[spec["kind"]](name, spec)


def apply_file_blocks(text: str, workdir: Path) -> list[str]:
    """Write every `<<<FILE path>>>` block under `workdir`; paths that leave it
    are refused. Returns the paths written."""
    written = []
    root = workdir.resolve()
    for match in FILE_BLOCK.finditer(text):
        relative = match.group("path").strip()
        target = (root / relative).resolve()
        if root not in target.parents:
            raise ValueError(f"file block leaves the worktree: {relative}")
        target.parent.mkdir(parents=True, exist_ok=True)
        body = match.group("body")
        target.write_text(body if body.endswith("\n") else body + "\n")
        written.append(relative)
    return written
