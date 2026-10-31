# The campaign driver

`tools/campaign` runs the agent tasks of the wNEAR campaign
([`wnear_campaign_plan.md`](../todo/wnear_campaign_plan.md)): it briefs an
agent in a warm worktree, accepts only what the task's checks pass, escalates
through tiers, switches backends when a subscription or balance runs out, and
records every attempt per task kind and model. It is the Integrator and the
Runner of the plan's roster; the models are the other roles.

```
just campaign auth                      # which backends can run now
just campaign new ID --role prover --kind lean-proof --title "..." --files F.lean --check "lake build M"
just campaign run [--profile P] [--parallel N] [--task ID]
just campaign status | results
just campaign merge --into origin/main [--push]
```

## Backends and billing

| Backend | How it runs | Billing |
|---|---|---|
| `claude` | `claude -p --output-format json` in the worktree; the agent edits and runs commands itself | The Claude subscription the CLI is logged into. `ANTHROPIC_API_KEY` is removed from the environment so a stray key never switches billing. |
| `codex` | `codex exec --json -s workspace-write` in the worktree; likewise agentic | The ChatGPT subscription (`codex login status`). `OPENAI_API_KEY` is removed likewise. |
| `deepseek` | Chat completions over HTTP (`DEEPSEEK_API_KEY`); no tools | The API balance. The driver runs the loop: the model answers with whole files in `<<<FILE path>>> … <<<END>>>` blocks, the driver writes them, runs the checks, sends the failures back, up to `rounds` times. |

Any OpenAI-compatible endpoint is a `openai-api` backend: add it to
`tools/campaign/profiles.json` with its `base_url` and `api_key_env`.

## Profiles and exhaustion

`profiles.json` maps every role (architect, auditor, prover, grinder, runner,
integrator) to a chain of tiers per profile. The first tier runs first; the
rest are the escalation of §11.2 of the proof plan, each with its number of
attempts. A profile names fallback profiles.

When a backend reports that its limit is reached (the CLI's error text matches
the backend's `exhausted_patterns`, or the API answers 402), the driver marks
it exhausted for `exhaustion_reset_hours` (5, the Claude window) in
`campaign/.state/exhausted.json`, visible to every run. From then on the
backend's tiers are skipped and the same role's tiers from the fallback
profiles are appended, so the campaign continues on what is left:

- `default`: Opus architect, Codex auditor (never the author's family), Sonnet
  provers escalating to Codex then Opus, DeepSeek grinders, Haiku runner.
- `claude-exhausted`: Codex for every reasoning role, DeepSeek grinders.
- `codex-exhausted`: Claude for every reasoning role, DeepSeek grinders.
- `api-only`: DeepSeek everywhere. Degraded; the architect and auditor roles
  do not get the intelligence they need, so prefer waiting for a window.
- `cheap`: DeepSeek and Haiku first, Sonnet as the escalation.

Pick one with `--profile`; `claude`'s model names are the CLI's aliases
(`opus`, `sonnet`, `haiku`); `codex`'s `null` is the model configured in
`~/.codex/config.toml`, and the names in `codex`'s model list may be given
instead; DeepSeek's are `deepseek-reasoner` and `deepseek-chat`.

## Tasks

A task is `campaign/tasks/<id>.json` with a brief in `campaign/briefs/`:

```json
{"id": "parser-leaf-12", "role": "prover", "kind": "lean-proof",
 "title": "f81 closing reserve", "brief": "campaign/briefs/parser-leaf-12.md",
 "package": "contracts/w-near/verification",
 "files": ["Bridge/Functions/SerdeClose.lean"],
 "context": ["Bridge/Functions/SerdeIgn.lean"],
 "check": ["lake build Bridge.Functions.SerdeClose",
           "python3 ../../../tools/axiom-audit.py . --no-build --report /tmp/a.json"],
 "base": "origin/main", "timeout_minutes": 90, "rounds": 3}
```

- `files`, relative to `package`, are the only files the agent may change. Any
  other change is rejected, which is how "only the architect changes a
  contract" is enforced: a prover's task never lists a contract file. A task
  without `files` may change nothing (a report).
- `check` runs in `package` after the agent finishes; every command must
  pass. For a proof: the module's build and the axiom audit, so a `sorry` or
  `native_decide` is rejected mechanically.
- `kind` is the task type the results record is kept by (`lean-proof`,
  `harness-test`, `audit`, `report`, …).
- `context` is sent read-only to API models, which cannot read the tree.

The brief is prefixed with the rules (change only the listed files, never
weaken a statement, no `sorry`, run the checks, do not commit, end with a
report naming anything suspicious about the statement). The agent's final
report is kept in the results record.

## What happens on `run`

1. A worktree is created at `.campaign/worktrees/<id>` on branch
   `campaign/<id>` from the task's `base`, and every `.lake` of the checkout
   running the driver is cloned into it. On APFS `cp -c` clones ~3 GB of
   builds in about 10 seconds; Lake then replays everything the task does not
   change (`lake build Spec`: 748 jobs replayed in 5 s). On Linux
   `--reflink=auto` does the same on btrfs and xfs.
2. The role's chain is resolved from the profile and the exhausted set. For
   each tier, up to its `attempts`: the agent runs (one call for a CLI agent,
   up to `rounds` repair rounds for an API model), the file guard runs, then
   the checks. Between attempts the worktree is reset.
3. Accepted work is committed on `campaign/<id>` and the worktree removed;
   `merge` later folds accepted branches into a target one at a time,
   re-running each task's checks, and pushes with `--push`.
4. Every attempt is appended to `campaign/results.jsonl` (task, kind, role,
   backend, model, attempt, accepted, exhausted, seconds, cost, usage, the
   check log's tail, the agent's report). `results` prints the success rate
   per kind and model: the "Agent results" record of §11.2, which decides when
   a task type moves to a cheaper model.

Tasks run in parallel (`--parallel`, 4 by default; 32 cores take 6
comfortably). Each has its own worktree, so they never touch the same files;
the shared `.git` serializes commits.

## Limits

- CLI agents run with permissions bypassed inside their worktree. Nothing
  stops a misbehaving agent from touching another path; the file guard rejects
  the result, it does not prevent the edit. Run the driver on a machine whose
  checkouts you can rebuild.
- Exhaustion detection is textual for the CLIs: if a CLI changes its message,
  add the new text to `exhausted_patterns`. A backend that fails for another
  reason is retried like any failure, not marked.
- The driver does not write briefs. A task that cannot be briefed clearly is
  not ready for a cheaper model (§11.2).
