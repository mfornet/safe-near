---
name: refinement-stress
description: Stress-test a contract model against its deployed binary before proving the refinement. Write differential scenarios (common flows, border cases, interleavings of calls and callbacks, adversarial inputs, random sequences), run them on near-lean and on the model, triage every discrepancy, fix the model, and report what is covered. Use when asked to review, fuzz, stress-test or build trust in a model or a refinement statement.
argument-hint: "<contract> [focus]"
---

The goal is trust in the model before anyone tries to prove
`refines_<contract>`. A proof of a false statement fails late and
expensively; a scenario that shows the model and the binary disagree fails in
seconds. The work is adversarial: you are looking for inputs where the model
is wrong, not collecting passing tests. A round that finds nothing has to say
what it tried, so the reader can judge how much trust it buys.

The contract is `$ARGUMENTS` (a name from `contracts/`). An optional second
word narrows the round to one area, such as `callbacks` or `gas`.

## The harness

Every receipt in a scenario runs on the binary through
`Near.Boundary.execOn`, the runtime the refinement theorem is stated against,
and on the model. Both results are checked against the three clauses of
`NearInterface.Refines`. Before each receipt, the runner also checks that the
theorem's hypotheses hold.

- **wNEAR** has the harness:
  - **Runner:** `contracts/w-near/verification/Differential/`.
    `Runner.lean` is contract-independent, behind an `ExecModel`;
    `WNear.lean` is the wNEAR instance.
  - **Scenarios:** `contracts/w-near/verification/scenarios/`.
  - **Generator:** `scenarios/generate.py`, for generated and random files.
  - **Docs:** `scenarios/README.md` has the format, the semantics of every
    field and the findings so far. Read it first.
  - **Running it:** `just wnear-scenarios [-v] [--only text] [paths]`.
- **Another contract** needs an `ExecModel` instance first. It is a few dozen
  lines in `<contract>/verification/Differential/`, plus an executable and a
  `just` recipe, following `WNear.lean` and `Main.lean`. The fields:
  - `decode` is the function whose graph is `Parses`.
  - `step`, `gas`, `encodeState`, `encodeRet`, `encodeReceipts` and
    `failure` are exactly the model's definitions.
  - `invViolation` is the decidable part of the invariant.
  - `initial` builds a model state and its storage from JSON.

  When a second contract needs the runner, move `Runner.lean` to
  `near-lean/runtime` instead of copying it. If the model is not yet a
  `NearInterface.ContractModel`, stop and say so: there is no statement to
  stress.

## Steps

1. **Start clean.** Work on a branch from `origin/main`; the result is a PR.
   - **Build cache:** in a fresh worktree, clone the main checkout's
     `near-lean/.lake`, `near-lean/*/.lake` and the contract's `.lake` with
     `cp -Rc` first. A cold Mathlib build takes hours.
   - **Baseline:** run the existing scenarios. They must pass before you add
     any. A failure on a fresh `main` is a finding in itself: runtime changes
     surface there. One round found a gap that a runtime change on `main` had
     introduced.

2. **Read before writing.** Read three things side by side:
   - the model (`Model/`, in particular every panic site and every branch);
   - the contract's Rust source and its SDK version;
   - the boundary (`near-lean/runtime/NearRuntime/Boundary.lean`: what
     `observe` checks after the VM, and in which order).

   From these, list the pathways: every method × every branch × every
   failure kind. That list becomes the coverage table you report.

3. **Write scenarios by attack surface.** Each one targets a specific claim
   of the model. Give each receipt an `expect`, so a scenario that silently
   stops reaching its path reports BROKEN. Use `probe` for blocks of
   independent checks. Use `gas: "bound"` and `"bound-1"`: they sit exactly
   on the edge where `Refines` starts promising a match. The surfaces, with
   what earlier rounds found in each:
   - **Protocol limits the model forgot.** Earlier rounds found the total log
     length (a long memo) and the validation of the receipts a call creates
     (zero gas forwarded, total prepaid gas). Go through
     `near-lean/vm/configs/runtime_config_v*.json` `limit_config` field by
     field: number of logs, log length, arguments length, receipt size,
     promises per call, register size, storage key and value length, data
     dependencies. For each, decide whether the contract can reach it. A
     limit you argue is unreachable goes in the report, with the argument.
   - **Deserialization.** Earlier rounds found that serde_json does not check
     UTF-8 in ignored values.
     - **Shapes:** probe what the SDK accepts against what the model's
       `decode` accepts: object and array forms, duplicate and unknown
       fields, `null` options, escapes, surrogates, invalid UTF-8, nesting
       depth, numbers, whitespace, BOM.
     - **Which strings:** typed fields, ignored fields, keys.
     - **Results too:** callback results are parsed the same way.
   - **The gas bound.** It must hold for every input, every trie and every
     receiver. Earlier rounds found a payout to an implicit account (it pays
     to create the account) and the bytes of a callback result (leading zeros
     cost the most).
     - **Probe at `bound`:** every input that makes a call cost more — length
       and shape of arguments and results, account id kinds (named,
       64-hex implicit, `0x` ETH-implicit), deep tries (`trie` records
       sharing key prefixes), cold and warm cache.
     - **Measure:** before choosing a constant, measure the slope (gas per
       byte for each shape) with `-v` on a scratch scenario.
   - **Order of failures.** When two things fail, which is reported?
     - Inside the VM, failures happen in program order: a log over the limit
       or a promise the balance cannot pay fails where the code emits it.
       Read the Rust source for the order of its checks, and the SDK wrapper
       for the deposit, private and initialisation checks.
     - After the VM, `observe` checks receipt validation, then the storage
       stake.

     Construct inputs that trip two checks at once, and compare the reported
     failure.
   - **Resources.**
     - Contract balance against the promises' deposits.
     - The storage stake, including the 770-byte zero-balance exemption.
     - Locked balance.
     - `u128` and `u64` edges of state, amounts and balances.
     - Deposits on views and on non-payable methods.
   - **Reachability and interleavings.** Callbacks delivered late, in
     reverse order, twice, or forged by another predecessor. Parties
     unregistering or re-registering between a call and its callback. Calls
     to the contract itself. Every promise-result shape: none, `notReady`,
     failed, empty, garbage, extra results.
   - **Random sequences.** Extend `generate.py` with seeded interleavings
     over a few accounts. Include a 64-character implicit account and the
     contract itself as callers; amounts at 0, 1 and the `u128` edges; and gas
     choices including `bound`, `bound-1` and the contract's own thresholds.
     Run many fresh seeds in the scratchpad. Commit only the seeds that found
     something, as regressions, plus a handful for breadth.

4. **Triage every discrepancy** before fixing anything. Decide which side
   is wrong:
   - **The model is wrong** (the common case). Fix it in `Model/`, citing the
     Rust source or nearcore. A generic runtime behaviour (limits,
     validation, resource checks) belongs in `near-lean/interface`, where
     every model can use it, not in one contract's model. Earlier rounds
     added `logLimitError` and `ReceiptValidation` there.
   - **near-lean differs from nearcore.** Check the pinned nearcore source
     (`near-lean/runtime/reference.json`), or a conformance tool such as
     `just near-conformance`. Never bend the model to a runtime bug: fix the
     runtime, or report it.
   - **The statement is wrong**, for example a hypothesis that cannot hold or
     a clause that cannot be met. Report it to the user before changing
     `Refines` or `Context.WF`. These are shared by every contract.
   - **The scenario or the harness is wrong**: a BROKEN result, a violated
     hypothesis, an expectation that no longer fits. Fix the scenario. Don't
     weaken a check to make it pass.

5. **After each fix**, rebuild and rerun everything, not just the scenario
   that found it:
   - `lake build --wfail` for the contract's `Model`, `Spec` and the harness.
   - `lake build Proofs`: only the open refinement `sorry` may remain. Fix the
     proofs a model change breaks.
   - The changed `near-lean` packages.
   - The contract's audit recipe (`just wnear-audit` for wNEAR).
   - All scenarios.

   A model fix that changes a specification adds hypotheses or changes what
   a theorem says. Call it out in the report: the user has to accept it.

6. **Keep runs fast.** The interpreter is slow on large inputs. Keep each
   default file under about 30 seconds and put megabyte inputs in
   `scenarios/slow/`, which runs only when named. On macOS, `scenarios/` and
   a Lean directory `Scenarios/` are the same directory.

7. **Report and PR.**
   - **Scenarios:** commit the new scenarios and the generator changes.
   - **README:** update `scenarios/README.md`: the file table, and the
     findings with their fixes.
   - **PR description:**
     - every discrepancy found, how it was triaged and how it was fixed;
     - specification changes;
     - the coverage table: pathways × scenario labels, with the limits argued
       unreachable;
     - what was not tried.
   - **Tracker:** findings that are not fixed in the round are filed as the
     periodic check files them (`notes/design/PERIODIC_CHECK.md`, "Findings
     in Linear").

Agreement on finitely many inputs proves nothing. Never describe a round as
showing the model is correct. Say what it covered and what it found.
