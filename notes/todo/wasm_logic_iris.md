# WasmLogic: a usable iris-lean program logic for the Wasm runtime

Follow-up to Phase 4 of [wasm_runtime_rewrite.md](wasm_runtime_rewrite.md).
Today `near-lean/wasm-logic` has the iris-lean `Language` instance, rules that
own the **whole store** (`ownP`), adequacy back to `Exec.run`, and one example
proved by letting the kernel run the machine on a fixed input. That proves
nothing about a function for *all* inputs and can't host a proof written
elsewhere.

Goal: a separation logic at the **Wasm level** (not NEAR) good enough that
an existing Iris proof about Wasm code can be ported with its statements
intact. This note fixes, before any code is written, what "done" means and
how each point is measured.

Items marked **Decided** are not re-opened without discussion. Items marked
**Open** are for the implementer to settle and record here.

## 1. Porting source — **Decided**

[Iris-Wasm](https://github.com/logsem/iriswasm) (Rao, Georges, Legoupil,
Conrad, Bodin, Birkedal; PLDI 2023), Rocq, **MIT licence**. It is the
reference Iris logic for Wasm 1.0, and its case studies are the benchmark.
We port from it with attribution (copyright line and licence text in
`near-lean/wasm-logic/NOTICE`, file headers name the Rocq file).

The removed Talos `iris-wasm` (AGPL) stays off-limits under the clean-room
rule in `near-lean/wasm/README.md`. Iris-Wasm and Talos `iris-wasm` are
different projects; a reviewer checks that nothing comes from the latter.

Benchmark: the stack case study,
`theories/iris/examples/stack/` in Iris-Wasm:

| Rocq file | What we port |
|---|---|
| `function/stack_common.v` | `isStack`, the stack's memory layout |
| `function/new_stack.v`, `is_empty.v`, `is_full.v`, `pop.v`, `push.v`, `stack_length.v` | `spec_*` lemmas for each function |
| `function/stack_map.v`, `stack_map_trap.v` | `spec_stack_map` (exercises `call_indirect` and tables) |
| `stack_instantiation.v`, `stack_client.v` | instantiation spec of the module and a client, end to end |

Not in scope for this milestone (listed so the work does not creep): the
logical relation and robust safety (`iris_fundamental.v`, `valid_*`,
`stack_robust.v`, `stack_module_robust.v`), host reentrancy
(`stack_with_reentrancy.v`), total correctness, and anything NEAR-specific.
They are the next milestone once this one is green.

## 2. Success criteria — **Decided**

The work is done when every row holds. Each one has a mechanical check;
"Where" says what enforces it.

### S1. Soundness and trusted base

| # | Criterion | Measured by |
|---|---|---|
| S1.1 | The executable semantics is the semantics of the logic. `near-lean/wasm` gains lemmas only; `Exec.step`, `Exec.run`, `Store`, `Thread` are unchanged. | `git diff` on `near-lean/wasm/Wasm/{Exec,Store,Syntax,Numeric,Memory}.lean` adds no definitions; `testsuite_report.txt` byte-identical (CI drift check). |
| S1.2 | One adequacy theorem, stated over `Wasm.Exec.run`, from which every end-to-end corollary is derived. It says: given a WP proof from the initial resources of a configuration, every run that finishes satisfies the postcondition (values *and* final store, not just values). | Statement reviewed once and frozen in `WasmLogic/Adequacy.lean`; corollaries in examples call it, nothing else. |
| S1.3 | No `sorry`, no `native_decide`, no axioms beyond `propext`, `Classical.choice`, `Quot.sound`. | `python3 tools/axiom-audit.py near-lean/wasm-logic` → 0 violations (already in CI). |
| S1.4 | The trusted surface is small and listed: the `Language` instance, the state interpretation, the definitions of the points-to assertions, and the adequacy statement. Everything else is a lemma. | A "Trusted definitions" section in the package README naming the files; review checks nothing else is `def`-level logic. |
| S1.5 | Wasm level only. | `wasm-logic` depends on `Wasm` and `iris` alone (lakefile); no `NearVM` import. |

### S2. The logic is complete for the instruction set

| # | Criterion | Measured by |
|---|---|---|
| S2.1 | Every `Wasm.Instr` constructor in the NEAR feature set has a WP rule with a **small footprint**: it mentions only the resources the instruction reads or writes (the touched bytes, global, table entry, frame), never the whole store. Floats get rules over the uninterpreted operations. | A Lean check (`#eval`/`#guard` command in `WasmLogic/Coverage.lean`, built in CI) enumerates `Instr` constructors and fails if one has no rule tagged for it. Out-of-feature constructors are listed explicitly. |
| S2.2 | Structural rules: sequencing/bind, frame rule, `block`, `loop`, `if`, `br`/`br_if`/`br_table` through labels, `return`, `call` to a Wasm function, `call_indirect`, host `call` against a host *contract* (not an implementation), trap propagation, `memory.grow`/`size`. | Same coverage file lists them; each is used in at least one example. |
| S2.3 | Every rule names its Iris-Wasm counterpart (`wp_binop`, `wp_load`, `wp_block`, …) so a ported proof can find its lemmas. Rules with no counterpart, or with a different shape, are listed with the reason. | A name table in the README, or an attribute in the style of iris-lean's `rocq_alias` (already used by its HeapLang port). |
| S2.4 | Resource vocabulary matching Iris-Wasm: `↦[wf]` function, `↦[wt]` table entry, `↦[wm]` byte, `↦[wms]` byte list, `↦[wmlength]` memory size, `↦[wg]` global, `↪[frame]` locals + instance, plus ownership of the host state for host calls. Derived `↦[i32]`/`↦[i64]` word points-to. | Definitions present; separation lemmas (`↦[wms]` split/append, word ↔ bytes) proved. |

### S3. The port succeeds (the main yardstick)

| # | Criterion | Measured by |
|---|---|---|
| S3.1 | Every `spec_*` lemma of the stack case study (§1) is stated and proved in Lean. | Proved, audited, built in CI. |
| S3.2 | **Faithful statements.** Each Lean lemma is a transliteration of its Rocq statement: same pre- and postconditions up to notation. Any difference goes in a deviations table (Rocq text, Lean text, why). Representation-only differences (e.g. how a frame is encoded) are allowed; an extra hypothesis that weakens the spec is not. Target: zero semantic deviations. | Deviations table in `WasmLogic/Examples/Stack/README.md`; reviewed side by side against the Rocq file. |
| S3.3 | **Symbolic, for all inputs.** Specs quantify over the stack contents and arguments; proofs go instruction by instruction with the rules of S2. They do not use `wp_run`, `decide` over the machine, or anything that executes a concrete input. | Grep in CI: no `wp_run` / `decide` in `Examples/Stack/`. |
| S3.4 | **Proof effort is comparable.** Lean proof lines per function within 1.5× of the Rocq proof. Above that, the rules or tactics are at the wrong level and get fixed, not the budget. | A script counts lines per lemma on both sides; the table goes in the example README. |
| S3.5 | **The proof is about the binary.** The stack module is a `.wat` file compiled by the pinned `wasm-tools`. The proof is about what our decoder produces from those bytes (`Module.decode bytes = .ok stackModule`, checked by the kernel), not about a hand-built AST alone. | Theorem in the example; bytes committed. |
| S3.6 | **End to end.** The client of `stack_client.v` gets a corollary of adequacy (S1.2) about `Exec.run` on the decoded, validated and instantiated modules: every finished run returns what the spec says and never traps. | Theorem in the example. |

### S4. The specs are not vacuous

| # | Criterion | Measured by |
|---|---|---|
| S4.1 | Preconditions are reachable: S3.6 establishes, from instantiation, the preconditions the function specs assume, so no spec is proved under an unsatisfiable hypothesis. | S3.6 depends on each `spec_*`. |
| S4.2 | **Mutation test.** A script makes at least 10 small mutations to the stack `.wat` (wrong offset, `add`↔`sub`, dropped store, off-by-one bound in `is_full`, swapped `br_if` target, …), rebuilds, and checks that a proof fails for each. All mutants must be killed. | `near-lean/wasm-logic/scripts/mutation-test.sh`, run in the periodic check; results committed. |
| S4.3 | Agreement with execution: the CLI runs the client on sample inputs and the result matches the S3.6 postcondition. | Smoke step in CI. |

### S5. Engineering

| # | Criterion | Measured by |
|---|---|---|
| S5.1 | Build time stays affordable: `wasm-logic` (iris-lean cached) builds in CI in under 15 minutes; no single file over 3 minutes. Baseline recorded before starting. | CI timings; `lake build` with per-file timing in the PR description. |
| S5.2 | Clean room and licence: `NOTICE` with Iris-Wasm's MIT text; independent review recorded in `near-lean/wasm/REVIEW.md`, as for Phase 4. | Review entry present. |
| S5.3 | Docs: package README (modules, trusted definitions, rule table), `notes/design/WASM_RUNTIME.md` and `notes/TODO.md` updated. | Review. |

## 3. Design questions — **Open**

These block the points-to work and are decided first, recorded here.

1. **Compositional WP over a flat machine.** Iris-Wasm's expressions are
   administrative instruction sequences with label/frame evaluation
   contexts, so `bind` and `wp_seq` come from the context structure. Our
   machine runs a whole `Thread` (value stack, labels, call frames) with no
   syntactic contexts. Options:
   (a) keep `Language` as is and define a derived fragment WP, "running `es`
   in this frame under any continuation `K` reaches `K` with `Φ`",
   quantifying over continuations, then derive bind, sequencing and the label
   rules. The runtime stays untouched and the existing adequacy is reused.
   (b) restate the language over fragment and context (an `EctxLanguage`),
   with a proved correspondence to `Exec.step`.
   Leaning (a). Either way, S1.1 holds.
2. **Where locals and the frame live.** Locals are in `Thread.frames`, not
   in the store, but the state interpretation sees only the language state.
   `↪[frame]` needs the current frame in the state, either by making the
   language state `Store × frame` (a language-level split, the runtime
   unchanged) or by ghost tracking.
3. **Memory granularity.** Byte-level `↦[wm]` as in Iris-Wasm, with word
   points-to derived, versus word-level primitives. Byte-level matches the
   port; check that the `Memory` page representation still gives a clean
   `gen_heap` view.
4. **Partial correctness.** Iris-Wasm is partial (WP, not total WP);
   `Exec.run` reports `outOfFuel` as "no claim". Match that. Total WP (which
   iris-lean has) is a later milestone, relevant to gas bounds.

## 4. Order of work

1. Settle §3, record the decisions, freeze the adequacy statement (S1.2).
2. State interpretation and points-to (S2.4); numeric, local, global and
   memory rules; coverage check (S2.1).
3. Control rules and bind (S2.2). Re-prove the `Sum` example symbolically for
   all `n` as the first check of S3.3.
4. `call`, `call_indirect`, tables, host-call rule against a contract.
5. Stack functions (S3.1–S3.4), then `.wat`/binary (S3.5), instantiation and
   client (S3.6).
6. Mutation test and smoke run (S4), timings, review, docs (S5).
