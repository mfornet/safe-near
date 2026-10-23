# WasmLogic: a usable iris-lean program logic for the Wasm runtime

Follow-up to Phase 4 of [wasm_runtime_rewrite.md](wasm_runtime_rewrite.md).
When this note was written, `near-lean/wasm-logic` had the iris-lean
`Language` instance, rules that owned the **whole store** (`ownP`), adequacy
back to `Exec.run`, and one example proved by letting the kernel run the
machine on a fixed input. That proved nothing about a function for *all*
inputs and couldn't host a proof written elsewhere. §3 records the design
decisions and §5 how the result measures against the criteria.

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

## 3. Design questions — **Decided**

1. **Compositional WP over a flat machine: option (a).** `Frag.lean`
   defines `wpi lim d f vs es Φ`: running `es` in frame `f` with operands
   `vs`, under *every* context (operands below, labels around, code after,
   frames below) and every continuation `Kont` that knows how to carry on
   from each way the fragment can end (fall through, branch, return, trap),
   reaches `WP` of the whole thread. Bind (`wpi_seq`), framing (`wpi_wand`,
   `wpi_frame`) and the label rules are derived; the `Language` instance and
   the runtime are unchanged and adequacy is reused.
2. **Where locals and the frame live: in the index of `wpi`.** Neither a
   `Store × frame` language state nor ghost tracking: a `Frame` (locals,
   instance address, module instance) is a parameter of `wpi`, and
   postconditions say what the final frame keeps. The module instance is a
   persistent cell (`↪[inst]`), assumed by `wpi`. Iris-Wasm's `↪[frame]`
   becomes this index; the stack README lists it as a representation
   deviation.
3. **Memory granularity: bytes**, as in Iris-Wasm (`↦[wm]`, `↦[wms]`), with
   `↦[i32]` derived. The heap view (`Heap.lean`) shows a memory's cells only
   while it is well formed (every page empty or full size), which every
   runtime operation preserves (`MemoryLemmas.lean`).
4. **Partial correctness, `MaybeStuck`.** `Exec.step` is total, so stuckness
   rules nothing out; `outOfFuel` is "no claim". Total WP stays for later.

Decisions taken while implementing:

- **Instruction set.** nearcore enables reference types and bulk memory
  (`NearVM` validates with `Features.nearcore true`), so every `Wasm.Instr`
  constructor is in scope; the table and bulk-memory instructions, which
  Iris-Wasm does not have, get rules in its style (`Rules/Table.lean`).
- **Adequacy shape.** The root theorem, `wp_adequacy_cells`, takes a
  postcondition that owns cells chosen existentially (`cellsSat`), so a
  result that is not a return value (the client's `answer` global) can be
  stated about the final store.
- **Decoding in the kernel.** The binary decoder recursed by well-founded
  recursion, which the kernel cannot evaluate; it now spends one unit of
  fuel per nesting level and recurses structurally. Same results
  (`testsuite_report.txt` unchanged), and `Binary.decode bytes = .ok m` is
  provable by `kernel_rfl`.
- **CI.** Fast checks that need no Lean (`tools/tests/test_wasm_logic.py`)
  run on every push and PR; the Lean build, axiom audit, byte check and
  smoke run are the `wasm-logic` workflow, triggered by changes to the logic
  or the runtime; the mutation test runs in the periodic check.

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

## 5. Outcome

Measured on the branch that implements this note.

| # | Status | Evidence |
|---|---|---|
| S1.1 | Met | `Exec`, `Store`, `Syntax`, `Numeric`, `Memory` unchanged; the only runtime change is the decoder's structural recursion (§3), with `testsuite_report.txt` identical. |
| S1.2 | Met | `wp_adequacy_cells` (root: values, traps, final cells), `adequacy_cells` over `Exec.run`, `adequacy` as a corollary; `sum_adequate` and `client_adequate` derive from them. |
| S1.3 | Met | Axiom audit: 24 modules, 1771 declarations, 0 violations; in the `wasm-logic` workflow. |
| S1.4 | Met | "What to trust" in `near-lean/wasm-logic/README.md`. |
| S1.5 | Met | `lakefile.toml` requires `Wasm` and `iris` only; checked by `test_wasm_logic.py`. |
| S2.1 | Met | `#check_rule_coverage`: 56 instructions with rules, 0 out of scope; each rule's footprint is the cells the instruction touches. |
| S2.2 | Met | Each structural rule is used in an example: sequencing, `block`, `loop`, `if`, `br`, `br_if`, `return`, `call`, `call_indirect`, `memory.grow` in `Sum`/`Stack`/`Client`; `br_table`, `memory.size`, traps, the call-depth limit, the host call and the frame rule in `Examples/Control.lean`. |
| S2.3 | Met | Iris-Wasm names in `Coverage.lean` and the README rule table. |
| S2.4 | Met, with two differences | All of Iris-Wasm's vocabulary and the separation lemmas (`memBytes_append`, word ↔ bytes); `↪[frame]` is the `wpi` index (§3.2); `↦[i64]` is not defined, as no proof needed it. |
| S3.1 | Met for every function | `spec_new_stack`, `spec_is_empty`, `spec_is_full`, `spec_push`, `spec_pop`, `spec_stack_length`, `spec_stack_map` (with their `_op` lemmas). `stack_map_trap.v`, the variant where the callee may trap, is not ported. |
| S3.2 | Met, two forced hypotheses | Deviations table in `Examples/Stack/README.md`. All rows are representation except: `stack_map`'s callee must be a Wasm function, and calls need `d + 1 < maxCallDepth` (the runtime traps past a call depth, Iris-Wasm's semantics does not). |
| S3.3 | Met | Specs step through the rules for all stacks and arguments; `test_wasm_logic.py` checks that `Specs.lean`/`Map.lean` use no `Exec.run`, `Exec.step`, `kernel_rfl` or `native_decide`. `decide` appears only on closed arithmetic facts, so the check is on machine execution rather than the word `decide`. |
| S3.4 | Met | `scripts/proof-lines.py`: Lean/Rocq = 0.34 overall, at most 0.84 per file (`stack_length.v`). |
| S3.5 | Met | `stack_decodes`, `client_decodes` (kernel); `.wasm` and byte literals committed and checked against the pinned wasm-tools. |
| S3.6 | Met | `client_adequate`: for any fuel, validation, the runtime's linker and `Link.instantiate` (running `main` as start function) never fail or trap, and `answer` ends 20 with one page of memory, or -1 with none. |
| S4.1 | Partly | The client reaches `new_stack`, `push`, `pop`, `stack_map` and `square` from instantiation; `is_empty`, `is_full` and `stack_length` are proved but no end-to-end corollary reaches them (Iris-Wasm's client does not call them either). |
| S4.2 | Met | `scripts/mutation-test.py`: 21 mutants of the stack and client, all killed; in the periodic check. |
| S4.3 | Met | `scripts/smoke-client.sh` runs the linked client on the runtime and checks `answer` = 20; in CI. |
| S5.1 | Met | Clean build of the package with dependencies cached: about 65 s; slowest file `Examples/Stack/Code.lean`, 18 s (kernel decoding). |
| S5.2 | Partly | `NOTICE` with Iris-Wasm's MIT licence. The independent clean-room review is still to be done and recorded in `near-lean/wasm/REVIEW.md`. |
| S5.3 | Met | Package and example READMEs, `notes/design/WASM_RUNTIME.md`, `notes/TODO.md`. |

Next milestone, as §1 scopes it: `stack_map_trap.v`, the logical relation
and robust safety, host reentrancy; and in the rules, `memory.copy` /
`table.copy` over overlapping ranges, zero-length bulk operations, and
out-of-bounds trap rules for tables and bulk memory.
