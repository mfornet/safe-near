# WasmLogic

A separation logic over the Wasm runtime in [`../wasm`](../wasm/README.md),
built on [iris-lean](https://github.com/leanprover-community/iris-lean)
(pinned by revision in `lakefile.toml`), good enough to port proofs written
in [Iris-Wasm](https://github.com/logsem/iriswasm) with their statements
intact. The success criteria and how each is measured are in
[notes/todo/wasm_logic_iris.md](../../notes/todo/wasm_logic_iris.md); the
benchmark port, Iris-Wasm's stack case study, is in
[`WasmLogic/Examples/Stack`](WasmLogic/Examples/Stack/README.md).

The clean-room rule of [`../wasm/README.md`](../wasm/README.md) applies: this
package is written from iris-lean, the runtime and Iris-Wasm (MIT, see
[`NOTICE`](NOTICE)), never from the removed Talos layer `iris-wasm`.

## Modules

| Module | What it is |
|---|---|
| `Language.lean` | The machine as an iris-lean `Language`: an expression is a running thread (with its limits) or a finished outcome, the state is the store, the primitive step is `Wasm.Exec.step`. `run_steps` ties `Exec.run` to the language's steps. |
| `Heap.lean` | The store seen as a heap: locations (`Loc`) for every byte, memory length and limit, global, table entry, function, module instance and the host state, and `lookup`/`heapOf`, what each holds. Memory cells exist only for well-formed memories. |
| `MemoryLemmas.lean` | Lemmas about the runtime's `Memory` (reads after writes, `grow`); no runtime change. |
| `Resources.lean` | The state interpretation (`ghost_map_auth` over `heapOf σ`), the points-to assertions and their Iris-Wasm notations (`↦[wm]`, `↦[wms]`, `↦[i32]`, `↦[wmlength]`, `↪[wmlimit]`, `↦[wg]`, `↦[wt]`, `↪[wf]`, `↪[inst]`, `↦[host]`), and the lifting lemmas over `Exec.step` with small footprints. |
| `Frag.lean` | The weakest precondition of a fragment, `wpi lim d f vs es Φ`: instructions `es` in frame `f` (locals, module instance) at call depth `d`, ending normally, by a branch, by a return or by a trap as `Φ : Post` says. Bind (`wpi_seq`), framing (`wpi_wand`) and the generic instruction rule. |
| `Tactic.lean` | `wp_step k rule` and friends for stepping through code; `kernel_rfl` for equations the kernel evaluates (decoding, validation, linking). |
| `Rules/Pure.lean`, `Rules/Memory.lean`, `Rules/Control.lean`, `Rules/Call.lean` | One rule per instruction (table below), with the footprint the instruction touches: the bytes, the global, the table entry, the frame. `wpInvoke` is the specification of a function invocation; `call` to a host function is against a contract (`HostContract`), not an implementation. |
| `Adequacy.lean` | The closed resource family and the adequacy theorems back to `Exec.run`. |
| `Coverage.lean` | `#check_rule_coverage`: fails the build unless every `Wasm.Instr` constructor has its rules, or is listed out of scope. |
| `Examples/Sum.lean` | A counting loop proved for every input by induction, and its adequacy corollary. |
| `Examples/Stack/` | Iris-Wasm's stack module, from bytes, and every function's specification. |
| `Examples/Client/` | A client module linked against the stack by the runtime's linker, proved from the stack's specifications, end to end. |

## What to trust

The end-to-end theorems (`sum_adequate`, `main_adequate`, and the
`*_decodes`/`*_instantiates` theorems they rest on) are statements about
`Wasm.Exec.run`, `Wasm.Binary.decode`, `Wasm.Module.validate` and
`Wasm.Link`: nothing in this package needs to be trusted to read them.

An intermediate specification (a `Triple`, `wpi` or `wpInvoke` statement)
means what adequacy makes it mean. Reading one trusts:

- `Language.lean`: the `Language` instance (step = `Exec.step`);
- `Heap.lean`: `lookup`, what each location holds;
- `Resources.lean`: the state interpretation and the definitions of the
  points-to assertions;
- `Frag.lean` and `Rules/Call.lean`: `wpi`, `Post`, `Kont` and `wpInvoke`;
- `Adequacy.lean`: the statements of `wp_adequacy_cells` (the root),
  `adequacy_cells` and `adequacy`.

Everything else is a lemma. Proofs use only the standard axioms:
`python3 tools/axiom-audit.py near-lean/wasm-logic --report audit/wasm-logic.json`.

## Rules

Every rule names its Iris-Wasm counterpart; `Coverage.lean` holds this table
and checks it against `Wasm.Instr` on every build. Out of scope is what
nearcore keeps behind `reftypes_bulk_memory`, off in every protocol version
the project models.

| Instruction | Lean rules | Iris-Wasm |
|---|---|---|
| `unreachable` | `wpi_unreachable` | wp_unreachable |
| `nop` | `wpi_nop` | wp_nop |
| `block` | `wpi_block` | wp_block |
| `loop` | `wpi_loop` | wp_loop |
| `if` | `wpi_if_true`, `wpi_if_false` | wp_if_true, wp_if_false |
| `br` | `wpi_br` | wp_br |
| `br_if` | `wpi_br_if_true`, `wpi_br_if_false` | wp_br_if_true, wp_br_if_false |
| `br_table` | `wpi_br_table` | wp_br_table |
| `return` | `wpi_return` | wp_return |
| `call` | `wpi_call`, `wpi_call_host`, `wpi_call_exhausted` | wp_call, wp_invoke_host; depth limit: none |
| `call_indirect` | `wpi_call_indirect` | wp_call_indirect_success |
| `ref_null` | `wpi_ref_null` | none (Wasm 1.0) |
| `ref_is_null` | `wpi_ref_is_null` | none (Wasm 1.0) |
| `ref_func` | `wpi_ref_func` | none (Wasm 1.0) |
| `drop` | `wpi_drop` | wp_drop |
| `select` | `wpi_select_true`, `wpi_select_false` | wp_select_true, wp_select_false |
| `local_get` | `wpi_local_get` | wp_get_local |
| `local_set` | `wpi_local_set` | wp_set_local |
| `local_tee` | `wpi_local_tee` | wp_tee_local |
| `global_get` | `wpi_global_get` | wp_get_global |
| `global_set` | `wpi_global_set` | wp_set_global |
| `load` | `wpi_load` | wp_load, wp_load_packed (one rule over widths) |
| `store` | `wpi_store` | wp_store, wp_store_packed (one rule over widths) |
| `memory_size` | `wpi_memory_size` | wp_current_memory |
| `memory_grow` | `wpi_memory_grow`, `wpi_memory_grow_fail`, `wpi_memory_grow_either` | wp_grow_memory (its either-outcome shape is wpi_memory_grow_either) |
| `i32_const` | `wpi_i32_const` | wp_val (constants are values there) |
| `i64_const` | `wpi_i64_const` | wp_val |
| `f32_const` | `wpi_f32_const` | wp_val |
| `f64_const` | `wpi_f64_const` | wp_val |
| `i32_eqz` | `wpi_i32_eqz` | wp_testop_i32 |
| `i64_eqz` | `wpi_i64_eqz` | wp_testop_i64 |
| `i32_unop` | `wpi_i32_unop` | wp_unop |
| `i64_unop` | `wpi_i64_unop` | wp_unop |
| `i32_binop` | `wpi_i32_binop`, `wpi_i32_binop_trap` | wp_binop, wp_binop_failure |
| `i64_binop` | `wpi_i64_binop`, `wpi_i64_binop_trap` | wp_binop, wp_binop_failure |
| `i32_relop` | `wpi_i32_relop` | wp_relop |
| `i64_relop` | `wpi_i64_relop` | wp_relop |
| `f32_unop` | `wpi_f32_unop` | wp_unop |
| `f64_unop` | `wpi_f64_unop` | wp_unop |
| `f32_binop` | `wpi_f32_binop` | wp_binop |
| `f64_binop` | `wpi_f64_binop` | wp_binop |
| `f32_relop` | `wpi_f32_relop` | wp_relop |
| `f64_relop` | `wpi_f64_relop` | wp_relop |
| `cvt` | `wpi_cvt`, `wpi_cvt_trap` | wp_cvtop_convert, wp_cvtop_convert_failure, wp_cvtop_reinterpret |

Out of scope: `table_get`, `table_set`, `table_size`, `table_grow`, `table_fill`, `table_copy`, `table_init`, `elem_drop`, `memory_fill`, `memory_copy`, `memory_init`, `data_drop`.

| Structural | Iris-Wasm |
|---|---|
| `wpi_seq` | wp_seq |
| `wpi_nil` | wp_nil |
| `wpi_wand` | wp_wand_ctx; framing is part of it |
| `wpInvoke_intro` | wp_invoke_native |
| `wpi_instr` | none: the generic rule every instruction rule is derived from |
| `wp_lift` | none: the one lifting lemma, over Exec.step |
| `wp_adequacy_cells` | wp_adequacy, with final-store facts from owned cells (wp_strong_adequacy) |
| `adequacy_cells` | wp_adequacy, instantiated to Exec.run: values, traps and final cells |
| `adequacy` | wp_adequacy, instantiated to Exec.run, pure postconditions |


## Checks

| Check | What it catches | Where |
|---|---|---|
| `lake build --wfail` | every proof, the rule coverage table, the decode/validate/link theorems of the examples | CI (`wasm-logic` workflow), periodic check |
| axiom audit | `sorry`, `native_decide`, non-standard axioms | CI, periodic check |
| `scripts/check-wasm-bytes.sh` | a committed `.wasm` or byte literal out of date with its `.wat` (pinned wasm-tools) | CI, periodic check |
| `scripts/smoke-client.sh` | the linked client, run by the runtime's testsuite runner, returns what `main_adequate` says | CI, periodic check |
| `scripts/mutation-test.py` | specifications too weak to notice a changed instruction: 19 mutants, all must break a proof | periodic check (a few minutes) |
| `tools/tests/test_wasm_logic.py` | stale byte literals, unbuilt modules, escape hatches, a coverage table or mutation suite out of date, a non-Wasm dependency | every push and PR, in seconds |
| `scripts/proof-lines.py <iriswasm>` | proof size against Iris-Wasm's | by hand; result in the stack README |

```
lake build            # compiles iris-lean from source on first use
```
