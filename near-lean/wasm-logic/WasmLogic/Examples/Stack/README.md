# The Iris-Wasm stack, ported

Iris-Wasm's stack case study (`theories/iris/examples/stack/` at commit
`e37f8387a1171d104d78a2f77f9e637e090cf3d4`, MIT, see [`NOTICE`](../../../NOTICE)):
a module that keeps stacks of `i32`s in memory pages, with a function to make
a stack, to test it, to push, to pop, to measure it and to map a function
from a table over it.

- `stack.wat` is the module as text; `stack.wasm` is compiled from it by the
  pinned wasm-tools and `Bytes.lean` is its byte literal
  (`scripts/check-wasm-bytes.sh` keeps them in step).
- `Code.lean` names Iris-Wasm's fragments (`validate_stack`, `push_op`, …)
  and proves `stack_decodes : Binary.decode stackBytes = .ok stackModule`
  with the kernel: the specifications are about the binary.
- `Specs.lean` and `Map.lean` state and prove every function's
  specification, instruction by instruction with the rules, for every stack
  and every argument. Nothing runs the machine on an input.
- [`../Client`](../Client) is Iris-Wasm's client: it imports the stack's
  functions and table, installs `square` with an element segment and runs
  `main` as its start function, which maps `square` over a stack and stores
  36 - 16 = 20 in the global `answer`. `client_adequate` proves, for any
  fuel, what the whole pipeline (validation, the runtime's linker,
  `Link.instantiate` running the start function) does: it never traps, and
  `answer` ends 20, or -1 when no page is left.

## Lemma by lemma

| Rocq (`function/…`) | Lean |
|---|---|
| `stack_common.v`: `isStack` | `isStack` |
| `stack_common.v`: `is_stack_valid`, `is_stack_bound_valid` | `is_stack_valid`, `is_stack_bound_valid`; `validated` packages the shared prefix of every function |
| `new_stack.v`: `spec_new_stack` | `spec_new_stack` |
| `is_empty.v`: `spec_is_empty_op`, `spec_is_empty` | same names |
| `is_full.v`: `spec_is_full_op`, `spec_is_full` | same names |
| `push.v`: `spec_push_op`, `spec_push` | same names |
| `pop.v`: `spec_pop_op`, `spec_pop` | same names |
| `stack_length.v`: `spec_stack_length_op`, `spec_stack_length` | same names |
| `stack_common.v`: `stackAll`, `stackAll2` | same names (`Map.lean`) |
| `stack_map.v`: `spec_map_loop_body_terminate`, `spec_map_loop_body_continue`, `spec_map_loop_j` | `spec_map_loop`, by induction on `j`, its two cases being the two loop-body lemmas |
| `stack_map.v`: `spec_map_op`, `spec_stack_map` | same names |
| `stack_client.v`: `main`, `square`, `client_module` | `Client/Code.lean`: `main`, `square`, `clientModule` (decoded from `client.wasm`) |
| `stack_client.v`, `stack_instantiation.v`: the client's and the stack's instantiation, `main`'s spec | `Client/Main.lean`: `client_links`, `square_spec`, `main_spec`, `start_adequate`, `client_adequate` |

Not ported, as the criteria note scopes it: `stack_map_trap.v` (the variant
where the callee may trap), the logical relation and robust safety
(`stack_robust.v`, `stack_module_robust.v`), and host reentrancy.

## Deviations from the Rocq statements

The statements are transliterations: the same preconditions and
postconditions up to notation. These are the differences, all of
representation except the last two rows, which are hypotheses our runtime
forces and Iris-Wasm's does not.

| Rocq | Lean | Why |
|---|---|---|
| `↪[frame] f0` in pre- and postconditions | the frame is the index of `Triple`/`wpi` (`f`), and postconditions say what the final frame `g` keeps: `⌜g.inst = f.inst ∧ g.mi = f.mi⌝`, or `⌜g = f⌝` where Iris-Wasm returns `↪[frame] f0` | Our machine keeps locals in the thread, not the store, so the frame is not a resource (criteria note §3.2). The information is the same. |
| `f0.(f_inst).(inst_memory) !! 0 = Some n` | `f.mi.memAddrs[0]? = some n` | Notation. |
| `w = immV [v]` | `vs = [v]` | Notation. |
| `{{{{ P }}}} es @ E {{{{ Q }}}}` for every mask `E` | `Triple lim d f P es Q`, at mask `⊤` | Our fragment WP has no mask parameter. No spec here opens an invariant, so no proof needed one. |
| Iris-Wasm's `WP` is `NotStuck` | `MaybeStuck` | `Exec.step` is total: every configuration steps, finishes or traps, so there is nothing for stuckness to rule out. |
| `N.of_nat a ↦[wf] cl` owned, and passed through the callee's spec | `a ↪[wf] FuncInst.wasm …` persistent, not passed | Function instances never change in our store, so their cells are persistent. A stronger resource, not a weaker spec. |
| The callee's spec takes `↪[frame] fc` | It is a `wpInvoke`, which has the callee's own frame | Same reason as the first row. |
| `cl` any closure of type `[i32] → [i32]` | `FuncInst.wasm ctype cinst ccode` with `ctype = [i32] → [i32]` | Our `call_indirect` rule covers Wasm callees; a host callee would need `wpi_call_host`'s contract form for indirect calls, which no proof here needed. |
| No call-depth hypothesis | `spec_stack_map` assumes `d + 1 < lim.maxCallDepth` | The runtime, like nearcore, traps past a fixed call depth (`ExecLimits.maxCallDepth`), so a call is safe only below it. Every call rule carries the same premise. |

## Proof size

`scripts/proof-lines.py <iriswasm checkout>` counts the non-blank,
non-comment lines of the proved statements on each side (criterion S3.4
asks for at most 1.5×):

| Rocq file | Rocq lines | Lean lines | Lean / Rocq |
|---|---:|---:|---:|
| `new_stack.v` | 420 | 122 | 0.29 |
| `is_empty.v` | 226 | 55 | 0.24 |
| `is_full.v` | 271 | 101 | 0.37 |
| `push.v` | 441 | 145 | 0.33 |
| `pop.v` | 397 | 129 | 0.32 |
| `stack_length.v` | 103 | 87 | 0.84 |
| `stack_map.v` | 684 | 320 | 0.47 |
| `stack_common.v` | 768 | 176 | 0.23 |
| total | 3310 | 1135 | 0.34 |

## Mutation test

`scripts/mutation-test.py` changes one instruction at a time in the decoded
stack and client modules and checks that a proof fails; the decode theorems
are stubbed while it runs, so only the specifications can notice. All 21
mutants are killed:

| # | Mutant | Killed in |
|---:|---|---|
| 1 | `is_empty` compares with `ne` | `Specs.lean` |
| 2 | `is_full` checks the wrong offset | `Specs.lean` |
| 3 | `push` moves the pointer by 8 | `Specs.lean` |
| 4 | `push` stores the address, not the value | `Specs.lean` |
| 5 | `push` does not update the pointer | `Specs.lean` |
| 6 | `pop` moves the pointer up | `Specs.lean` |
| 7 | `pop` returns the address, not the value | `Specs.lean` |
| 8 | `stack_length` takes a remainder | `Specs.lean` |
| 9 | `new_stack` grows by two pages | `Specs.lean` |
| 10 | `new_stack` computes the address wrongly | `Specs.lean` |
| 11 | `new_stack` returns 0 on failure | `Specs.lean` |
| 12 | `validate_stack` traps on valid stacks | `Specs.lean` |
| 13 | `stack_map` stops at once | `Map.lean` |
| 14 | `stack_map` steps by 8 | `Map.lean` |
| 15 | `stack_map` calls the table entry named by the stack | `Map.lean` |
| 16 | `stack_map` starts at the top | `Map.lean` |
| 17 | the client pushes 7 | `Client/Main.lean` |
| 18 | the client adds the popped values | `Client/Main.lean` |
| 19 | the client stores 0 when `new_stack` fails | `Client/Main.lean` |
| 20 | the client maps with table entry 1 | `Client/Main.lean` |
| 21 | `square` doubles | `Client/Main.lean` |
