# wNEAR refinement: misstatement log

Every wrong statement caught during the refinement campaign
([wnear_refinement_proof.md](wnear_refinement_proof.md), section 6). A
statement caught here before its proof was finished is a detour that did not
happen: that is the point of the log.

Before writing a new contract, skim the root causes below: the same mistake
tends to come back in another place.

## Entry format

```
### <n>. <short title>

- **Statement:** the declaration and what it claimed.
- **Truth:** what actually holds.
- **Caught by:** harness / call site / failed proof / review / scenario.
- **Root cause:** the wrong assumption about the code, the runtime or the model.
- **Sweep:** where else the same mistake was looked for, and what was fixed.
- **Test added:** the harness test or scenario that would have caught it.
```

## Entries

### 1. `__multi3`'s cost: activation miscounted

- **Statement:** `Harness.multi3.cost`: 72 `regular_op_cost`.
- **Truth:** 80: the activation is 20 (64 bytes, 36 of parameters, 56 of
  seven `i64` locals, in 8-byte units), not 12; the 60 instructions were right.
- **Caught by:** harness (every input burnt 80).
- **Root cause:** the activation was estimated from the parameters only;
  `activationGas` counts the declared locals too.
- **Sweep:** `memcpy`, `memset`, `bcmp` recounted with locals: right.
- **Test added:** the cost check of `wnear-harness` on every input.

### 2. `bcmp`'s cost: loop body miscounted

- **Statement:** `Harness.bcmp.cost`: `30 + 18k` for the `k` pairs compared.
- **Truth:** 24 per equal pair (23 instructions and the back-edge charge of
  `br 0`), and two shapes: `16 + 24n` when all `n` pairs agree, `30 + 24k`
  when pair `k` differs.
- **Caught by:** harness (stated below the burnt gas on 117 of 120 inputs).
- **Root cause:** the loop body was counted from `memcpy`'s, which it does
  not share: `bcmp` loads two bytes, compares, and exits through two
  different branches.
- **Sweep:** every cost in `Harness/Builtins.lean` is now written with its
  count in a comment, and the harness reports how many inputs it matches
  exactly.
- **Test added:** the bcmp inputs with equal ranges and with differences at
  the first and last pair.

### 3. `Vec::deref`'s precondition: overlap too strong

- **Statement:** `Harness.vecDeref.pre` required the 8 output bytes not to
  overlap the 12 bytes of the `Vec`.
- **Truth:** the function writes the length (from `vec + 8`) to `out + 4`
  before it reads the pointer (at `vec`); only that slot over the pointer
  word goes wrong. Overlapping the capacity or the length is harmless.
- **Caught by:** harness (the probe outside the precondition passed).
- **Root cause:** the clause was written from the usual "no aliasing" rule
  instead of from the order of the loads and stores in the body.
- **Sweep:** `memcpy` (forward copy: harmless for `dst < src`, noted at M1),
  `stateOrPanic` (one `memcpy`, same rule): no other clause stated from the
  rule rather than the body.
- **Test added:** an input with `out` over the capacity and length (passes),
  and the probe with the length's slot over the pointer (fails).

### 4. The not-initialized panic needs the environment

- **Statement:** `Harness.stateOrPanic`: with the state absent, the call
  panics with "The contract is not initialized", from any store.
- **Truth:** `env::panic` reaches the host through the blockchain interface
  that `set_blockchain_interface` installs at the start of every method;
  from a fresh store, Rust's `unwrap` on `None` traps with `unreachable`.
- **Caught by:** harness (the generated input trapped differently).
- **Root cause:** near-sdk's environment is global state that the method's
  prologue sets up; the contract left that precondition implicit.
- **Sweep:** every contract whose function can reach `env::*` (any host
  access, any panic) needs the same ghost precondition; the method
  contracts of M3 onward state it once, from the prologue, for all callees.
- **Test added:** the generated inputs start from a store captured inside a
  method; the probe from the fresh store must fail.

### 5. `Result::expect` on `Err` needs the error's representation

- **Statement:** `Harness.resultExpect`: on `Err`, the call panics.
- **Truth:** `unwrap_failed` formats the error value through its `Debug`
  impl, which follows the pointer in the payload; with arbitrary bytes the
  call traps out of bounds instead.
- **Caught by:** harness (generated `Err` inputs trapped).
- **Root cause:** the `Err` payload was treated as opaque bytes, but its
  meaning depends on the error type `E`.
- **Sweep:** the contract now covers `Ok` only, which is all
  `ft_total_supply`'s path reaches (`to_vec` of a `U128` never fails); every
  later contract with a generic payload states its representation
  predicate (M4/M5) before covering the error path.
- **Test added:** a probe with a garbage error.

### 6. `Option<Vec<u8>>::expect`'s activation, again

- **Statement:** `Harness.optionExpect.cost`: 24 `regular_op_cost` on `Some`.
- **Truth:** 25: three `i32` parameters are 12 bytes, so the activation is
  `(64 + 12 + 7) / 8 = 10`, not 9.
- **Caught by:** harness (every `Some` input burnt 25).
- **Root cause:** entry 1's: the activation estimated rather than computed.
  The rounding makes 8 bytes of parameters (9) and 12 bytes (10) differ.
- **Sweep:** every activation in `Harness/*.lean` recomputed from the
  formula; all others match, and the harness reports each as exact.
  Costs are now written with the parameter bytes in their comment.
- **Test added:** the existing cost check; no new input needed.


### 7. Parser rejection cost could exceed its own gas ceiling

- **Statement:** `FromSliceSpec.RejectContract` quantified `∀ Cg, ∃ K` before
  specifying a normal rejecting run from `credits Cg (K + R)`.
- **Truth:** the cost must be independent of `Cg`: `∃ K, ∀ Cg`. Otherwise
  `K = Cg + 1` makes the credits impossible and proves any postcondition.
- **Caught by:** review, followed by a successful Lean LSP proof of the entire
  old `RejectContract S` from that contradiction, without using parser behavior.
- **Root cause:** “some finite cost” was chosen inside the resource ceiling's
  quantifier, whereas the raised-limit comparison needs a fixed cost first.
- **Sweep:** searched all Bridge `RejectContract`, `f65_reject` and existential
  `K` declarations. The wrapper `f65_reject` had the same ordering; both are
  strengthened. The accepting contract already fixes its cost independently.
- **Validation:** the original exploit was kernel checked in a standalone LSP
  snippet. The strengthened wrapper is checked against the uniform contract;
  runtime scenarios cannot detect this logical quantifier error.

### 8. The all-outcome string bound cannot close the accepting linear bound

- **Statement:** the M6 continuation planned a closed linear bound on the existing
  `ParseStr.costRun` to integrate escaped accepting inputs.
- **Truth:** `costRun` is a valid but excessively loose all-outcome bound. On `n`
  valid newline escapes followed by a quote, its value is at least
  `(800*n*n + 3400*n) * regularOpCost`, with input length `2*n + 1`.
  Each escape reserves eight whole-input error-position scans, even when it
  succeeds. This quadratic expression cannot supply the intended linear bound.
  It does not imply quadratic gas consumption by the binary.
- **Caught by:** inspection of `StrCost` followed by the kernel-checked
  `StrCostLower.costRun_newlineEscapes_quadratic` witness. `newlineEscapes_model`
  and `newlineEscapes_utf8` prove the witness strings are accepted by the model.
- **Root cause:** reusing contracts that reserve both successful and rejecting
  paths, and charging final UTF-8 validation in every segment, loses the actual
  accepting path's cost structure.
- **Sweep:** successful byte and hex readers get contracts without error reserves
  (`SerdeEscSuccess`). The successful escape paths use those contracts in
  `ParseEscapeSuccess`; the old general contracts remain valid and unchanged.
  The outer string loop still needs a success-specific cost and a bound on
  amortized scratch growth, then integration into the argument contracts.
- **Validation:** the cost lower bound and accepting witness are formal Lean
  results. No model gas bound or semantics is changed.

### 9. One object bound predicate lost the one-time String allocation

- **Statement:** the first draft of `SerdeStructObjKeyState.member` used one
  reachable-state bound `B` both before and after saving `account_id`;
  `ValueConditions` consequently required a pure `B → B` allocation closure.
- **Truth:** the control proof permits one account-id allocation. The pure
  resource bounds must distinguish the state before that allocation from the
  state after it. Otherwise composing the pure closure can demand room for
  hypothetical repeated String allocations, even though the loop rejects a
  duplicate account field. The conditional Hoare theorem was true, but its
  proposed quantitative interface was too strong for the intended use.
- **Caught by:** interface review before publishing the changing-state loop,
  after the first draft passed the kernel and axiom audit.
- **Root cause:** the separation-logic member state tracked `seen`, but its pure
  bound predicate erased that distinction and charged the one-time copy as a
  repeatable transition.
- **Sweep:** `member` now selects `B` or `Bsaved`; keys preserve either phase,
  values move only from `B` to `Bsaved`, and cursor monotonicity is required for
  each separately. The concrete key/value adapters and assembled object theorem
  use that distinction. The generic object control proof is unchanged.
- **Validation:** Lean MCP checks the revised assembled theorem and adapters.
  The quantitative bounds themselves remain open; runtime scenarios cannot
  validate this interface issue.

### 10. Reachable length bounds were asked to imply alignment on an interval

- **Statement:** the object adapter's first resource-closure draft required `B`
  for every memory length in its growth interval, while `KeyConditions` and
  `ValueConditions` demanded allocation room from `B` alone. Room includes
  page alignment, so the combined interface could require alignment at `hl + 1`.
- **Truth:** pure budget bounds can hold across a length interval; allocator
  alignment and positivity belong to the actual heap. The room conditions must
  receive those physical facts as explicit premises, derived from `heapInv`.
- **Caught by:** interface review before publication. The kernel-checked
  `alignment_not_interval` witness shows that an aligned length cannot have an
  entirely aligned interval through `hl + 65536`.
- **Root cause:** mixing physical heap well-formedness with an interval-closed
  upper-bound predicate. A conditional theorem can pass the kernel while its
  proposed premises are unusable at real call sites.
- **Sweep:** both key and value conditions now take alignment and positivity
  separately. `scratch_alignment` reads those facts from the actual allocator
  invariant without consuming scratch; both concrete adapters supply them.
  The growth-closure predicates no longer need to imply alignment.
- **Validation:** Lean MCP checks the witness, allocator extraction and revised
  adapters; the package audit checks the assembled theorem. Runtime tests do
  not validate this quantified resource interface.

### 11. The ignored reader lacked its literal data and transitive code

- **Statement:** the first assembled object interface supplied only the key/value
  reader code bundle and a member state without `SerdeIdent.identBytes`.
- **Truth:** ignored `true`/`false`/`null` values need the literal table; the
  ignored-value implementation also calls functions outside that code bundle.
  Its conditional hypothesis therefore needs both resources to be usable.
- **Caught by:** ownership and callee review before publishing the object loop.
- **Root cause:** generalizing the loop's changing heap state while overlooking
  read-only resources of the remaining reader. Kernel checking validates the
  implication but does not establish its premises at a concrete call site.
- **Sweep:** `core` retains the literal table; key/value adapters frame it through.
  The assembled theorem accepts an additional persistent context, shared by all
  reader hypotheses, for the ignored reader's transitive code dependencies.
- **Validation:** Lean MCP checks the revised adapters and assembled theorem;
  the complete audit checks their compiled declarations. Discharging the ignored
  reader itself remains open.

## Agent results

Success and failure per task type and model (section 11.2 of the plan), used
to move task types to a cheaper or stronger model.

| Task type | Model | Succeeded | Failed | Notes |
|---|---|---|---|---|
| Harness design and first checkers (M1) | Opus | 1 | 0 | Two cost miscounts, caught by the harness itself |
