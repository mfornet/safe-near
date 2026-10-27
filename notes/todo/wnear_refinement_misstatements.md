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

## Agent results

Success and failure per task type and model (section 11.2 of the plan), used
to move task types to a cheaper or stronger model.

| Task type | Model | Succeeded | Failed | Notes |
|---|---|---|---|---|
| Harness design and first checkers (M1) | Opus | 1 | 0 | Two cost miscounts, caught by the harness itself |
