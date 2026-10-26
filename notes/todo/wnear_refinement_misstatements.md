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

None yet.

## Agent results

Success and failure per task type and model (section 11.2 of the plan), used
to move task types to a cheaper or stronger model.

| Task type | Model | Succeeded | Failed | Notes |
|---|---|---|---|---|
