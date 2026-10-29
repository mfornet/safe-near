# Proving

## Blueprint

`@[blueprint]` annotations ([LeanArchitect](https://github.com/hanwenzhu/LeanArchitect))
and [leanblueprint](https://github.com/PatrickMassot/leanblueprint) link prose,
statements and proofs. Build with `just blueprint w-near`. The blueprint must
show open obligations as open: stating a property is not proving it.

Only w-near has a leanblueprint so far. The `blueprint/` folders of
`sputnik-dao-factory` and `sputnikdao2-v3.2` hold a hand-written proof index
(`blueprint/README.md`: statement, evidence, status) and `just blueprint`
does not build them. The same rule applies: an index row is `proved` only
when the named declaration passes the checks below.

## What counts as proved

- Checked by the Lean kernel.
- Only the axioms `propext`, `Classical.choice` and `Quot.sound`.
- No `sorryAx` and no `native_decide`.

`just wnear-audit` checks this transitively for every wNEAR declaration, and
`just sorries <contract>` lists what is still open. Automation and exploratory
tools are fine during development, as long as the result passes these checks.

A proof also counts only for the statement we reviewed. A contract's
`verification/statements.json` names the modules and theorems that state what
is proved (for wNEAR: `Spec`, the interface's `ContractModel` and `Refines`,
and the theorem that closes each spec), and `verification/STATEMENTS.md`
holds each of those statements as Lean prints it, with a hash of its terms.
The audit fails when the build differs from that file, so weakening a
statement, for example with an extra hypothesis the proof never uses, cannot
pass as a proof fix: the pull request must regenerate the file
(`just wnear-pin-statements`), and the change shows in its diff. The `wNEAR`
workflow runs this audit on every pull request that can reach the proofs.

## Before proving a refinement

Stress the statement before trying to prove it. Differential scenarios run
the deployed binary on near-lean and the model on the same timelines of
receipts, and check every step against `Refines`. A discrepancy means the
model or the statement is wrong, and finding one costs seconds instead of a
failed proof. The `refinement-stress` skill (`.claude/skills/refinement-stress`)
runs such a round. wNEAR's harness is in
`contracts/w-near/verification/Differential` and `scenarios/`; its first
rounds fixed five model gaps (`scenarios/README.md`). Passing scenarios
build trust; they prove nothing.

## Open

- A stricter final check with Comparator is proposed but not set up yet.
- Making proofs cheaper to write without making statements harder to audit.
