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

## Open

- A stricter final check with Comparator is proposed but not set up yet.
- Making proofs cheaper to write without making statements harder to audit.
