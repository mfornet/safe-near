# Proving

Verification uses LeanArchitect `@[blueprint]` annotations and leanblueprint to
connect explanations, formal statements, and proofs. Build the wNEAR blueprint
with `just blueprint w-near`. The blueprint must show open obligations as open;
a definition of a property is not a proof of it.

Theorem proving can use automation and exploratory tools during development,
but completed proofs must be checked by the Lean kernel. The accepted logical
axioms are `propext`, `Classical.choice`, and `Quot.sound`; completed verification
must not depend on `sorryAx` or `native_decide`. The transitive axiom audit
(`just wnear-audit`) checks proof dependencies. The programs package has known
open proofs recorded in periodic reports; these are not completed verification.

Strict Comparator checking remains a proposed additional final check until a
pinned integration and repository command exist. It is not currently enforced.

Scaling proof development should reduce cost while keeping statements, model
assumptions, and trusted dependencies auditable.

Tooling references:

- [leanblueprint](https://github.com/PatrickMassot/leanblueprint)
- [LeanArchitect](https://github.com/hanwenzhu/LeanArchitect)
