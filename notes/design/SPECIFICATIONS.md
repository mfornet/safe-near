# Specifications

Create a clean way to write statements / specifications about the smart contracts.
These will be the statements (once proven) that will be treated as the evidence of
the correctness of the smart contracts. This mean that the statements should have
small overhead to be understood (easily auditable by humans) and the dependencies
(definitions) used should be as easy to audit as possible.

We can develop a common library of definitions to use for writing specifications
(maybe NEAR Runtime library) is enough. One important feature for this library is
that we should not grow it often, since it will be part of the trusted base, and
we should always have an available audit of the latest version. I imagine that a lot
of common machinery like parsing json, data structures defined on near-sdk and 
other used libraries will belong here.

## Current layout and tooling

The wNEAR formalization lives in `contracts/w-near/verification/`:

```text
verification/
    lakefile.toml
    Model/          -- Definitions needed to state contract properties
    Spec/           -- Properties, generally defined as def ... : Prop
    Proofs/         -- Separate theorems proving those properties
    blueprint/      -- Explanations and links to formal statements and proofs
```

LeanArchitect extracts annotated statements and proof dependencies into the
blueprint, rendered with `just blueprint w-near`. The transitive axiom audit
(`just wnear-audit`) checks the trust dependencies of completed proofs. A
formalized statement does not by itself mean the property has been proved;
blueprint proof status must distinguish the two.

The specification format and shared vocabulary still need refinement as more
contracts are verified. Keep statements independently auditable and make any
model assumptions explicit.
