# Linkdrop proof index

The trust gate is Lean kernel checking plus the transitive axiom audit allowing
only `propext`, `Classical.choice`, and `Quot.sound`. No deployed refinement is
claimed. This index records checked theorem names and unproved boundaries.

| Specification | Theorem / file | Status |
|---|---|---|
| `InvPreserved` | `Linkdrop.invPreserved`, `Proofs/Safety.lean` | proved |
| `PrivateAuthorization` | `privateAuthorization`, Safety | proved |
| `MapAuthorization` | `mapAuthorization`, Safety | proved under State.WF |
| `ViewsPure`, `InitOnce`, `ReturnSelection`, `CallbackArity` | matching lowerCamelCase theorems, Safety | proved |
| `SendAvailable`, `SendCreditBound`, `ClaimAvailable` | matching lowerCamelCase theorems, `Proofs/Economics.lean` | proved |
| `FailedClaimRestore`, `FailedCreationRefund`, `AdvancedValidation` | matching lowerCamelCase theorems, Economics | proved |
| `SendConservation`, `ClaimConservation`, `RestoreConservation` | matching lowerCamelCase theorems, `Proofs/Liability.lean` | proved |
| Successful model trace invariants | `reachable_invariants`, `Proofs/Reachability.lean` | proved |
| Intervening deposits are preserved | `failed_callback_overwrites_topup`, `Proofs/Interleavings.lean` | false in model; witness checked |
| Map balance implies a claim key exists | `successful_callback_deletes_topped_up_key`, Interleavings | unsupported; witness checked |
| Header/record byte sizes | `Proofs/Storage.lean` | proved for specified encoding |
| Logical state uniqueness / projection round trip | `represents_unique`, `project_encode`, `Proofs/Projection.lean` | proved under LayoutValid |
| Physical layout compatible with SDK execution | `Storage.Represents` relation | open |
| Concrete Wasm behavior equals model | `Spec.RefinesTypedExecution`, `Spec/Refinement.lean` | stated; no runtime instance |
| Whole-chain solvency and progress | constraints in verification README | open, not formalized |

Dependency order: Types → State → Methods → Safety lemmas; Safety → Economics
and reachability; Economics → liability lemmas and interleaving witnesses.
Storage sizing depends only on State and the source-derived layout encoder.
The runtime obligation consumes these interfaces but is not assumed by any proof.
