# Sequential dataset formalization

The unit of work is one pinned dataset entry. For each entry: inspect the pinned
source and resolved SDK; model all explicit entry points and their actual guards;
identify security, accounting, authorization, callback and liveness constraints;
prove valid model properties; record counterexamples to stronger claims; describe
storage; audit proofs; then connect the model to concrete Wasm/runtime behavior.
Model proof completion and deployed refinement must remain separate statuses.

## Current status (2026-10-22)

| Entry | State |
|---|---|
| w-near | Existing completed model proofs; concrete runtime refinement stated and open |
| [linkdrop](linkdrop/verification/README.md) | Source model and safety/liability proofs checked; storage layout, sizes and mathematical projection round trip proved; concrete adapter and deployed refinement open |
| [sputnik-dao-factory](sputnik-dao-factory/verification/README.md) | In progress: all 18 methods modeled on one raw trie; namespace alias witness, conditional DAO/metadata layouts, raw-key uniqueness, owner gate, receipt, store/delete rollback paths proved in the model; source and deployed refinement open |
| [sputnikdao2-v3.2](sputnikdao2-v3.2/verification/README.md) | In progress: all 34 named exports have checked projections; policy/status/authorization, proposal/bounty/delegation/blob storage effects, views, upgrade and migration are modeled, with selected governance vote/finalize traces and raw-key refinements. Several action branches, a whole-contract dispatcher, and concrete Wasm/runtime refinement remain open. |
| ref-farming | Queued: reward-per-share arithmetic/rounding, seed custody, claim/withdraw callbacks and storage liabilities |
| skyward | Queued: auction/time accounting, pro-rata rounding, token trust, treasury authority and promise failures |
| eth2-client | Queued: trusted initialization, cryptographic validation, finality/committee transitions and pruning |
| omni-bridge | Queued: proof/signature trust, replay protection, nonce/fee accounting, cross-chain asset custody and delayed messages |
| intents-defuse | Queued: signatures/nonces, domain separation, authorization, multi-token conservation and asynchronous withdrawal |
| mpc-contract | Queued: membership/quorums, protocol state transitions, request/response binding, timeout/refund and external crypto assumptions |
| aurora-engine | Queued: EVM semantics, transaction authentication/replay, gas and balance accounting, bridge and cross-contract boundaries |

This order starts with smaller interfaces and shared factory/DAO semantics before
the larger protocol engines. It is a queue, not a claim that queued contracts have
been analyzed or proved. The dataset scope is the ten pinned, reproduced entries
besides w-near; pending catalog entries are outside the current pass.

The current linkdrop package is smaller than w-near's verification: all ten
explicit methods are modeled and model proofs are audited, but it has no concrete
VM adapter yet. The mathematical storage projection round trip is now proved.
The shared runtime lacks five imports used by this binary; this concrete gap
remains part of the overall goal and must not be presented as deployed coverage.
The next contract can undergo source/storage analysis while this shared runtime
work remains explicitly open; no contract is marked fully verified on that basis.

## Checks

`just build <contract>` builds an individual package. `just audit
contracts/<contract>/verification` performs the strict transitive axiom audit.
The periodic-check plan discovers additional verification projects and schedules
their build before their audit. Discovery does not imply a deployed proof.
