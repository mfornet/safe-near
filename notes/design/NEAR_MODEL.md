# NEAR model

How contract state and the environment are presented to specifications.

## State view

Each contract has a function from its raw storage (key/value bytes in the host)
to a high-level Lean view of its state. Specifications talk about the view, so
the function is audited once per contract.

The view should be bijective: it captures everything in storage, so the raw
state can be reconstructed and nothing is left out. For wNEAR this is
`encode`/`project` in `Model/Storage.lean`, with `project (encode s) = some s`
proved.

## Access keys

The runtime models full-access and function-call access keys. Full-access keys
can deploy new code, so lifetime properties must state assumptions about keys
and deployment. A theorem about one pinned binary says nothing about later
upgrades.

## Upgrades

Open: how to state and prove properties across a contract upgrade.
