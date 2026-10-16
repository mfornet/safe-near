# TODO

- Bring Talos to NEAR, not as a submodule, just as a runtime
    - Bring the iris-lean machinery
    - Let's have an easy way to run the whole testsuite and understand where we are right now
    - Setup mergesort as a test to be solved by a harness

- Create NEAR Runtime (requires discussion about the interfaces / boundaries)
- Simplify Talos as much as possible, remove features that we don't need, etc...

- Setup linter and formatter in CI for lean
- Enforce that every LEAN package uses the same LEAN toolchain / version

- Tool to download a partial snapshot of the NEAR blockchain such that we can run
  the runtime against real smart contracts on the blockchain. This will be the basis of the
  tests for NEAR runtime.

- NEAR Runtime testing harness: We should have infrastructure similar to near-workspaces,
  where we can start a trusted chain with some state including some contracts deployed and
  then run some actions there, if new receipts are generated we should let the chain apply
  those receipts one after the other in custom block and then check the results matches
  exactly what happened on NEAR.

