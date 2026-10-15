# TODO

- Setup linter and formatter in CI for lean
- Enforce that every LEAN package uses the same LEAN toolchain / version

- Bring Talos to NEAR, not as a submodule, just as a runtime
    - Let's have an easy way to run the whole testsuite and understand where we are right now

- Tool to download a partial snapshot of the NEAR blockchain such that we can run
  the runtime against real smart contracts on the blockchain. This will be the basis of the
  tests for NEAR runtime.

- NEAR Runtime testing harness: We should have infrastructure similar to near-workspaces,
  where we can start a trusted chain with some state including some contracts deployed and
  then run some actions there, if new receipts are generated we should let the chain apply
  those receipts one after the other in custom block and then check the results matches
  exactly what happened on NEAR.

