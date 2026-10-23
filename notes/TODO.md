# TODO

Done so far: our own Wasm runtime passes the Wasm testsuite; the VM, runtime
and chain layers run on it with nearcore conformance harnesses.

## Runtime

- Complete runtime semantic coverage and conformance against nearcore.
- Prove compositional runtime/chain invariants.
- Extend scenario and conformance harnesses to real-chain snapshots and full
  scheduling equivalence, towards a near-workspaces-style test environment.
- Extend the snapshot downloader to more account features and deployed contracts.
- Exact historical replay from complete archived chunks ([replay_near_history.md](todo/replay_near_history.md)).

## Contracts

- Prove the wNEAR refinement (`Refines`): the binary behaves as the model.
- Decide how to handle contract upgrades ([NEAR model](design/NEAR_MODEL.md)).

## Wasm runtime

- `near-lean/wasm-logic`, next milestone: Iris-Wasm's `stack_map_trap.v`,
  its logical relation and robust safety, host reentrancy; rules for
  overlapping `memory.copy`/`table.copy`, zero-length bulk operations and
  out-of-bounds traps; the independent clean-room review of the logic
  ([wasm_logic_iris.md](todo/wasm_logic_iris.md) §5).
- Close the model gaps listed in [Wasm runtime](design/WASM_RUNTIME.md): start
  functions, exported imports, nearcore's stack limiter.

## Code health

- Extend Lean style and formatting enforcement as packages evolve.
