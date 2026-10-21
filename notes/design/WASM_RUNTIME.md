# Wasm runtime

- `near-lean/wasm`: the Wasm interpreter, adapted from Talos. It runs with a
  configurable host.
- `near-lean/iris-wasm`: Iris proof machinery for reasoning about Wasm code.
- The NEAR host lives in `near-lean/vm` (see [NEAR runtime](NEAR_RUNTIME.md)).

The interpreter is tested with the official Wasm testsuite and custom tests.
`testsuite_report.txt` records the results and CI checks it is up to date.

Passing a finite testsuite does not prove compatibility; each supported feature
must be validated. Fuzzing and tests from NEAR history are future work.
Auditability matters more than performance.
