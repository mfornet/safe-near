# WASM Runtime

`near-lean/wasm` contains the adapted Talos interpreter, and
`near-lean/iris-wasm` contains its Iris proof machinery. The interpreter executes
Wasm with a configurable host; the NEAR host and metered single-call executor
live in `near-lean/vm`.

The official Wasm testsuite and custom tests exercise the interpreter. The
committed `testsuite_report.txt` records the tested results and is checked in CI.
VM conformance tests compare supported NEAR execution with a pinned reference.

Broader fuzzing, interchangeability with other Wasm runtimes, and tests derived
from NEAR execution history remain validation goals. Full compatibility must be
established for each supported feature rather than inferred from passing a
finite testsuite. Performance is secondary to an auditable execution model.
