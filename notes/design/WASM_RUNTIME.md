# Wasm runtime

`near-lean/wasm` is a WebAssembly runtime written in Lean from the core
specification. It is our own code (no Talos, no AGPL), kept small by
implementing exactly the features nearcore enables: the MVP, mutable globals,
sign extension, saturating truncation, floats with canonical NaNs, reference
types and bulk memory. Multi-value is implemented for the spec testsuite and
switched off in the NEAR feature set. SIMD, threads, tail calls, multi-memory,
memory64, exceptions, GC and function references are rejected as unsupported,
distinct from malformed.

## Shape

- One deterministic executable step, `Wasm.Exec.step`. The relation proofs use
  (`Step`, `Steps`) is defined from it, so nothing has to be kept in sync and
  determinism is free.
- Hosts are generic: a host function sees its own state and the calling
  module's memory. Hosts are name-keyed modules whose exports imports resolve
  to, exactly like Wasm modules, so several hosts and several module instances
  link in one store.
- `Wasm.HostInvariant` proves once that a step preserves any host-state
  predicate the host functions preserve (strict and live variants), and
  `Wasm.LinkInvariant` that instantiation keeps the host state and adds no host
  function. The NEAR runtime's invariants are instances of these.
- Input is `.wasm` bytes. There is no WAT parser in Lean; tests compile `.wat`
  with the pinned `wasm-tools` at run time (`Wasm.Wat.compile`).
- Floats are bit patterns operated on through Lean's `Float32` / `Float`; those
  operations are opaque to the kernel and covered by the testsuite.

## Testing

The official spec testsuite is the primary signal: `testsuite_report.txt`
records one outcome per command, CI regenerates it and fails on drift, and
`testsuite_out_of_scope.txt` lists whole files outside scope. Every in-scope
command passes; see `near-lean/wasm/README.md` for the numbers. Compatibility
with nearcore is checked at the `NearVM.run` boundary by the conformance
harness ([NEAR runtime](NEAR_RUNTIME.md)).

Passing a finite testsuite does not prove compatibility; each supported feature
must be validated. Fuzzing and tests from NEAR history are future work.
Auditability matters more than performance.

## Proofs about Wasm code

`near-lean/wasm-logic` is an iris-lean separation logic over `Wasm.Exec.step`:
the machine as a `Language`, weakest-precondition rules from store ownership
(one step, or a whole finishing run), adequacy back to `Exec.run`, and a
worked example. Its resource is the whole store; points-to assertions over
memory, locals and globals are future work.

## Known model gaps

- A start function is rejected as unsupported; nearcore runs it as a metered
  export before the method. No contract in the dataset has one.
- Exporting an imported function under a method name is rejected as
  unsupported.
- nearcore's stack limiter is not modelled; recursion traps at a fixed call
  depth (`NearVM.execLimits`).
