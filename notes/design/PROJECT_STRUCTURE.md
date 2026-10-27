# Project structure

```text
safe-near/
    notes/              -- Design notes, TODO and finished plans (history/)
    tools/              -- Conformance, snapshots, audits and Lean quality tools
    reports/periodic/   -- Periodic check ledger (reports are in Linear)
    lean-toolchain      -- Lean version shared by every package
    near-lean/
      wasm/             -- Wasm runtime, written from the spec, tested on the official testsuite
      wasm-logic/       -- separation logic over the runtime's step (iris-lean)
      interface/        -- Shared vocabulary and the refinement statement (NearInterface)
      vm/               -- Single contract call: metering and host functions
      runtime/          -- Transactions, receipts and account state
      chain/            -- Block execution and settlement
      sdk/              -- near-sdk layouts and NEP-141/145 assumptions, shared by contract projects
    contracts/
      CATALOG.md        -- List of contracts
      <name>/           -- One deployed binary (see SMART_CONTRACTS.md)
        verification/   -- Lean project: Model/, Spec/, Proofs/, blueprint/
```

Executable code and proofs share a package but not an import closure. A
package's umbrella module (`NearVM.lean`, ...) imports both and is only a
build target; every other module imports the modules it uses, so the test
executables and the runtime under a contract build the executable code alone
(`NearVM.Run`, `NearRuntime.Apply`). `just umbrella-imports` checks it.

Generated blueprint HTML goes to `verification/blueprint/web/`. Contracts
without a leanblueprint yet keep a hand-written proof index in
`verification/blueprint/README.md` instead (see PROVING.md).
