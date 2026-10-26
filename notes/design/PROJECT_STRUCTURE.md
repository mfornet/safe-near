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
    contracts/
      CATALOG.md        -- List of contracts
      <name>/           -- One deployed binary (see SMART_CONTRACTS.md)
        verification/   -- Lean project: Model/, Spec/, Proofs/, blueprint/
```

Generated blueprint HTML goes to `verification/blueprint/web/`. Contracts
without a leanblueprint yet keep a hand-written proof index in
`verification/blueprint/README.md` instead (see PROVING.md).
