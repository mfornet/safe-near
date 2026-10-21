# Project structure

```text
safe-near/
    notes/              -- Design notes and TODO
    tools/              -- Conformance, snapshots, audits and Lean quality tools
    reports/periodic/   -- Dated periodic check reports
    lean-toolchain      -- Lean version shared by every package
    near-lean/
      wasm/             -- Wasm interpreter (adapted from Talos)
      iris-wasm/        -- Iris proof machinery and Wasm code library
      programs/         -- Wasm test programs and their proofs
      vm/               -- Single contract call: metering and host functions
      runtime/          -- Transactions, receipts and account state
      chain/            -- Block execution and settlement
    contracts/
      CATALOG.md        -- List of contracts
      <name>/           -- One deployed binary (see SMART_CONTRACTS.md)
        verification/   -- Lean project: Model/, Spec/, Proofs/, blueprint/
```

Generated blueprint HTML goes to `verification/blueprint/web/`.
