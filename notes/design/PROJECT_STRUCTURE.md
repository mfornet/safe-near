# Project structure

```text
safe-near/
    notes/              -- Design notes and TODO
    tools/              -- Conformance, snapshots, audits and Lean quality tools
    reports/periodic/   -- Dated periodic check reports
    lean-toolchain      -- Lean version shared by every package
    near-lean/
      wasm/             -- Wasm runtime, written from the spec, tested on the official testsuite
      wasm-logic/       -- separation logic over the runtime's step (iris-lean)
      vm/               -- Single contract call: metering and host functions
      runtime/          -- Transactions, receipts and account state
      chain/            -- Block execution and settlement
    contracts/
      CATALOG.md        -- List of contracts
      <name>/           -- One deployed binary (see SMART_CONTRACTS.md)
        verification/   -- Lean project: Model/, Spec/, Proofs/, blueprint/
```

Generated blueprint HTML goes to `verification/blueprint/web/`.
