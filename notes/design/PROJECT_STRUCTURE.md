# Project structure

```text
safe-near/
    notes/              -- Component design, verification policy and open tasks
    reports/periodic/   -- Dated check findings and validation evidence
    near-lean/
      wasm/             -- Adapted Talos Wasm interpreter
      iris-wasm/        -- Iris proof machinery and Wasm code library
      programs/         -- Wasm test programs, smoke harnesses and proofs
      vm/               -- Metered single-call execution and NEAR host functions
      runtime/          -- Transactions, receipts, account state and routing
      chain/            -- Block execution, settlement and reachability
    contracts/          -- Dataset of pinned smart contracts
      <name>/
        source/         -- Pinned upstream source submodule
        build.sh        -- Reproduce the contract from source
        build/          -- Reconstructed outputs, including contract.wasm
        contract.wasm   -- Pinned on-chain binary
        hash.txt        -- NEAR code hash of the pinned binary
        contract.toml   -- Provenance, build instructions and hash metadata
        verification/   -- Lean project, where verification is implemented
          lakefile.toml
          Model/        -- Contract model and supporting definitions
          Spec/         -- Property statements
          Proofs/       -- Proofs of those properties
          blueprint/    -- Blueprint source
```

The verification layout is currently instantiated for wNEAR. Generated blueprint
HTML lives in its verification project's `web/` directory.
