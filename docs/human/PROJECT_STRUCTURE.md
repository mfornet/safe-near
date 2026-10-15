# Project structure

safe-near/
    docs/               -- Here is where all documentation lives. Documentation are markdown
                        -- files that can be built somehow. There is a clear separation
                        -- between human written vs AI written documents.
    near-lean/          -- This is the implementation of NEAR in LEAN, for now just focused
                        -- on the runtime and nothing more
      wasm/             -- This is a wasm interpreter, for now let's just bring talos here,
                        -- copy-pasted
      runtime/          -- NEAR Runtime, host plugged into wasm for running the NEAR runtime
      sdk/              -- Common definitions used by all contracts
    contracts/          -- Dataset of smart contracts that we want to verify
      name-1/
        source/         -- Original source code
        build.sh        -- Script to build the contract from the source code
        contract.wasm
        contract.toml   -- Metadata of the contract (hash, location in near blockchain,
                        -- meaining, the account id and block height at which it exists)
        verification/   -- This is a LEAN project 
          lakefile.toml
          model/        -- Common definitions about the smart contract
          spec/         -- Specification / Theorems that we want to prove
          proofs/       -- The actual proofs for each spec
          
