# Smart Contracts

Our first goal is to formalize critical smart contracts on the NEAR blockchain,
and the first step is to identify and collect those smart contracts, including
source code (github repository), with the pinned version that was used to generate
the binary that is deployed on chain. I imagine that we will have multiple 
versions for some smart contracts (say multisig or dao) if there are different
versions deployed and in use. We should treat each of them independently even
if we later can reuse part of the formalization effort between them.

Interface: This is just a dataset, where we have source code, and how to build
the exact binary from the source code in a reproducible way, the actual binary
and its hash (useful to check exactly which version we are verifying).

There are several tiers on what we can verify:

1. Manually identified contracts that are considered critical in the NEAR ecosystem
2. Contracts that have had "significant" usage in the last month (year)
3. All smart contracts ever deployed

Let's consider finding potential point of contacts for each of the smart contracts
that could help us audit the formal statements that we are verifying.

Define the format of the dataset: 
One folder per problem containing:

smart-contract/
    src/            -- Source code
    contract.wasm   -- Binary deployed on chain
    hash.txt        -- Hash of the binary (use the same hash used in NEAR)
    build.sh        -- Reproducible script to re-build contract.wasm from src/
