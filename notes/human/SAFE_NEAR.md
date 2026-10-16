# Safe NEAR

This is the plan to formally verify NEAR Smart Contract using LEAN.

This project will be developed aggresively using AI but we want to 
make sure we are not making any stupid move along the way hard to audit.
In this regard the main idea is that we will split the project in 
components with clear responsibilities and boundaries, such that each
of them can audited or replaced indepdendently from each other.

The previous point is also linked to the idea of maintaining clarity
about the trusted base at every point, which pieces of code needed to be
trusted, and what are the current and future efforts to make sure we
can actually trust them.

Next we describe some of the components that we are going to use:

## WASM Runtime

> There is partial work that we can use here: https://github.com/cajal-technologies/talos)

WASM Runtime is responsible to running arbitrary WASM code over some custom
defined host. 

We can build trust in our implementation about the WASM Runtime by running
official and custom made wasm testsuite. There is a comprehensive wasm
testsuite, and we can extract all history of NEAR blockchain into a
testsuite and compare that our Runtime (+Host) produce the same outcome
as the official one.

Interface: This implementation should have the same ability as any other
wasm runtime such as wasmtime or wasmer and should allow for a plug&play
replacement in most scenarios, even if sometime is not feasible since
out implementation doesn't need to be as performant as others. This should
allows us to run as many fuzz tests as possible.

## NEAR Runtime

The former WASM Runtime is generic over hosts, and in particular we will
need to have a detailed model of the NEAR Runtime such that we can replay
all NEAR history and validate that we get to the same state.

In particular this will require modeling all host functions that are
exposed to the smart contracts, the internal state representation in a way
that is as rich as the NEAR blockchain, it doesn't need to be as efficient
and details of the implementations doesn't really matter as long as we can
replicate to the bit granularity all actions in our runtime vs NEAR runtime.

We will need to model receipts, to deal with promises and callbacks, contract
and account state, gas accounting, Runtime upgrades (such that the behavior
of the runtime can change over time).

Not covered in the NEAR Runtime is all cryptographic verification (check signer,
predecessor_account_id, etc...), this is a trusted runtime that needs to be
orchestrated by a trustless manipulator, so nothing about consensus, and most
parts of the chain are not modeled here, all data is externally provided and
trusted.

This opens the door to test it by creating rust shims over our implementation
and try to plug this runtime inside nearcore, and replay all the history verified
using a patched version of nearcore that uses our runtime. This could be also
an step towards building nearcore in LEAN.

Interface: Runtime implementation that can be plugged inside the NEAR runtime
replacing it by whatever there is there (requires some investigation to see
how decoupled is the runtime inside nearcore). Even if it is not decoupled
we can have a parallel implementation of nearcore that we can run next to the
official one and we use exactly for this purpose.

There was some previous effort at: https://github.com/cajal-technologies/NEAR-lean/

### Questions

Is it true that after we schedule any callback that will always be triggered
despite if the intermediate results are executed succesfully or not.

## Smart Contracts

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

## Specifications

Create a clean way to write statements / specifications about the smart contracts.
These will be the statements (once proven) that will be treated as the evidence of
the correctness of the smart contracts. This mean that the statements should have
small overhead to be understood (easily auditable by humans) and the dependencies
(definitions) used should be as easy to audit as possible.

We can develop a common library of definitions to use for writing specifications
(maybe NEAR Runtime library) is enough. One important feature for this library is
that we should not grow it often, since it will be part of the trusted base, and
we should always have an available audit of the latest version. I imagine that a lot
of common machinery like parsing json, data structures defined on near-sdk and 
other used libraries will belong here.

TODO: Discuss in more details (with example the format of the specifications)

Each formalization task will be a LEAN project with the following structure:

smart-contract-lean/
    task/           -- A copy (or link) to the task defined in SmartContract section
    lakefile.toml   -- This is a LEAN Project (that can be built)
    Specs/.lean     -- Multiple file containing all properties that we want to prove 
    Proofs/.lean    -- A mirror of specs, for each spec the theorem that proves it.

The goal of the previous structure is to have specs in a common place which makes it
easy for auditors and automated tools to verify the state of a project. We can have
a tool that extract all specs automatically from this repo and shows which one have
been proven and which ones are not prove yet.

## Proving

Once we have the contracts and the statements, we just need to scale theorem proving,
This might be the most expensive part of the system, so we need to make it as cheap 
as possible. 

This part requires little trust, once the proof is finalized, for that we should use
state of the art tools in LEAN to verify the final proofs. 

- Lean Kernel using accepted three axioms (no sorry and no native decide)
- Comparator in strict mode

Note this is only needed at the very end of the verification, during the development
of the proof we can use fastart and "trusted" tools.

## Future work

Theorems that span multiple contracts simultaneously (do we really need this?)
