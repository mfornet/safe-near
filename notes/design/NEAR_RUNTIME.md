# NEAR Runtime

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

## Interface and implementation

NearRuntime
    WasmRuntime
    NearHost

NearRuntime is the main abstraction that we use to run transactions, using the
wasm runtime, and always passing the current host state, and getting back the
modified host state.

Between txs we can modify the host state (for example to increase block height,
    or update the state in any other way)

The program orchestrating the NearRuntime is responsible for synchrounously
executing transactions.

## Questions

Is it true that after we schedule any callback that will always be triggered
despite if the intermediate results are executed succesfully or not.
