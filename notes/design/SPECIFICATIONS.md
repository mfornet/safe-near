# Specifications

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
