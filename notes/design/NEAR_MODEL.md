# NEAR Model and specifications

Discussion on how the NEAR model should work and how to write
specifications for particular smart contracts.

## View

Per contract let's have a method that converts the state of the 
contract from the low level representation in the host to a higher
level view in Lean, this method needs to be audited once per
contract but provide a very clean way to talk about the internals
of the smart contract. Ideally this representation is bijective,
i.e it capture everything that can be capture from the state, so
it can be reconstructed later, and we are not leaving anything
behind.

## Keys

The runtime models full-access and restricted function-call access keys. Contract
specifications must account for the permissions that can change deployed code
or affect execution. Full-access keys can authorize upgrades, so lifetime and
upgrade-safety properties need explicit assumptions about deployment identity,
key permissions, and code changes. A theorem about one pinned binary must not
silently claim correctness of later upgrades.

## Smart contract Upgrade

TODO: Discuss how to deal when a smart contract is updated.
