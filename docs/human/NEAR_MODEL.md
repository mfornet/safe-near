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

We can add to the NEAR Runtime model full access keys and function
call keys, so that theorems should explicitly account for that.
In particular if a smart contract has a full access key it means
it can be upgraded at any time chaning its behavior in unexpected
ways. We should be carefult about this, since we don't want to
the hypothesis that the contract doesn't have any full access key
potentially invalidating the whole theorem in case it has, instead
we should capture what could happen.

## Smart contract Upgrade

TODO: Discuss how to deal when a smart contract is updadted.
