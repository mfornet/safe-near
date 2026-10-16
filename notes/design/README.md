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

- [WASM Runtime](WASM_RUNTIME.md)
- [NEAR Runtime](NEAR_RUNTIME.md)
- [Smart Contracts](SMART_CONTRACTS.md)
- [Specifications](SPECIFICATIONS.md)
- [Proving](PROVING.md)

## Future work

Theorems that span multiple contracts simultaneously (do we really need this?)
