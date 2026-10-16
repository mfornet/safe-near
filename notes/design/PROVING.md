# Proving

Once we have the contracts and the statements, we just need to scale theorem proving,
This might be the most expensive part of the system, so we need to make it as cheap 
as possible. 

This part requires little trust, once the proof is finalized, for that we should use
state of the art tools in LEAN to verify the final proofs. 

- Lean Kernel using accepted three axioms (no sorry and no native decide)
- Comparator in strict mode

Note this is only needed at the very end of the verification, during the development
of the proof we can use fastart and "trusted" tools.
