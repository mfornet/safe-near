import Programs.GcdStdio.Adequacy

/-!
# Correctness of the compiled GCD stream

The arithmetic kernel is proved in `KernelProof`. `Adequacy` connects the real
allocator, codec and host calls to its call-context contract and derives the
finite execution required by the unchanged public specification.
-/

namespace Programs.GcdStdio.Proof

@[proves Programs.GcdStdio.Spec.PublicEntrySpecification]
theorem gcd_correct : Programs.GcdStdio.Spec.PublicEntrySpecification :=
  Adequacy.entry_adequacy

end Programs.GcdStdio.Proof
