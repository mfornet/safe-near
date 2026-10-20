import Programs.GcdStdio.KernelProof

/-!
# Correctness of the compiled GCD stream

The arithmetic kernel is proved in `KernelProof`. The public stream-driver
proof remains open; it must connect the actual allocator, codec and host calls
to that kernel without assuming its output.
-/

namespace Programs.GcdStdio.Proof

@[proves Programs.GcdStdio.Spec.PublicEntrySpecification]
theorem gcd_correct : Programs.GcdStdio.Spec.PublicEntrySpecification := by
  sorry

end Programs.GcdStdio.Proof
