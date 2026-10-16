import Programs.GcdStdio.Spec

/-!
# Correctness of the compiled GCD stream

Statements only: the proofs are not ported from Talos and are left as `sorry`.
Upstream proves `kernel_correct` by transporting the verified `num-integer`
Stein kernel across a body equality, and `gcd_correct` through an adequacy
bridge from a separation-logic driver proof.
-/

namespace Programs.GcdStdio.Proof

@[proves Programs.GcdStdio.Spec.KernelSpecification]
theorem kernel_correct : Programs.GcdStdio.Spec.KernelSpecification := by
  sorry

@[proves Programs.GcdStdio.Spec.PublicEntrySpecification]
theorem gcd_correct : Programs.GcdStdio.Spec.PublicEntrySpecification := by
  sorry

end Programs.GcdStdio.Proof
