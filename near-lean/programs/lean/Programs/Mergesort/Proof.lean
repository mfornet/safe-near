import Programs.Mergesort.Spec

/-!
# Correctness of `mergesort`

Statement only: the proof is not ported from Talos and is left as `sorry`.
Upstream composes separation-logic contracts for the driver, Vec and allocator
functions (about 18k lines) and bridges them to the public statement through a
partial-adequacy theorem.
-/

namespace Programs.Mergesort.Proof

@[proves Programs.Mergesort.Spec.PublicEntrySpecification]
theorem mergesort_correct : Programs.Mergesort.Spec.PublicEntrySpecification := by
  sorry

end Programs.Mergesort.Proof
