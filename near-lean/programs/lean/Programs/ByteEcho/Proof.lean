import Programs.ByteEcho.Spec

/-!
# Correctness of `byte_echo`

Statement only: the proof is not ported from Talos and is left as `sorry`.
-/

namespace Programs.ByteEcho.Proof

@[proves Programs.ByteEcho.Spec.ByteEchoSpec]
theorem byte_echo_correct : Programs.ByteEcho.Spec.ByteEchoSpec := by
  sorry

end Programs.ByteEcho.Proof
