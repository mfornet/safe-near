import Programs.ByteEcho.Spec
import Programs.ProofSupport.Cbv

/-!
# Correctness of `byte_echo`

The actual compiled export terminates after 85 small steps under the universal
host. Evaluation is symbolic in the input byte, including allocator and host
execution. The small-step soundness theorem removes fuel from the public result.
-/

namespace Programs.ByteEcho.Proof

open Wasm

private def initialConfig (input : Spec.Input) : SmallStep.Config Universal.State :=
  (startExportConfig? (Universal.envFor «module») «module» "byte_echo" (Spec.args input)).get (by rfl)

set_option Elab.async false in
@[proves Programs.ByteEcho.Spec.ByteEchoSpec]
theorem byte_echo_correct : Programs.ByteEcho.Spec.ByteEchoSpec := by
  intro input
  refine ⟨input.byte, ?_, rfl⟩
  unfold Spec.Runs Universal.RunsExport RunsExportWith
  refine ⟨initialConfig input, ?_, ?_⟩
  · rfl
  · apply SmallStep.runSteps_result_terminates (fuel := 85)
    program_cbv

end Programs.ByteEcho.Proof
