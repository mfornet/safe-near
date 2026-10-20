import NearVM.ResolvedEncoding
import NearVM.SuccessInvariant

namespace Wasm.Near

/-- Instruction and frame charges change no encoding field, even on failure. -/
theorem chargeWasm_encodingInvariant (config : SmallStep.Config NearState) (cost : Nat)
    (h : EncodingInvariant config.store.wasm.host) :
    EncodingInvariant (chargeWasm config cost).1.store.wasm.host := h

/-- Concrete host registry preservation composes with every checked interpreter
step and instruction/frame charge of a successful initialized run. -/
theorem runInitialized_outcome_encoding (cfg : WasmConfig) (fuel : Nat)
    (config : SmallStep.Config NearState) (ctx : VMContext) (storage : List (Bytes × Bytes))
    (h : ConfigLiveInvariant EncodingInvariant config)
    (hsuccess : (outcomeOfExecution ctx storage (runInitialized cfg fuel config).1
      (runInitialized cfg fuel config).2).aborted = none) :
    ∀ spec ∈ (outcomeOfExecution ctx storage (runInitialized cfg fuel config).1
      (runInitialized cfg fuel config).2).receipts, ReceiptEncoding spec.receiverId spec.actions := by
  have herr := outcomeOfExecution_success_error_none ctx storage _ _ hsuccess
  have hl := runInitialized_success_liveInvariant EncodingInvariant
    (fun config cost _ h => chargeWasm_encodingInvariant config cost h) cfg fuel config h herr
  have hf := outcomeOfExecution_success_live ctx storage _ _ hsuccess hl.2
  exact outcomeOfExecution_success_predicate ReceiptEncoding ctx storage _ _ hsuccess hf.2

end Wasm.Near
