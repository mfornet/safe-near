import Proofs.VectorDropPositiveResources
import Proofs.VectorDropPositive237Credits

/-! Exact whole-wrapper residual credits for positive vector destruction. -/
namespace WNear.Proofs.VectorDropPositive
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.VectorDrop

theorem bodyAfter_credits (s : Store NearState) (op rest : Nat) (q : DeallocateCore.Layout)
    (hc : s.host.gas.Credits (309 * op + rest)) : (bodyAfter s op q).host.gas.Credits rest := by
  have cp := before237_credits s op (247 * op + rest) (hc.mono (by omega))
  have cd := VectorDropPositive237.callAfter_credits (before237 s op) op (op + rest) q (cp.mono (by omega))
  exact StorePair.charged_credits (VectorDropPositive237.callAfter (before237 s op) op q) op rest cd

theorem callAfter_credits (s : Store NearState) (op rest : Nat) (q : DeallocateCore.Layout)
    (hc : s.host.gas.Credits (319 * op + rest)) : (callAfter s op q).host.gas.Credits rest :=
  bodyAfter_credits (entered s op) op rest q (entered_credits s op (309 * op + rest) (hc.mono (by omega)))
end WNear.Proofs.VectorDropPositive
