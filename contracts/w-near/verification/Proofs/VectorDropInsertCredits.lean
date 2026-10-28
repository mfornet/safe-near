import Proofs.VectorDropInsertResources
import Proofs.VectorDropInsert237Credits

/-! Exact whole-wrapper residual credits for positive vector destruction. -/
namespace WNear.Proofs.VectorDropInsert
open Wasm Wasm.Near MeteredLogic
open VectorDropPositive
open WNear.Proofs.VectorDrop

def bodyAfter(s:Store NearState)(op:Nat)(q:DeallocateCore.Layout):=
  chargedStore (VectorDropInsert237.callAfter (before237 s op) op q) op
def callAfter(s:Store NearState)(op:Nat)(q:DeallocateCore.Layout):=bodyAfter (entered s op) op q

theorem bodyAfter_credits (s : Store NearState) (op rest : Nat) (q : DeallocateCore.Layout)
    (hc : s.host.gas.Credits (220 * op + rest)) : (bodyAfter s op q).host.gas.Credits rest := by
  have cp := before237_credits s op (158 * op + rest) (hc.mono (by omega))
  have cd := VectorDropInsert237.callAfter_credits (before237 s op) op (op + rest) q (cp.mono (by omega))
  exact StorePair.charged_credits (VectorDropInsert237.callAfter (before237 s op) op q) op rest cd

theorem callAfter_credits (s : Store NearState) (op rest : Nat) (q : DeallocateCore.Layout)
    (hc : s.host.gas.Credits (230 * op + rest)) : (callAfter s op q).host.gas.Credits rest :=
  bodyAfter_credits (entered s op) op rest q (entered_credits s op (220 * op + rest) (hc.mono (by omega)))
end WNear.Proofs.VectorDropInsert
