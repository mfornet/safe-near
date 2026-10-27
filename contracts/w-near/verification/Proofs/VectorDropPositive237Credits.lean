import Proofs.VectorDropPositive237State
import Proofs.DeallocateCoreCredits

/-! Residual gas of the concrete f237 forwarder and nested allocator phases. -/
namespace WNear.Proofs.VectorDropPositive237
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)

theorem entered_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (11 * op + rest)) : (entered s op).host.gas.Credits rest :=
  StorePair.charged_credits (chargedStore s op) (10 * op) rest
    (StorePair.charged_credits s op (10 * op + rest) (hc.mono (by omega)))

theorem after_credits (s : Store NearState) (op rest : Nat) (p : DeallocateCore.Layout)
    (hc : s.host.gas.Credits (235 * op + rest)) : (after s op p).host.gas.Credits rest :=
  DeallocateCore.callAfter_credits (before582 s op) op rest p (paid_credits s op 4 _ (hc.mono (by omega)))

theorem callAfter_credits (s : Store NearState) (op rest : Nat) (p : DeallocateCore.Layout)
    (hc : s.host.gas.Credits (246 * op + rest)) : (callAfter s op p).host.gas.Credits rest :=
  after_credits (entered s op) op rest p (entered_credits s op (235 * op + rest) (hc.mono (by omega)))
end WNear.Proofs.VectorDropPositive237
