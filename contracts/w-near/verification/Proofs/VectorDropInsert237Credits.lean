import Proofs.VectorDropInsert237State
import Proofs.DeallocateInsertGas

/-! Residual gas of the concrete f237 forwarder and nested allocator phases. -/
namespace WNear.Proofs.VectorDropInsert237
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)

def entered(s:Store NearState)(op:Nat):=chargedStore (chargedStore s op) (10*op)
def before582(s:Store NearState)(op:Nat):=paid s op 4
def after(s:Store NearState)(op:Nat)(p:DeallocateCore.Layout):=DeallocateInsert.callAfter (before582 s op) op p
def callAfter(s:Store NearState)(op:Nat)(p:DeallocateCore.Layout):=after (entered s op) op p

theorem entered_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (11 * op + rest)) : (entered s op).host.gas.Credits rest :=
  StorePair.charged_credits (chargedStore s op) (10 * op) rest
    (StorePair.charged_credits s op (10 * op + rest) (hc.mono (by omega)))

theorem after_credits (s : Store NearState) (op rest : Nat) (p : DeallocateCore.Layout)
    (hc : s.host.gas.Credits (146 * op + rest)) : (after s op p).host.gas.Credits rest :=
  DeallocateInsert.callAfter_credits (before582 s op) op rest p (paid_credits s op 4 _ (hc.mono (by omega)))

theorem callAfter_credits (s : Store NearState) (op rest : Nat) (p : DeallocateCore.Layout)
    (hc : s.host.gas.Credits (157 * op + rest)) : (callAfter s op p).host.gas.Credits rest :=
  after_credits (entered s op) op rest p (entered_credits s op (146 * op + rest) (hc.mono (by omega)))
end WNear.Proofs.VectorDropInsert237
