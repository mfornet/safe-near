import Proofs.DeallocateCoreState

/-! Residual gas for the real previous-free deallocation phases. -/
namespace WNear.Proofs.DeallocateCore
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)

theorem guarded_credits (s : Store NearState) (op rest : Nat) (hc : s.host.gas.Credits (6 * op + rest)) :
    (guarded s op).host.gas.Credits rest := paid_credits s op 6 rest hc

theorem aligned_credits (s : Store NearState) (op rest : Nat) (hc : s.host.gas.Credits (49 * op + rest)) :
    (aligned s op).host.gas.Credits rest :=
  Deallocate.aligned_credits (guarded s op) op rest (guarded_credits s op (43 * op + rest) (hc.mono (by omega)))

theorem saved_credits (s : Store NearState) (op rest : Nat) (hc : s.host.gas.Credits (52 * op + rest)) :
    (saved s op).host.gas.Credits rest :=
  paid_credits (aligned s op) op 3 rest (aligned_credits s op (3 * op + rest) (hc.mono (by omega)))

theorem marked_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (61 * op + rest)) :
    (marked s op p).host.gas.Credits rest :=
  paid_credits (saved s op) op 9 rest (saved_credits s op (9 * op + rest) (hc.mono (by omega)))

theorem sized_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (88 * op + rest)) :
    (sized s op p).host.gas.Credits rest :=
  Deallocate.sized_credits (marked s op p) op rest (marked_credits s op (27 * op + rest) p (hc.mono (by omega)))

theorem zeroed_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (91 * op + rest)) :
    (zeroed s op p).host.gas.Credits rest :=
  paid_credits (sized s op p) op 3 rest (sized_credits s op (3 * op + rest) p (hc.mono (by omega)))

theorem previousSelected_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (106 * op + rest)) :
    (previousSelected s op p).host.gas.Credits rest :=
  paid_credits (zeroed s op p) op 15 rest (zeroed_credits s op (15 * op + rest) p (hc.mono (by omega)))

theorem unlinkEntered_credits (s : Store NearState) (op rest : Nat) (hc : s.host.gas.Credits (11 * op + rest)) :
    (unlinkEntered s op).host.gas.Credits rest := by
  exact StorePair.charged_credits (chargedStore s op) (10 * op) rest
    (StorePair.charged_credits s op (10 * op + rest) (hc.mono (by omega)))

theorem unlinked_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (179 * op + rest)) :
    (unlinked s op p).host.gas.Credits rest := by
  apply DeallocateListState.after_credits _ op rest (unlinkLayout p)
  apply unlinkEntered_credits _ op (61 * op + rest)
  apply paid_credits _ op 1 (11 * op + (61 * op + rest))
  exact previousSelected_credits s op _ p (hc.mono (by omega))

theorem flagChecked_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (185 * op + rest)) :
    (flagChecked s op p).host.gas.Credits rest :=
  paid_credits (unlinked s op p) op 6 rest (unlinked_credits s op (6 * op + rest) p (hc.mono (by omega)))

theorem previousSized_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (212 * op + rest)) :
    (previousSized s op p).host.gas.Credits rest :=
  Deallocate.sized_credits (flagChecked s op p) op rest (flagChecked_credits s op (27 * op + rest) p (hc.mono (by omega)))

theorem restored_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (215 * op + rest)) :
    (restored s op p).host.gas.Credits rest :=
  paid_credits (previousSized s op p) op 3 rest (previousSized_credits s op (3 * op + rest) p (hc.mono (by omega)))

theorem after_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (218 * op + rest)) :
    (after s op p).host.gas.Credits rest :=
  paid_credits (restored s op p) op 3 rest (restored_credits s op (3 * op + rest) p (hc.mono (by omega)))

theorem entered_credits (s : Store NearState) (op rest : Nat) (hc : s.host.gas.Credits (13 * op + rest)) :
    (entered s op).host.gas.Credits rest :=
  StorePair.charged_credits (chargedStore s op) (12 * op) rest
    (StorePair.charged_credits s op (12 * op + rest) (hc.mono (by omega)))

theorem callAfter_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (231 * op + rest)) :
    (callAfter s op p).host.gas.Credits rest :=
  after_credits (entered s op) op rest p (entered_credits s op (218 * op + rest) (hc.mono (by omega)))

end WNear.Proofs.DeallocateCore
