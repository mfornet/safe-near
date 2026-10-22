import Spec.Liability
import Proofs.Economics

namespace Linkdrop
open Spec

theorem liability_set_absent (s : State) (keys : List Key) (k : Key) (v : Option Nat)
    (hk : k ∉ keys) : liability (s.set k v) keys = liability s keys := by
  unfold liability
  congr 1
  apply List.map_congr_left
  intro j hj
  rw [set_other s k j v (by intro h; subst j; exact hk hj)]

theorem liability_set (s : State) (keys : List Key) (k : Key) (v : Option Nat)
    (hn : keys.Nodup) (hk : k ∈ keys) :
    liability (s.set k v) keys + (s.accounts k).getD 0 =
      liability s keys + v.getD 0 := by
  induction keys with
  | nil => simp at hk
  | cons j js ih =>
    simp only [List.nodup_cons] at hn
    simp only [List.mem_cons] at hk
    rcases hk with h | h
    · subst j
      have he := liability_set_absent s js k v hn.1
      simp only [liability, List.map_cons, List.sum_cons] at *
      rw [set_same]
      omega
    · have hne : j ≠ k := by intro he; subst j; exact hn.1 h
      have he := ih hn.2 h
      simp only [liability, List.map_cons, List.sum_cons] at *
      rw [set_other s k j v hne]
      omega

theorem sendConservation : SendConservation := by
  intro s e k out keys hn hk h
  have hb := step_ok_body h
  simp only [body] at hb
  split at hb <;> simp_all
  subst out
  have he := liability_set s keys k
    (some (min ((s.accounts k).getD 0 + e.deposit) maxAmount)) hn hk
  simp only [Option.getD_some] at he
  dsimp only at *
  have hm := Nat.min_le_left ((s.accounts k).getD 0 + e.deposit) maxAmount
  omega

theorem claimConservation : ClaimConservation := by
  intro s e account amount out keys hn hk hamt h
  have hb := step_ok_body h
  simp only [body, hamt, Except.ok.injEq] at hb
  subst out
  have he := liability_set s keys e.signerKey none hn hk
  simpa [hamt] using he

theorem restoreConservation : RestoreConservation := by
  intro s e amount keys hn hk hnone
  have he := liability_set s keys e.signerKey (some amount) hn hk
  simpa [hnone] using he

end Linkdrop
