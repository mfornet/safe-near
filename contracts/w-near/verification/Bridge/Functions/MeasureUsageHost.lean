import NearLogic.Hosts.StorageRemove
import NearLogic.Hosts.StorageWrite

/-!
# The host between `measure_account_storage_usage`'s calls

* `swh_fields`: what `storage_write` keeps of the host (config, fees, the context but the usage)
  and what it changes (the usage grown by the record, the key holding the value).
* `post_fields`: the same for any host equal to it up to gas.
* `usage_sub`: the `u64` difference `after - before` of the two `storage_usage()` readings, with no
  wrap: the record's size, and the overflow check (`after - before > after`) not taken.
-/

namespace WNear.Binary.MeasureUsage

open Wasm Wasm.Near NearLogic Near.TrieOverlay

theorem swh_fields (e : Nat) (h : NearState) (k v : List UInt8) (r : UInt64) (s2 : State) :
    (storageWriteHost e h k v r s2).config = h.config ∧
    (storageWriteHost e h k v r s2).fees = h.fees ∧
    (storageWriteHost e h k v r s2).extCosts = h.extCosts ∧
    (storageWriteHost e h k v r s2).context.isView = h.context.isView ∧
    (storageWriteHost e h k v r s2).context.currentAccountId = h.context.currentAccountId ∧
    (storageWriteHost e h k v r s2).context.storageUsage =
      UInt64.ofNat (writeUsage e k v (h.storage k) h.context.storageUsage.toNat) ∧
    (storageWriteHost e h k v r s2).storage k = some v := by
  have hs := storageWriteHost_storage e h k v r s2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, by rw [hs]; simp⟩ <;>
  · unfold storageWriteHost logWrite
    simp only [NearState.invalidateIterators, NearState.setStorage]
    try (unfold storageReadRegs; split <;> (try split) <;> rfl)

/-- The fields of a host equal, up to gas, to the one `storage_write` leaves. -/
theorem post_fields {e : Nat} {h h1 : NearState} {k v : List UInt8} {r : UInt64} {s2 : State}
    (he : erase h1 = erase (storageWriteHost e h k v r s2)) :
    h1.config = h.config ∧ h1.fees = h.fees ∧ h1.extCosts = h.extCosts ∧
    h1.context.isView = h.context.isView ∧
    h1.context.currentAccountId = h.context.currentAccountId ∧
    h1.context.storageUsage = UInt64.ofNat (writeUsage e k v (h.storage k) h.context.storageUsage.toNat) ∧
    h1.storage k = some v := by
  obtain ⟨a, b, c, d, f, g, i⟩ := swh_fields e h k v r s2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [erase_field he NearState.config fun _ => rfl]; exact a
  · rw [erase_field he NearState.fees fun _ => rfl]; exact b
  · rw [erase_field he NearState.extCosts fun _ => rfl]; exact c
  · rw [erase_field he (fun x : NearState => x.context.isView) fun _ => rfl]; exact d
  · rw [erase_field he (fun x : NearState => x.context.currentAccountId) fun _ => rfl]; exact f
  · rw [erase_field he (fun x : NearState => x.context.storageUsage) fun _ => rfl]; exact g
  · rw [erase_field he NearState.storage fun _ => rfl]; exact i

/-- `after - before` with `after = before + X` and no wrap: `X`, and not above `after`. -/
theorem usage_sub (B : UInt64) (X : Nat) (h : B.toNat + X < 2 ^ 64) :
    UInt64.ofNat (B.toNat + X) - B = UInt64.ofNat X ∧ ¬ (UInt64.ofNat (B.toNat + X) < UInt64.ofNat X) := by
  have hb := B.toNat_lt
  constructor
  · apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le]
    · simp only [UInt64.toNat_ofNat']; omega
    · rw [UInt64.le_iff_toNat_le]; simp only [UInt64.toNat_ofNat']; omega
  · rw [UInt64.lt_iff_toNat_lt]; simp only [UInt64.toNat_ofNat']; omega

end WNear.Binary.MeasureUsage
