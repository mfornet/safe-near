import NearVM.MeteredHosts.StorageFrame
import NearVM.MeteredHosts.StoragePrepareBudget

/-! Frames obtained from actual returning discard-register storage writes.
No assumption specifies pre-invocation validation, trie preparation or billing. -/
namespace Wasm.Near.MeteredHosts.StorageReturnFrame
open StorageMetered StorageFrame
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384

/-- The public trie-phase projection masks all effects outside the frame,
even when its hidden implementation reports a failure. -/
theorem prepare_frame (before : HostStore NearState) (keyLen keyPtr valueLen valuePtr : UInt64) :
    Frame before (prepareStorageCall "storage_write" before (args keyLen keyPtr valueLen valuePtr)).1 :=
  ⟨rfl, rfl⟩

/-- A returning raw write with the discard sentinel changes only storage and iterators. -/
theorem raw_return_frame (before after : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (values : List Value)
    (hreturn : storageWriteFn.invoke before (args keyLen keyPtr valueLen valuePtr) = .Return values after) :
    Frame before after := by
  dsimp only [args, storageWriteFn, disallowInView, checkDataLimit, checkedSetRegister?] at hreturn
  repeat' first
    | cases hreturn
    | exact ⟨rfl, rfl⟩
    | split at hreturn

/-- Successful final billing and usage accounting preserve the raw host frame. -/
theorem finish_return_frame (extra : Nat) (before middle after : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (values result : List Value)
    (hraw : Frame before middle)
    (hreturn : finishMeteredCall extra "storage_write" before (args keyLen keyPtr valueLen valuePtr)
      (.Return values middle) = .Return result after) :
    Frame before after := by
  rw [StorageBudget.finish_eq] at hreturn
  dsimp only at hreturn
  cases hc : applyCharges middle.host
      (chargesAfter "storage_write" before middle (args keyLen keyPtr valueLen valuePtr)) with
  | mk paid error =>
    rw [hc] at hreturn
    cases error with
    | some error => cases hreturn
    | none =>
      cases hreturn
      have hf : Frame middle {middle with host := paid} := by
        refine ⟨rfl, ?_⟩
        have hp := charges_restore middle.host
          (chargesAfter "storage_write" before middle (args keyLen keyPtr valueLen valuePtr))
          (StorageBudget.afterPlan_burnsOnly before middle keyLen keyPtr valueLen valuePtr)
        simpa only [hc] using hp
      refine ⟨?_, ?_⟩
      · simp only [updateStorageUsage]
        repeat' first | exact (hraw.trans hf).1 | split
      · rw [updateStorageUsage_restore]
        exact (hraw.trans hf).2


/-- The real storage phase, raw host and successful finish compose their frames. -/
theorem invoke_return_frame (extra : Nat) (before after : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (values : List Value)
    (hreturn : invokeStorageCall extra "storage_write" storageWriteFn before
      (args keyLen keyPtr valueLen valuePtr) = .Return values after) :
    Frame before after := by
  unfold invokeStorageCall at hreturn
  dsimp only at hreturn
  cases he : (prepareStorageCall "storage_write" before (args keyLen keyPtr valueLen valuePtr)).2 with
  | some error =>
    rw [he] at hreturn
    cases error <;> cases hreturn
  | none =>
    rw [he] at hreturn
    let phase := (prepareStorageCall "storage_write" before (args keyLen keyPtr valueLen valuePtr)).1
    cases hr : storageWriteFn.invoke phase (args keyLen keyPtr valueLen valuePtr) with
    | Trap middle message =>
      change finishMeteredCall extra "storage_write" phase (args keyLen keyPtr valueLen valuePtr)
        (storageWriteFn.invoke phase (args keyLen keyPtr valueLen valuePtr)) = _ at hreturn
      rw [hr] at hreturn
      cases hreturn
    | Return result middle =>
      change finishMeteredCall extra "storage_write" phase (args keyLen keyPtr valueLen valuePtr)
        (storageWriteFn.invoke phase (args keyLen keyPtr valueLen valuePtr)) = _ at hreturn
      rw [hr] at hreturn
      exact (prepare_frame before keyLen keyPtr valueLen valuePtr).trans
        (finish_return_frame extra phase middle after keyLen keyPtr valueLen valuePtr result values
          (raw_return_frame phase middle keyLen keyPtr valueLen valuePtr result hr) hreturn)

/-- Every actual returning metered discard-register write preserves the full
storage frame, without any validation, trie-success or billing premise. -/
theorem metered_return_frame (extra : Nat) (before after : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (values : List Value)
    (hreturn : (metered extra "storage_write" storageWriteFn).invoke before
      (args keyLen keyPtr valueLen valuePtr) = .Return values after) :
    Frame before after := by
  simp only [metered, show deprecatedRuntimeHost "storage_write" = false by decide,
    Bool.false_eq_true, ↓reduceIte] at hreturn
  split at hreturn
  · cases hreturn
  · cases hc : applyCharges before.host
        (chargesBefore "storage_write" before (args keyLen keyPtr valueLen valuePtr)) with
    | mk paid error =>
      rw [hc] at hreturn
      cases error with
      | some error => cases hreturn
      | none =>
        let prePaid := Output.paidStore before paid
        change (match preInvokeError "storage_write" prePaid (args keyLen keyPtr valueLen valuePtr) with
          | some error => trapWith prePaid error
          | none => invokeStorageCall extra "storage_write" storageWriteFn prePaid
            (args keyLen keyPtr valueLen valuePtr)) = _ at hreturn
        cases he : preInvokeError "storage_write" prePaid (args keyLen keyPtr valueLen valuePtr) with
        | some error => rw [he] at hreturn; cases hreturn
        | none =>
          rw [he] at hreturn
          have hf := prepayment_frame before
            (chargesBefore "storage_write" before (args keyLen keyPtr valueLen valuePtr))
            (StorageBudget.plan_burnsOnly before keyLen keyPtr valueLen valuePtr)
          have hpaid : Frame before prePaid := by simpa only [hc] using hf
          exact hpaid.trans (invoke_return_frame extra prePaid after keyLen keyPtr valueLen valuePtr values hreturn)

end Wasm.Near.MeteredHosts.StorageReturnFrame
