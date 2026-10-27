import NearVM.MeteredHosts.StorageReadPrepare

/-! Composition through the actual metered storage-read wrapper. -/
namespace Wasm.Near.MeteredHosts.StorageRead
open StorageMetered
open _root_.Near.TrieOverlay
set_option maxRecDepth 16384
set_option maxHeartbeats 500000

theorem pre_error (before : HostStore NearState) (keyLen keyPtr register : UInt64) :
    preInvokeError "storage_read" before (args keyLen keyPtr register) = none := by
  simp [preInvokeError, invocationArgumentError, storageMutationPlan?, globalContractInputs?,
    creationPrefixError, creationAccountError, creationAccountArgs, allocatesPromise,
    functionCallInputError, functionCallInputs?]

theorem post_hit (before after : HostStore NearState) (keyLen keyPtr register : UInt64) (key value : List UInt8)
    (hk : getMemOrReg before keyPtr keyLen = some key) (hs : before.host.storage key = some value)
    (ha : before.host.storageAccounting.isSome = true) :
    chargesAfter "storage_read" before after (args keyLen keyPtr register) = writeReg value.length := by
  simp only [chargesAfter, args, argU64, List.getElem?_cons_zero, List.getElem?_cons_succ, hk, hs]
  cases h : before.host.storageAccounting <;> simp_all

theorem finish_hit (extra : Nat) (before : HostStore NearState) (keyLen keyPtr register : UInt64)
    (key value : List UInt8) (postPaid : NearState)
    (hk : getMemOrReg before keyPtr keyLen = some key) (hs : before.host.storage key = some value)
    (ha : before.host.storageAccounting.isSome = true)
    (hc : applyCharges (written before register value).host (writeReg value.length) = (postPaid, none)) :
    finishMeteredCall extra "storage_read" before (args keyLen keyPtr register)
      (.Return [.i64 1] (written before register value)) =
      .Return [.i64 1] {written before register value with host := postPaid} := by
  simp only [finishMeteredCall]
  rw [post_hit _ _ _ _ _ _ _ hk hs ha, hc]
  simp [deductDeposit, promiseDeposit?, actionMethodEncodingError, actionMethodBytes?,
    usesKeyMethodFields, functionCallInputs?, updateStorageUsage]

/-- Successful canonical preparation is local to the storage phase; this
lemma composes it with actual raw register mutation and final billing. -/
theorem metered_hit (extra : Nat) (before : HostStore NearState)
    (keyLen keyPtr register : UInt64) (key value : List UInt8) (prePaid phasePaid postPaid : NearState) (trie : State)
    (hpre : applyCharges before.host (chargesBefore "storage_read" before (args keyLen keyPtr register)) = (prePaid, none))
    (hk : getMemOrReg (Output.paidStore before prePaid) keyPtr keyLen = some key)
    (hl : withinLimit prePaid.config.maxStorageKeyLen key.length = true)
    (hs : prePaid.storage key = some value)
    (hr : register = u64Max ∨ withinLimit prePaid.config.maxRegisterLen value.length = true)
    (hp : prepareStorageCall "storage_read" (Output.paidStore before prePaid) (args keyLen keyPtr register) =
      (prepared (Output.paidStore before prePaid) phasePaid trie, none))
    (hpost : applyCharges (written (prepared (Output.paidStore before prePaid) phasePaid trie) register value).host
      (writeReg value.length) = (postPaid, none)) :
    (metered extra "storage_read" storageReadFn).invoke before (args keyLen keyPtr register) =
      .Return [.i64 1] {written (prepared (Output.paidStore before prePaid) phasePaid trie) register value with host := postPaid} := by
  simp only [metered, show deprecatedRuntimeHost "storage_read" = false by decide,
    show viewRestrictedHost "storage_read" = false by decide, Bool.and_false, Bool.false_eq_true, ↓reduceIte, hpre]
  change (match preInvokeError "storage_read" (Output.paidStore before prePaid) (args keyLen keyPtr register) with
    | some error => trapWith (Output.paidStore before prePaid) error
    | none => invokeStorageCall extra "storage_read" storageReadFn (Output.paidStore before prePaid) (args keyLen keyPtr register)) = _
  rw [pre_error]
  simp only [invokeStorageCall, hp]
  rw [raw_hit (prepared (Output.paidStore before prePaid) phasePaid trie) keyLen keyPtr register key value hk hl hs hr]
  exact finish_hit extra _ keyLen keyPtr register key value postPaid hk hs rfl hpost

end Wasm.Near.MeteredHosts.StorageRead
