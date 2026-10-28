import NearLogic.CallWrite
import NearLogic.Hosts.Registers

/-!
# Context getters, metered: `storage_usage` and `attached_deposit`

The host contracts of `storage_usage()` and `attached_deposit(ptr)` with their
exact gas: each charge list is `chargesBefore` (`chargesAfter` is empty for
both), and the gas of the contract is its `chargesUse`.

* `storageUsage_readContract`: `storage_usage()` reads no memory, returns
  `h.context.storageUsage`, the host unchanged but for gas
  (`storageUsageUse h`, the `base` charge).
* `attachedDeposit_rwContract`: `attached_deposit(ptr)` outside a view call
  writes the deposit as 16 little-endian bytes (`leU128Bytes`) over the 16
  bytes at `ptr`, the host unchanged but for gas (`attachedDepositUse h`:
  `base` and the 16-byte memory write).
-/

namespace NearLogic

open Wasm Wasm.Near

theorem chargesBefore_storageUsage (st : HostStore NearState) :
    chargesBefore "storage_usage" st [] = [.ext "base"] := by
  have hs : storageMutationPlan? "storage_usage" st [] = none := by simp [storageMutationPlan?]
  have hpre : "storage_usage".startsWith "promise_batch_action_" = false := by decide
  simp [chargesBefore, hs, creationAccountArgs, argU64, hpre, chargesBeforeUnvalidated, cryptoEval]

theorem chargesBefore_attachedDeposit (st : HostStore NearState) (ptr : UInt64) :
    chargesBefore "attached_deposit" st [.i64 ptr] =
      [.ext "base", .ext "write_memory_base", .ext "write_memory_byte" 16] := by
  have hs : storageMutationPlan? "attached_deposit" st [.i64 ptr] = none := by
    simp [storageMutationPlan?]
  have hpre : "attached_deposit".startsWith "promise_batch_action_" = false := by decide
  simp [chargesBefore, hs, creationAccountArgs, argU64, hpre, chargesBeforeUnvalidated, writeMem]

/-- The two context getters. -/
def EnvGetterHost (name : String) : Prop :=
  name = "storage_usage" ∨ name = "attached_deposit"

theorem preInvokeError_envGetters (name : String) (st : HostStore NearState) (args : List Value)
    (hn : EnvGetterHost name) : preInvokeError name st args = none := by
  rcases hn with rfl | rfl <;>
  · simp [preInvokeError, invocationArgumentError, storageMutationPlan?, globalContractInputs?,
      creationPrefixError, creationAccountError, creationAccountArgs, allocatesPromise,
      functionCallInputError, functionCallInputs?]

/-- Post-call metering of a context getter leaves its result alone. -/
theorem finish_envGetters (extra : Nat) {name : String} (hn : EnvGetterHost name)
    (before : HostStore NearState) (args vals : List Value) (st2 : HostStore NearState) :
    finishMeteredCall extra name before args (.Return vals st2) = .Return vals st2 := by
  rcases hn with rfl | rfl <;>
  · simp (config := { decide := true }) [finishMeteredCall, chargesAfter, applyCharges, deductDeposit,
      promiseDeposit?, actionMethodEncodingError, actionMethodBytes?, functionCallInputs?,
      updateStorageUsage]

/-- A context getter whose charges fit, outside a view call when it is
view-restricted: the charges, then the functional host. -/
theorem metered_envGetters (extra : Nat) {name : String} (hn : EnvGetterHost name)
    (fn : NearHostFn NearState) (st : HostStore NearState) (args : List Value) {C : Nat}
    (hv : (st.host.context.isView && viewRestrictedHost name) = false)
    (h1 : st.host.gas.used + chargesUse st.host (chargesBefore name st args) ≤ C)
    (h2 : C ≤ st.host.gas.maxBurnt) (h3 : C ≤ st.host.gas.prepaid) :
    ∃ ns, ChargedTo st.host ns (chargesUse st.host (chargesBefore name st args)) ∧
      (metered extra name fn).invoke st args =
        finishMeteredCall extra name { mem := st.mem, host := afterCharges ns } args
          (fn.invoke { mem := st.mem, host := afterCharges ns } args) := by
  obtain ⟨hok, hch⟩ := applyCharges_ok st.host (chargesBefore name st args) h1 h2 h3
  have hdep : deprecatedRuntimeHost name = false := by
    rcases hn with rfl | rfl <;> decide
  have hother : ["storage_read", "storage_has_key", "storage_write", "storage_remove"].contains
      name = false := by
    rcases hn with rfl | rfl <;> decide
  refine ⟨_, hch, ?_⟩
  simp only [metered, hdep, hv, Bool.false_eq_true, ite_false]
  generalize hac : applyCharges st.host (chargesBefore name st args) = ac at hok hch ⊢
  obtain ⟨ns, err⟩ := ac
  simp only at hok
  subst hok
  simp only
  rw [preInvokeError_envGetters name _ _ hn]
  simp only [invokeStorageCall, prepareStorageCall_other _ _ _ hother]
  rfl

/-! ## `storage_usage` -/

/-- The charges of `storage_usage`. -/
def storageUsageChargeList : List Charge := [.ext "base"]

/-- The gas `storage_usage` uses. -/
def storageUsageUse (h : NearState) : Nat := chargesUse h storageUsageChargeList

/-- `storage_usage()`: reads no memory, returns the account's storage usage,
and leaves the host as it was but for gas. -/
theorem storageUsage_readContract (extra : Nat) (h : NearState) (ptr : Nat) {C : Nat} :
    ReadContract (metered extra "storage_usage" storageUsageFn).toHostFn h h
      [] [.i64 h.context.storageUsage] ptr [] (storageUsageUse h) C := by
  intro host mem _ he _ hu hmb hpp
  have hcs : chargesBefore "storage_usage" { mem, host } [] = storageUsageChargeList :=
    chargesBefore_storageUsage _
  have huse : storageUsageUse host = storageUsageUse h := chargesUse_erase he _
  have hv : (host.context.isView && viewRestrictedHost "storage_usage") = false := by
    have : viewRestrictedHost "storage_usage" = false := by decide
    rw [this, Bool.and_false]
  obtain ⟨ns, hch, hinv⟩ := metered_envGetters extra (name := "storage_usage") (Or.inl rfl)
    storageUsageFn { mem, host } [] (C := C) hv (by rw [hcs]; rw [← huse] at hu; exact hu) hmb hpp
  have hsu : ns.context.storageUsage = h.context.storageUsage :=
    erase_field (hch.erase.trans he) (fun x : NearState => x.context.storageUsage) fun _ => rfl
  refine ⟨afterCharges ns, ?_, ?_, ?_, hch.maxBurnt, hch.prepaid⟩
  · simp only [NearHostFn.toHostFn, Option.getD_some, hinv]
    simp only [storageUsageFn, contextU64Fn, afterCharges, hsu]
    rw [finish_envGetters extra (Or.inl rfl)]
  · rw [erase_afterCharges, hch.erase, he]
  · show ns.gas.used ≤ _
    rw [hch.used, hcs]
    show _ ≤ host.gas.used + storageUsageUse h
    rw [← huse]; exact Nat.le_refl _

/-! ## `attached_deposit` -/

/-- The charges of `attached_deposit`: `base` and a 16-byte memory write. -/
def attachedDepositChargeList : List Charge :=
  [.ext "base", .ext "write_memory_base", .ext "write_memory_byte" 16]

/-- The gas `attached_deposit` uses. -/
def attachedDepositUse (h : NearState) : Nat := chargesUse h attachedDepositChargeList

/-- `attached_deposit(ptr)` outside a view call: replaces the 16 bytes `old`
at `ptr` by the attached deposit's 16 little-endian bytes, returns nothing, and
leaves the host as it was but for gas. -/
theorem attachedDeposit_rwContract (extra : Nat) (h : NearState) (ptr : UInt64) (old : List UInt8)
    {C : Nat} (hold : old.length = 16) (hview : h.context.isView = false) :
    RWContract (metered extra "attached_deposit" attachedDepositFn).toHostFn h h
      [.i64 ptr] [] ptr.toNat old (leU128Bytes h.context.attachedDeposit) (attachedDepositUse h) C := by
  intro host mem hwf he hrd hu hmb hpp
  have hcs : chargesBefore "attached_deposit" { mem, host } [.i64 ptr] = attachedDepositChargeList :=
    chargesBefore_attachedDeposit _ _
  have huse : attachedDepositUse host = attachedDepositUse h := chargesUse_erase he _
  have hview' : host.context.isView = false := by
    rw [erase_field he (fun x : NearState => x.context.isView) fun _ => rfl]; exact hview
  have hv : (host.context.isView && viewRestrictedHost "attached_deposit") = false := by
    rw [hview', Bool.false_and]
  obtain ⟨ns, hch, hinv⟩ := metered_envGetters extra (name := "attached_deposit") (Or.inr rfl)
    attachedDepositFn { mem, host } [.i64 ptr] (C := C) hv
    (by rw [hcs]; rw [← huse] at hu; exact hu) hmb hpp
  have hens : erase ns = erase h := hch.erase.trans he
  have hdep : ns.context.attachedDeposit = h.context.attachedDeposit :=
    erase_field hens (fun x : NearState => x.context.attachedDeposit) fun _ => rfl
  have hview'' : ns.context.isView = false := by
    rw [erase_field hens (fun x : NearState => x.context.isView) fun _ => rfl]; exact hview
  have hlen : (leU128Bytes h.context.attachedDeposit).length = 16 := by simp [leU128Bytes]
  have hin : ptr.toNat + 16 ≤ mem.byteSize := by
    have := (hrd 15 (by omega)).1
    omega
  have hin' : ¬ ptr.toNat + (leU128Bytes h.context.attachedDeposit).length > mem.size * 65536 := by
    rw [hlen]
    unfold Memory.byteSize at hin
    show ¬ _ > mem.pages.size * 65536
    unfold pageSize at hin
    omega
  refine ⟨afterCharges ns, mem.writeList ptr.toNat (leU128Bytes h.context.attachedDeposit), ?_,
    writeList_spec hwf (by rw [hlen]; exact hin), ?_, ?_, hch.maxBurnt, hch.prepaid⟩
  · simp only [NearHostFn.toHostFn, Option.getD_some, hinv]
    simp only [attachedDepositFn, disallowInView, contextU128MemFn, writeU128, writeMemBytes,
      afterCharges, hview'', hdep, memBytes, hin', Bool.false_eq_true, ite_false]
    rw [finish_envGetters extra (Or.inr rfl)]
  · rw [erase_afterCharges, hch.erase, he]
  · show ns.gas.used ≤ _
    rw [hch.used, hcs]
    show _ ≤ host.gas.used + attachedDepositUse h
    rw [← huse]; exact Nat.le_refl _

end NearLogic
