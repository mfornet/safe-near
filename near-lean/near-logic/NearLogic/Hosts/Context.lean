import NearLogic.Hosts.Registers

/-!
# Context hosts, metered: `attached_deposit` and `predecessor_account_id`

Both are view-restricted: outside a view call (`context.isView = false`) they run like the
register hosts (`Registers.lean`), with their charges before and none after.

* `attachedDeposit_rwContract`: `attached_deposit(ptr)` writes the attached deposit as 16
  little-endian bytes (`leU128Bytes`) over the 16 bytes at `ptr` (`RWContract`); gas
  `attachedDepositUse` (`base`, `write_memory_base`, `write_memory_byte · 16`).
* `predecessorAccountId_readContract`: `predecessor_account_id(r)`, the predecessor a valid
  account id within the register limit, sets register `r` to it (`ReadContract`, the host
  `predecessorHost`); gas `predecessorUse` (`base`, `write_register_base`,
  `write_register_byte · |id|`).
-/

namespace NearLogic

open Wasm Wasm.Near

/-- A context host that is view-restricted, outside a view call: the charges, then the functional
host, then nothing after. -/
theorem metered_context (extra : Nat) {name : String}
    (hn : name = "attached_deposit" ∨ name = "predecessor_account_id") (fn : NearHostFn NearState)
    (st : HostStore NearState) (args : List Value) {C : Nat} (hview : st.host.context.isView = false)
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
  have hpre : ∀ st' : HostStore NearState, preInvokeError name st' args = none := by
    intro st'
    rcases hn with rfl | rfl <;>
    · simp [preInvokeError, invocationArgumentError, storageMutationPlan?, globalContractInputs?,
        creationPrefixError, creationAccountError, creationAccountArgs, allocatesPromise,
        functionCallInputError, functionCallInputs?]
  refine ⟨_, hch, ?_⟩
  simp only [metered, hdep, hview, Bool.false_and, Bool.false_eq_true, ite_false]
  generalize hac : applyCharges st.host (chargesBefore name st args) = ac at hok hch ⊢
  obtain ⟨ns, err⟩ := ac
  simp only at hok
  subst hok
  simp only
  rw [hpre]
  simp only [invokeStorageCall, prepareStorageCall_other _ _ _ hother]
  rfl

/-- Post-call metering of the two context hosts leaves their result alone. -/
theorem finish_context (extra : Nat) {name : String}
    (hn : name = "attached_deposit" ∨ name = "predecessor_account_id")
    (before : HostStore NearState) (args vals : List Value) (st2 : HostStore NearState) :
    finishMeteredCall extra name before args (.Return vals st2) = .Return vals st2 := by
  rcases hn with rfl | rfl <;>
  · simp (config := { decide := true }) [finishMeteredCall, chargesAfter, applyCharges, deductDeposit,
      promiseDeposit?, actionMethodEncodingError, actionMethodBytes?, functionCallInputs?, updateStorageUsage]

/-! ## `attached_deposit` -/

/-- The charges of `attached_deposit`. -/
def attachedDepositChargeList : List Charge :=
  [.ext "base", .ext "write_memory_base", .ext "write_memory_byte" 16]

/-- The gas `attached_deposit` uses. -/
def attachedDepositUse (h : NearState) : Nat := chargesUse h attachedDepositChargeList

theorem chargesBefore_attachedDeposit (st : HostStore NearState) (ptr : UInt64) :
    chargesBefore "attached_deposit" st [.i64 ptr] = attachedDepositChargeList := by
  have hs : storageMutationPlan? "attached_deposit" st [.i64 ptr] = none := by simp [storageMutationPlan?]
  have hpre : "attached_deposit".startsWith "promise_batch_action_" = false := by decide
  simp [chargesBefore, hs, creationAccountArgs, argU64, hpre, chargesBeforeUnvalidated, writeMem,
    attachedDepositChargeList]

theorem leU128Bytes_length (n : Nat) : (leU128Bytes n).length = 16 := by simp [leU128Bytes]

/-- **`attached_deposit(ptr)`**, outside a view call: replaces the 16 bytes `old` at `ptr` by the
attached deposit's little-endian bytes, returns nothing, and leaves the host as it was but for
gas. -/
theorem attachedDeposit_rwContract (extra : Nat) (h : NearState) (ptr : UInt64) (old : List UInt8)
    {C : Nat} (hview : h.context.isView = false) (hold : old.length = 16) :
    RWContract (metered extra "attached_deposit" attachedDepositFn).toHostFn h h
      [.i64 ptr] [] ptr.toNat old (leU128Bytes h.context.attachedDeposit) (attachedDepositUse h) C := by
  intro host mem hwf he hrd hu hmb hpp
  have hcs : chargesBefore "attached_deposit" { mem, host } [.i64 ptr] = attachedDepositChargeList :=
    chargesBefore_attachedDeposit _ _
  have huse : attachedDepositUse host = attachedDepositUse h := chargesUse_erase he _
  have hview' : host.context.isView = false := by
    rw [erase_field he (fun x : NearState => x.context.isView) fun _ => rfl]; exact hview
  obtain ⟨ns, hch, hinv⟩ := metered_context extra (name := "attached_deposit") (Or.inl rfl)
    attachedDepositFn { mem, host } [.i64 ptr] (C := C) hview'
    (by rw [hcs]; rw [← huse] at hu; exact hu) hmb hpp
  have hens : erase ns = erase h := hch.erase.trans he
  have hdep : ns.context.attachedDeposit = h.context.attachedDeposit :=
    erase_field hens (fun x : NearState => x.context.attachedDeposit) fun _ => rfl
  have hvns : ns.context.isView = false := by
    rw [erase_field hens (fun x : NearState => x.context.isView) fun _ => rfl]; exact hview
  have hin : ptr.toNat + 16 ≤ mem.byteSize := by
    have := (hrd 15 (by omega)).1
    omega
  have hin' : ¬ ptr.toNat + (leU128Bytes h.context.attachedDeposit).length > mem.size * 65536 := by
    rw [leU128Bytes_length]
    unfold Memory.byteSize at hin
    show ¬ _ > mem.pages.size * 65536
    unfold pageSize at hin
    omega
  refine ⟨afterCharges ns, mem.writeList ptr.toNat (leU128Bytes h.context.attachedDeposit), ?_,
    writeList_spec hwf (by rw [leU128Bytes_length]; exact hin), ?_, ?_, hch.maxBurnt, hch.prepaid⟩
  · simp only [NearHostFn.toHostFn, Option.getD_some, hinv]
    simp only [attachedDepositFn, disallowInView, contextU128MemFn, writeU128, writeMemBytes, afterCharges,
      hvns, hdep, memBytes, hin', Bool.false_eq_true, ite_false]
    rw [finish_context extra (Or.inl rfl)]
  · rw [erase_afterCharges, hch.erase, he]
  · show ns.gas.used ≤ _
    rw [hch.used, hcs]
    show _ ≤ host.gas.used + attachedDepositUse h
    rw [← huse]; exact Nat.le_refl _

/-! ## `predecessor_account_id` -/

/-- The host after `predecessor_account_id(r)`: register `r` holds the predecessor (nothing
happens for the sentinel register `u64Max`). -/
def predecessorHost (h : NearState) (r : UInt64) : NearState :=
  if r = u64Max then h else h.setRegister r.toNat h.context.predecessorAccountId

/-- The charges of `predecessor_account_id` for an id of `n` bytes. -/
def predecessorChargeList (n : Nat) : List Charge :=
  [.ext "base", .ext "write_register_base", .ext "write_register_byte" n]

/-- The gas `predecessor_account_id` uses. -/
def predecessorUse (h : NearState) : Nat :=
  chargesUse h (predecessorChargeList h.context.predecessorAccountId.length)

theorem chargesBefore_predecessor (st : HostStore NearState) (r : UInt64) :
    chargesBefore "predecessor_account_id" st [.i64 r] =
      predecessorChargeList st.host.context.predecessorAccountId.length := by
  have hs : storageMutationPlan? "predecessor_account_id" st [.i64 r] = none := by
    simp [storageMutationPlan?]
  have hpre : "predecessor_account_id".startsWith "promise_batch_action_" = false := by decide +kernel
  simp [chargesBefore, hs, creationAccountArgs, argU64, hpre, chargesBeforeUnvalidated, writeReg,
    predecessorChargeList]

theorem erase_predecessorHost {h h' : NearState} (he : erase h = erase h') (r : UInt64) :
    erase (predecessorHost h r) = erase (predecessorHost h' r) := by
  have hi : h.context.predecessorAccountId = h'.context.predecessorAccountId :=
    erase_field he (fun x : NearState => x.context.predecessorAccountId) fun _ => rfl
  have hs : ∀ (x : NearState) (i : Nat) (d : List UInt8), erase (x.setRegister i d) = (erase x).setRegister i d :=
    fun _ _ _ => rfl
  unfold predecessorHost
  split
  · exact he
  · rw [hs, hs, he, hi]

theorem predecessorUse_erase {h h' : NearState} (he : erase h = erase h') : predecessorUse h = predecessorUse h' := by
  have hi : h.context.predecessorAccountId = h'.context.predecessorAccountId :=
    erase_field he (fun x : NearState => x.context.predecessorAccountId) fun _ => rfl
  unfold predecessorUse
  rw [hi]
  exact chargesUse_erase he _

/-- **`predecessor_account_id(r)`**, outside a view call, the predecessor a valid account id within
the register size limit: reads no memory, returns nothing, and sets register `r` to the predecessor
(`predecessorHost`). -/
theorem predecessorAccountId_readContract (extra : Nat) (h : NearState) (r : UInt64) (ptr : Nat) {C : Nat}
    (hview : h.context.isView = false)
    (hvalid : h.config.validAccountId h.context.predecessorAccountId = true)
    (hlim : withinLimit h.config.maxRegisterLen h.context.predecessorAccountId.length = true) :
    ReadContract (metered extra "predecessor_account_id" predecessorAccountIdFn).toHostFn h
      (predecessorHost h r) [.i64 r] [] ptr [] (predecessorUse h) C := by
  intro host mem _ he _ hu hmb hpp
  have hpid : host.context.predecessorAccountId = h.context.predecessorAccountId :=
    erase_field he (fun x : NearState => x.context.predecessorAccountId) fun _ => rfl
  have hcs : chargesBefore "predecessor_account_id" { mem, host } [.i64 r] =
      predecessorChargeList h.context.predecessorAccountId.length := by
    rw [chargesBefore_predecessor]; simp only [hpid]
  have hk : chargesUse host (predecessorChargeList h.context.predecessorAccountId.length) = predecessorUse h := by
    unfold predecessorUse; exact chargesUse_erase he _
  have hview' : host.context.isView = false := by
    rw [erase_field he (fun x : NearState => x.context.isView) fun _ => rfl]; exact hview
  obtain ⟨ns, hch, hinv⟩ := metered_context extra (name := "predecessor_account_id") (Or.inr rfl)
    predecessorAccountIdFn { mem, host } [.i64 r] (C := C) hview'
    (by rw [hcs]; show _ + chargesUse host _ ≤ C; rw [hk]; exact hu) hmb hpp
  have hens : erase ns = erase h := hch.erase.trans he
  have hcfg : ns.config = h.config := erase_field hens NearState.config fun _ => rfl
  have hp : ns.context.predecessorAccountId = h.context.predecessorAccountId :=
    erase_field hens (fun x : NearState => x.context.predecessorAccountId) fun _ => rfl
  have hvns : ns.context.isView = false := by
    rw [erase_field hens (fun x : NearState => x.context.isView) fun _ => rfl]; exact hview
  refine ⟨predecessorHost (afterCharges ns) r, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [NearHostFn.toHostFn, Option.getD_some, hinv]
    simp only [predecessorAccountIdFn, disallowInView, accountIdRegisterFn, checkAccountId,
      writeRegisterResult, checkedSetRegister?, afterCharges, hvns, hcfg, hp, hvalid,
      Bool.false_eq_true, ite_false, ite_true]
    by_cases hr : r = u64Max
    · simp only [hr, ite_true]
      rw [finish_context extra (Or.inr rfl)]
      simp [predecessorHost, afterCharges]
    · simp only [hr, ite_false, hlim, ite_true]
      rw [finish_context extra (Or.inr rfl)]
      simp [predecessorHost, hr, afterCharges, hp]
  · rw [erase_predecessorHost (erase_afterCharges ns) r, erase_predecessorHost hens r]
  · unfold predecessorHost; split <;> (show ns.gas.used ≤ _; rw [hch.used, hcs]; show _ + chargesUse host _ ≤ _; rw [hk]; exact Nat.le_refl _)
  · unfold predecessorHost; split <;> exact hch.maxBurnt
  · unfold predecessorHost; split <;> exact hch.prepaid

end NearLogic
