import NearLogic.CallWrite
import NearLogic.Hosts.ValueReturn

/-!
# Register hosts, metered

The host contracts of `register_len(r)`, `read_register(r, ptr)` and
`input(r)` with their exact gas: each charge list is computed from
`chargesBefore` (`chargesAfter` is empty for all three), and the gas `kh` of
the contract is its `chargesUse`. `register_len` and `input` read no memory
(`ReadContract` with no bytes); `read_register` writes the register over the
bytes at `ptr` (`RWContract`).
-/

namespace NearLogic

open Wasm Wasm.Near

theorem chargesBefore_registerLen (st : HostStore NearState) (r : UInt64) :
    chargesBefore "register_len" st [.i64 r] = [.ext "base"] := by
  have hs : storageMutationPlan? "register_len" st [.i64 r] = none := by simp [storageMutationPlan?]
  have hpre : "register_len".startsWith "promise_batch_action_" = false := by decide
  simp [chargesBefore, hs, creationAccountArgs, argU64, hpre, chargesBeforeUnvalidated]

theorem chargesBefore_input (st : HostStore NearState) (r : UInt64) :
    chargesBefore "input" st [.i64 r] = [.ext "base", .ext "write_register_base"] := by
  have hs : storageMutationPlan? "input" st [.i64 r] = none := by simp [storageMutationPlan?]
  have hpre : "input".startsWith "promise_batch_action_" = false := by decide
  simp [chargesBefore, hs, creationAccountArgs, argU64, hpre, chargesBeforeUnvalidated]

theorem chargesBefore_readRegister (st : HostStore NearState) (r ptr : UInt64) :
    chargesBefore "read_register" st [.i64 r, .i64 ptr] =
      [.ext "base", .ext "read_register_base",
        .ext "read_register_byte" (((st.host.registers r.toNat).map List.length).getD 0),
        .ext "write_memory_base",
        .ext "write_memory_byte" (((st.host.registers r.toNat).map List.length).getD 0)] := by
  have hs : storageMutationPlan? "read_register" st [.i64 r, .i64 ptr] = none := by
    simp [storageMutationPlan?]
  have hpre : "read_register".startsWith "promise_batch_action_" = false := by decide
  simp [chargesBefore, hs, creationAccountArgs, argU64, hpre, chargesBeforeUnvalidated, writeMem]

theorem preInvokeError_registers (name : String) (st : HostStore NearState) (args : List Value)
    (hn : name = "register_len" ∨ name = "read_register" ∨ name = "input") :
    preInvokeError name st args = none := by
  rcases hn with rfl | rfl | rfl <;>
  · simp [preInvokeError, invocationArgumentError, storageMutationPlan?, globalContractInputs?, creationPrefixError,
      creationAccountError, creationAccountArgs, allocatesPromise, functionCallInputError,
      functionCallInputs?]

/-- The three register hosts. -/
def RegisterHost (name : String) : Prop :=
  name = "register_len" ∨ name = "read_register" ∨ name = "input"

/-- The host state after the charges: the charged host with `usedGas` updated. -/
def afterCharges (ns : NearState) : NearState :=
  { ns with context := { ns.context with usedGas := UInt64.ofNat ns.gas.used } }

/-- Post-call metering of a register host leaves its result alone. -/
theorem finish_registers (extra : Nat) {name : String} (hn : RegisterHost name)
    (before : HostStore NearState) (args vals : List Value) (st2 : HostStore NearState) :
    finishMeteredCall extra name before args (.Return vals st2) = .Return vals st2 := by
  rcases hn with rfl | rfl | rfl <;>
  · simp (config := { decide := true }) [finishMeteredCall, chargesAfter, applyCharges, deductDeposit,
      promiseDeposit?, actionMethodEncodingError, actionMethodBytes?, functionCallInputs?, updateStorageUsage]

/-- A register host whose charges fit: the charges, then the functional host. -/
theorem metered_registers (extra : Nat) {name : String} (hn : RegisterHost name) (fn : NearHostFn NearState)
    (st : HostStore NearState) (args : List Value) {C : Nat}
    (h1 : st.host.gas.used + chargesUse st.host (chargesBefore name st args) ≤ C)
    (h2 : C ≤ st.host.gas.maxBurnt) (h3 : C ≤ st.host.gas.prepaid) :
    ∃ ns, ChargedTo st.host ns (chargesUse st.host (chargesBefore name st args)) ∧
      (metered extra name fn).invoke st args =
        finishMeteredCall extra name { mem := st.mem, host := afterCharges ns } args
          (fn.invoke { mem := st.mem, host := afterCharges ns } args) := by
  obtain ⟨hok, hch⟩ := applyCharges_ok st.host (chargesBefore name st args) h1 h2 h3
  have hdep : deprecatedRuntimeHost name = false := by
    rcases hn with rfl | rfl | rfl <;> decide
  have hview : viewRestrictedHost name = false := by
    rcases hn with rfl | rfl | rfl <;> decide
  have hother : ["storage_read", "storage_has_key", "storage_write", "storage_remove"].contains
      name = false := by
    rcases hn with rfl | rfl | rfl <;> decide
  refine ⟨_, hch, ?_⟩
  simp only [metered, hdep, hview, Bool.and_false, Bool.false_eq_true, ite_false]
  generalize hac : applyCharges st.host (chargesBefore name st args) = ac at hok hch ⊢
  obtain ⟨ns, err⟩ := ac
  simp only at hok
  subst hok
  simp only
  rw [preInvokeError_registers name _ _ hn]
  simp only [invokeStorageCall, prepareStorageCall_other _ _ _ hother]
  rfl

theorem erase_afterCharges (ns : NearState) : erase (afterCharges ns) = erase ns := rfl

/-! ## `register_len` -/

/-- What `register_len(r)` returns: the register's length, or `u64Max` when unset. -/
def registerLenResult (h : NearState) (r : UInt64) : Value :=
  match h.registers r.toNat with
  | none => .i64 u64Max
  | some data => .i64 (UInt64.ofNat data.length)

/-- The charges of `register_len`. -/
def registerLenChargeList : List Charge := [.ext "base"]

/-- The gas `register_len` uses. -/
def registerLenUse (h : NearState) : Nat := chargesUse h registerLenChargeList

/-- `register_len(r)`: reads no memory, returns the length of register `r`
(or `u64Max`), and leaves the host as it was but for gas. -/
theorem registerLen_readContract (extra : Nat) (h : NearState) (r : UInt64) (ptr : Nat) {C : Nat} :
    ReadContract (metered extra "register_len" registerLenFn).toHostFn h h
      [.i64 r] [registerLenResult h r] ptr [] (registerLenUse h) C := by
  intro host mem _ he _ hu hmb hpp
  have hcs : chargesBefore "register_len" { mem, host } [.i64 r] = registerLenChargeList :=
    chargesBefore_registerLen _ _
  have huse : registerLenUse host = registerLenUse h := chargesUse_erase he _
  obtain ⟨ns, hch, hinv⟩ := metered_registers extra (name := "register_len") (Or.inl rfl) registerLenFn
    { mem, host } [.i64 r] (C := C) (by rw [hcs]; rw [← huse] at hu; exact hu) hmb hpp
  have hreg : ns.registers = h.registers :=
    erase_field (hch.erase.trans he) NearState.registers fun _ => rfl
  refine ⟨afterCharges ns, ?_, ?_, ?_, hch.maxBurnt, hch.prepaid⟩
  · simp only [NearHostFn.toHostFn, Option.getD_some, hinv]
    simp only [registerLenFn, afterCharges, hreg]
    cases hr : h.registers r.toNat <;> simp only [] <;> rw [finish_registers extra (Or.inl rfl)] <;>
      simp [registerLenResult, hr]
  · rw [erase_afterCharges, hch.erase, he]
  · show ns.gas.used ≤ _
    rw [hch.used, hcs]
    show _ ≤ host.gas.used + registerLenUse h
    rw [← huse]; exact Nat.le_refl _

/-! ## `read_register` -/

/-- The charges of `read_register` of a register of `n` bytes. -/
def readRegisterChargeList (n : Nat) : List Charge :=
  [.ext "base", .ext "read_register_base", .ext "read_register_byte" n, .ext "write_memory_base",
    .ext "write_memory_byte" n]

/-- The gas `read_register` of a register of `n` bytes uses. -/
def readRegisterUse (h : NearState) (n : Nat) : Nat := chargesUse h (readRegisterChargeList n)

/-- `read_register(r, ptr)` with register `r` holding the nonempty `data`:
replaces the `data.length` bytes `old` at `ptr` by `data`, returns nothing, and
leaves the host as it was but for gas. -/
theorem readRegister_rwContract (extra : Nat) (h : NearState) (r ptr : UInt64) (data old : List UInt8)
    {C : Nat} (hreg : h.registers r.toNat = some data) (hold : old.length = data.length)
    (hpos : 0 < data.length) :
    RWContract (metered extra "read_register" readRegisterFn).toHostFn h h
      [.i64 r, .i64 ptr] [] ptr.toNat old data (readRegisterUse h data.length) C := by
  intro host mem hwf he hrd hu hmb hpp
  have hreg' : host.registers r.toNat = some data := by
    rw [erase_field he NearState.registers fun _ => rfl]; exact hreg
  have hcs : chargesBefore "read_register" { mem, host } [.i64 r, .i64 ptr] =
      readRegisterChargeList data.length := by
    rw [chargesBefore_readRegister]; simp [hreg', readRegisterChargeList]
  have huse : readRegisterUse host data.length = readRegisterUse h data.length := chargesUse_erase he _
  obtain ⟨ns, hch, hinv⟩ := metered_registers extra (name := "read_register") (Or.inr (Or.inl rfl))
    readRegisterFn { mem, host } [.i64 r, .i64 ptr] (C := C)
    (by rw [hcs]; rw [← huse] at hu; exact hu) hmb hpp
  have hreg'' : ns.registers = h.registers :=
    erase_field (hch.erase.trans he) NearState.registers fun _ => rfl
  have hin : ptr.toNat + data.length ≤ mem.byteSize := by
    have := (hrd (data.length - 1) (by omega)).1
    omega
  have hin' : ¬ ptr.toNat + data.length > mem.size * 65536 := by
    unfold Memory.byteSize at hin
    show ¬ _ > mem.pages.size * 65536
    unfold pageSize at hin
    omega
  refine ⟨afterCharges ns, mem.writeList ptr.toNat data, ?_, writeList_spec hwf hin, ?_, ?_,
    hch.maxBurnt, hch.prepaid⟩
  · simp only [NearHostFn.toHostFn, Option.getD_some, hinv]
    simp only [readRegisterFn, afterCharges, hreg'', hreg, memBytes, hin', ite_false]
    rw [finish_registers extra (Or.inr (Or.inl rfl))]
  · rw [erase_afterCharges, hch.erase, he]
  · show ns.gas.used ≤ _
    rw [hch.used, hcs]
    show _ ≤ host.gas.used + readRegisterUse h data.length
    rw [← huse]; exact Nat.le_refl _

/-! ## `input` -/

/-- The host after `input(r)`: register `r` holds the call's input (nothing
happens for the sentinel register `u64Max`). -/
def inputHost (h : NearState) (r : UInt64) : NearState :=
  if r = u64Max then h else h.setRegister r.toNat h.context.input

/-- The charges of `input`: nearcore shares the input buffer with the
register, without a byte copy. -/
def inputChargeList : List Charge := [.ext "base", .ext "write_register_base"]

/-- The gas `input` uses. -/
def inputUse (h : NearState) : Nat := chargesUse h inputChargeList

theorem erase_inputHost {h h' : NearState} (he : erase h = erase h') (r : UInt64) :
    erase (inputHost h r) = erase (inputHost h' r) := by
  have hi : h.context.input = h'.context.input :=
    erase_field he (fun x : NearState => x.context.input) fun _ => rfl
  have hs : ∀ (x : NearState) (i : Nat) (d : List UInt8), erase (x.setRegister i d) = (erase x).setRegister i d :=
    fun _ _ _ => rfl
  unfold inputHost
  split
  · exact he
  · rw [hs, hs, he, hi]

/-- `input(r)` within the register size limit: reads no memory, returns
nothing, and sets register `r` to the call's input (`inputHost`). -/
theorem input_readContract (extra : Nat) (h : NearState) (r : UInt64) (ptr : Nat) {C : Nat}
    (hlim : withinLimit h.config.maxRegisterLen h.context.input.length = true) :
    ReadContract (metered extra "input" inputFn).toHostFn h (inputHost h r)
      [.i64 r] [] ptr [] (inputUse h) C := by
  intro host mem _ he _ hu hmb hpp
  have hcs : chargesBefore "input" { mem, host } [.i64 r] = inputChargeList :=
    chargesBefore_input _ _
  have huse : inputUse host = inputUse h := chargesUse_erase he _
  obtain ⟨ns, hch, hinv⟩ := metered_registers extra (name := "input") (Or.inr (Or.inr rfl)) inputFn
    { mem, host } [.i64 r] (C := C) (by rw [hcs]; rw [← huse] at hu; exact hu) hmb hpp
  have hens : erase ns = erase h := hch.erase.trans he
  have hcfg : ns.config = h.config := erase_field hens NearState.config fun _ => rfl
  have hinp : ns.context.input = h.context.input :=
    erase_field hens (fun x : NearState => x.context.input) fun _ => rfl
  refine ⟨inputHost (afterCharges ns) r, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [NearHostFn.toHostFn, Option.getD_some, hinv]
    simp only [inputFn, writeRegisterResult, checkedSetRegister?]
    by_cases hr : r = u64Max
    · simp only [hr, ite_true]
      rw [finish_registers extra (Or.inr (Or.inr rfl))]
      simp [inputHost]
    · have hl : withinLimit (afterCharges ns).config.maxRegisterLen
          (afterCharges ns).context.input.length = true := by
        simp only [afterCharges, hcfg, hinp]; exact hlim
      simp only [hr, ite_false, hl, ite_true]
      rw [finish_registers extra (Or.inr (Or.inr rfl))]
      simp [inputHost, hr]
  · rw [erase_inputHost (erase_afterCharges ns) r, erase_inputHost hens r]
  · unfold inputHost; split <;> (show ns.gas.used ≤ _; rw [hch.used, hcs, ← huse]; exact Nat.le_refl _)
  · unfold inputHost; split <;> exact hch.maxBurnt
  · unfold inputHost; split <;> exact hch.prepaid

end NearLogic
