import NearVM.MeteredHosts.Output

/-! Exact register length and whole-register copy contracts for the metered hosts. -/
namespace Wasm.Near.MeteredHosts.RegisterRead

/-- Actual charges for a whole-register memory copy. -/
def readCharges (length : Nat) : List Charge :=
  [.ext "base", .ext "read_register_base", .ext "read_register_byte" length,
   .ext "write_memory_base", .ext "write_memory_byte" length]

def paid (st : HostStore NearState) (charges : List Charge) : HostStore NearState :=
  Output.paidStore st (applyCharges st.host charges).1

def lengthValue (st : HostStore NearState) (register : UInt64) : UInt64 :=
  ((st.host.registers register.toNat).map (fun xs => UInt64.ofNat xs.length)).getD u64Max

theorem raw_length (st : HostStore NearState) (register : UInt64) :
    registerLenFn.invoke st [.i64 register] = .Return [.i64 (lengthValue st register)] st := by
  simp only [registerLenFn, lengthValue]
  cases st.host.registers register.toNat <;> rfl

theorem raw_read (st : HostStore NearState) (register ptr : UInt64) (bytes : List UInt8)
    (hreg : st.host.registers register.toNat = some bytes)
    (hspan : ptr.toNat + bytes.length ≤ st.mem.byteSize) :
    readRegisterFn.invoke st [.i64 register, .i64 ptr] =
      .Return [] { st with mem := st.mem.writeList ptr.toNat bytes } := by
  have hb : ¬ ptr.toNat + bytes.length > st.mem.size * 65536 := Nat.not_lt_of_ge hspan
  simp only [readRegisterFn, hreg, memBytes, hb, ↓reduceIte]

theorem length_charges (st : HostStore NearState) (args : List Value) :
    chargesBefore "register_len" st args = [.ext "base"] := by
  simp [chargesBefore, storageMutationPlan?, creationAccountArgs, chargesBeforeUnvalidated]

theorem read_charges (st : HostStore NearState) (register ptr : UInt64) (bytes : List UInt8)
    (hreg : st.host.registers register.toNat = some bytes) :
    chargesBefore "read_register" st [.i64 register, .i64 ptr] = readCharges bytes.length := by
  simp [chargesBefore, storageMutationPlan?, creationAccountArgs, chargesBeforeUnvalidated,
    argU64, hreg, readCharges, writeMem]

theorem pre_length (st : HostStore NearState) (args : List Value) :
    preInvokeError "register_len" st args = none := by
  rfl

theorem pre_read (st : HostStore NearState) (args : List Value) :
    preInvokeError "read_register" st args = none := by
  rfl

theorem finish_length (extra : Nat) (before : HostStore NearState) (args : List Value)
    (result : HostResult NearState) :
    finishMeteredCall extra "register_len" before args result = result := by
  cases result <;> simp [finishMeteredCall, chargesAfter, cryptoHostNames, applyCharges,
    deductDeposit, promiseDeposit?, actionMethodEncodingError, actionMethodBytes?,
    usesKeyMethodFields, functionCallInputs?, updateStorageUsage]

theorem finish_read (extra : Nat) (before : HostStore NearState) (args : List Value)
    (result : HostResult NearState) :
    finishMeteredCall extra "read_register" before args result = result := by
  cases result <;> simp [finishMeteredCall, chargesAfter, cryptoHostNames, applyCharges,
    deductDeposit, promiseDeposit?, actionMethodEncodingError, actionMethodBytes?,
    usesKeyMethodFields, functionCallInputs?, updateStorageUsage]

theorem metered_length_eq (extra : Nat) (st : HostStore NearState) (register : UInt64) :
    (metered extra "register_len" registerLenFn).invoke st [.i64 register] =
      match (applyCharges st.host [.ext "base"]).2 with
      | some error => trapWith (paid st [.ext "base"]) error
      | none => registerLenFn.invoke (paid st [.ext "base"]) [.i64 register] := by
  simp only [metered, show deprecatedRuntimeHost "register_len" = false by decide,
    show viewRestrictedHost "register_len" = false by decide, Bool.false_eq_true,
    Bool.and_false, ↓reduceIte, length_charges, paid, Output.paidStore]
  cases hc : applyCharges st.host [.ext "base"] with
  | mk ns error =>
    cases error with
    | some error => rfl
    | none => simp only [pre_length, invokeStorageCall,
        prepareStorageCall_other "register_len" _ _ (by decide), finish_length]

theorem metered_read_eq (extra : Nat) (st : HostStore NearState) (register ptr : UInt64)
    (bytes : List UInt8) (hreg : st.host.registers register.toNat = some bytes) :
    (metered extra "read_register" readRegisterFn).invoke st [.i64 register, .i64 ptr] =
      match (applyCharges st.host (readCharges bytes.length)).2 with
      | some error => trapWith (paid st (readCharges bytes.length)) error
      | none => readRegisterFn.invoke (paid st (readCharges bytes.length)) [.i64 register, .i64 ptr] := by
  simp only [metered, show deprecatedRuntimeHost "read_register" = false by decide,
    show viewRestrictedHost "read_register" = false by decide, Bool.false_eq_true,
    Bool.and_false, ↓reduceIte, read_charges st register ptr bytes hreg, paid, Output.paidStore]
  cases hc : applyCharges st.host (readCharges bytes.length) with
  | mk ns error =>
    cases error with
    | some error => rfl
    | none => simp only [pre_read, invokeStorageCall,
        prepareStorageCall_other "read_register" _ _ (by decide), finish_read]

/-- Billing preserves every register even when the offered credits are insufficient. -/
theorem paid_registers (st : HostStore NearState) (charges : List Charge)
    (hburn : ∀ c ∈ charges, BurnsOnly c) :
    (paid st charges).host.registers = st.host.registers := by
  have h := congrArg NearState.registers (applyCharges_frame st.host charges hburn)
  simpa only [paid, Output.paidStore] using h

theorem paid_credits (st : HostStore NearState) (charges : List Charge) (rest : Nat)
    (hburn : ∀ c ∈ charges, BurnsOnly c)
    (hcredits : st.host.gas.Credits (burnSum st.host.extCosts charges + rest)) :
    (applyCharges st.host charges).2 = none ∧
    (paid st charges).host.gas.burnt = st.host.gas.burnt + burnSum st.host.extCosts charges ∧
    (paid st charges).host.gas.promises = st.host.gas.promises ∧
    (paid st charges).host.gas.Credits rest := by
  have h := applyCharges_credits st.host charges rest hburn hcredits
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩

theorem readCharges_burns (length : Nat) : ∀ c ∈ readCharges length, BurnsOnly c := by
  simp [readCharges, BurnsOnly]

/-- Length queries preserve all functional state, return the actual length or sentinel,
and retain the caller's unused credits. -/
theorem length_contract (extra : Nat) (st : HostStore NearState) (register : UInt64) (rest : Nat)
    (hcredits : st.host.gas.Credits (burnSum st.host.extCosts [.ext "base"] + rest)) :
    (metered extra "register_len" registerLenFn).invoke st [.i64 register] =
      .Return [.i64 (lengthValue st register)] (paid st [.ext "base"]) ∧
    (paid st [.ext "base"]).host.gas.burnt = st.host.gas.burnt + burnSum st.host.extCosts [.ext "base"] ∧
    (paid st [.ext "base"]).host.gas.promises = st.host.gas.promises ∧
    (paid st [.ext "base"]).host.gas.Credits rest := by
  have hb : ∀ c ∈ [.ext "base"], BurnsOnly c := by simp [BurnsOnly]
  have hp := paid_credits st [.ext "base"] rest hb hcredits
  refine ⟨?_, hp.2⟩
  rw [metered_length_eq, hp.1, raw_length]
  simp only [lengthValue, paid_registers st _ hb]

/-- The actual whole-register memory write, with exact gas and residual credit frame. -/
theorem read_contract (extra : Nat) (st : HostStore NearState) (register ptr : UInt64)
    (bytes : List UInt8) (rest : Nat)
    (hreg : st.host.registers register.toNat = some bytes)
    (hspan : ptr.toNat + bytes.length ≤ st.mem.byteSize)
    (hcredits : st.host.gas.Credits (burnSum st.host.extCosts (readCharges bytes.length) + rest)) :
    let final := { paid st (readCharges bytes.length) with mem := st.mem.writeList ptr.toNat bytes }
    (metered extra "read_register" readRegisterFn).invoke st [.i64 register, .i64 ptr] = .Return [] final ∧
    final.host.registers = st.host.registers ∧
    final.host.gas.burnt = st.host.gas.burnt + burnSum st.host.extCosts (readCharges bytes.length) ∧
    final.host.gas.promises = st.host.gas.promises ∧ final.host.gas.Credits rest := by
  have hb := readCharges_burns bytes.length
  have hp := paid_credits st (readCharges bytes.length) rest hb hcredits
  refine ⟨?_, paid_registers st _ hb, hp.2⟩
  rw [metered_read_eq extra st register ptr bytes hreg, hp.1]
  apply raw_read
  · rw [paid_registers st _ hb]; exact hreg
  · exact hspan

end Wasm.Near.MeteredHosts.RegisterRead
