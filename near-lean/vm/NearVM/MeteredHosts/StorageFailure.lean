import NearVM.MeteredHosts.StorageFrame

/-!
# Storage length rejection before trie access

The actual ordered validator stops at the key limit before reading the value,
and at the value limit before looking up the trie. These contracts retain
argument-reading charges and exact residual credits on ordinary host errors.
-/
namespace Wasm.Near.MeteredHosts.StorageFailure
open StorageMetered

/-- Charges through the key read, before the first length check. -/
def keyCharges (before : HostStore NearState) (keyLen keyPtr : UInt64) : List Charge :=
  [.ext "base", .ext "storage_write_base"] ++ readSpan before keyLen keyPtr

/-- The value is read only after the key length was accepted. -/
def valueCharges (before : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) : List Charge :=
  keyCharges before keyLen keyPtr ++ readSpan before valueLen valuePtr

/-- Deterministic paid store before validation, including used-gas synchronization. -/
def paid (before : HostStore NearState) (charges : List Charge) : HostStore NearState :=
  Output.paidStore before (applyCharges before.host charges).1

/-- The trap records its structured error and preserves all other paid resources. -/
def rejected (before : HostStore NearState) (charges : List Charge) (error : HostError) :
    HostStore NearState :=
  let st := paid before charges
  { st with host := { st.host with lastError := some error } }

theorem key_plan (before : HostStore NearState) (keyLen keyPtr valueLen valuePtr : UInt64)
    (key : List UInt8) (limit : Nat)
    (hkey : getMemOrReg before keyPtr keyLen = some key)
    (hlimit : before.host.config.maxStorageKeyLen = some limit) (hlong : limit < key.length) :
    storageMutationPlan? "storage_write" before (args keyLen keyPtr valueLen valuePtr) =
      some { charges := keyCharges before keyLen keyPtr, error := some (.keyLengthExceeded key.length limit) } := by
  simp [storageMutationPlan?, args, argU64, hkey, hlimit, hlong, keyCharges]

theorem value_plan (before : HostStore NearState) (keyLen keyPtr valueLen valuePtr : UInt64)
    (key value : List UInt8) (limit : Nat)
    (hkey : getMemOrReg before keyPtr keyLen = some key)
    (hkeyLimit : ∀ n, before.host.config.maxStorageKeyLen = some n → key.length ≤ n)
    (hvalue : getMemOrReg before valuePtr valueLen = some value)
    (hlimit : before.host.config.maxStorageValueLen = some limit) (hlong : limit < value.length) :
    storageMutationPlan? "storage_write" before (args keyLen keyPtr valueLen valuePtr) =
      some { charges := valueCharges before keyLen keyPtr valueLen valuePtr, error := some (.valueLengthExceeded value.length limit) } := by
  cases hk : before.host.config.maxStorageKeyLen with
  | none => simp [storageMutationPlan?, args, argU64, hkey, hk, hvalue, hlimit, hlong, valueCharges, keyCharges]
  | some n =>
    have hn := Nat.not_lt.mpr (hkeyLimit n hk)
    simp [storageMutationPlan?, args, argU64, hkey, hk, hn, hvalue, hlimit, hlong, valueCharges, keyCharges]

private theorem plan_charges (before : HostStore NearState) (arguments : List Value)
    (charges : List Charge) (error : HostError)
    (h : storageMutationPlan? "storage_write" before arguments = some {charges, error := some error}) :
    chargesBefore "storage_write" before arguments = charges := by
  simp only [chargesBefore, h]

private theorem plan_error (before : HostStore NearState) (arguments : List Value)
    (charges : List Charge) (error : HostError)
    (h : storageMutationPlan? "storage_write" before arguments = some {charges, error := some error}) :
    preInvokeError "storage_write" before arguments = some error := by
  simp only [preInvokeError, invocationArgumentError, h]

private theorem frame_read {before after : HostStore NearState} (h : StorageFrame.Frame before after)
    (len ptr : UInt64) : getMemOrReg after ptr len = getMemOrReg before ptr len := by
  simp only [getMemOrReg, h.1, h.registers]

private theorem readSpan_burns (before : HostStore NearState) (len ptr : UInt64) :
    ∀ c ∈ readSpan before len ptr, BurnsOnly c := by
  unfold readSpan
  split
  · split <;> simp [BurnsOnly]
  · simp [BurnsOnly]

theorem keyCharges_burns (before : HostStore NearState) (len ptr : UInt64) :
    ∀ c ∈ keyCharges before len ptr, BurnsOnly c := by
  simpa [keyCharges, BurnsOnly] using readSpan_burns before len ptr

theorem valueCharges_burns (before : HostStore NearState) (kl kp vl vp : UInt64) :
    ∀ c ∈ valueCharges before kl kp vl vp, BurnsOnly c := by
  simp only [valueCharges, List.mem_append]
  intro c hc
  rcases hc with hk | hv
  · exact keyCharges_burns before kl kp c hk
  · exact readSpan_burns before vl vp c hv

/-- Rejection changes only billing diagnostics, used gas and the structured
host error; storage and the complete trie remain untouched. -/
theorem rejected_fields (before : HostStore NearState) (charges : List Charge)
    (error : HostError) (hburn : ∀ c ∈ charges, BurnsOnly c) :
    (rejected before charges error).mem = before.mem ∧
    (rejected before charges error).host.storage = before.host.storage ∧
    (rejected before charges error).host.storageAccounting = before.host.storageAccounting ∧
    (rejected before charges error).host.logs = before.host.logs ∧
    (rejected before charges error).host.lastError = some error ∧
    (rejected before charges error).host.lastExecutionIssue = before.host.lastExecutionIssue := by
  have hf := applyCharges_frame before.host charges hburn
  have hs := congrArg NearState.storage hf
  have ht := congrArg NearState.storageAccounting hf
  have hl := congrArg NearState.logs hf
  have hi := congrArg NearState.lastExecutionIssue hf
  exact ⟨rfl, hs, ht, hl, rfl, hi⟩

private theorem metered_error (extra : Nat) (before : HostStore NearState)
    (arguments : List Value) (charges : List Charge) (error : HostError)
    (hview : before.host.context.isView = false)
    (hplan : chargesBefore "storage_write" before arguments = charges)
    (hcharge : (applyCharges before.host charges).2 = none)
    (herror : preInvokeError "storage_write" (paid before charges) arguments = some error) :
    (metered extra "storage_write" storageWriteFn).invoke before arguments =
      .Trap (rejected before charges error) error.message := by
  simp only [metered, show deprecatedRuntimeHost "storage_write" = false by decide,
    hview, Bool.false_and, Bool.false_eq_true, ↓reduceIte, hplan, hcharge]
  change (match preInvokeError "storage_write" (paid before charges) arguments with
    | some e => trapWith (paid before charges) e
    | none => _) = _
  rw [herror]
  rfl

/-- Exact billing and residual credits on any validated pre-trie rejection. -/
theorem rejected_gas (before : HostStore NearState) (charges : List Charge)
    (error : HostError) (rest : Nat) (hburn : ∀ c ∈ charges, BurnsOnly c)
    (hcredits : before.host.gas.Credits (burnSum before.host.extCosts charges + rest)) :
    (rejected before charges error).host.gas.burnt = before.host.gas.burnt + burnSum before.host.extCosts charges ∧
    (rejected before charges error).host.gas.promises = before.host.gas.promises ∧
    (rejected before charges error).host.gas.Credits rest := by
  have h := applyCharges_credits before.host charges rest hburn hcredits
  exact ⟨h.2.1, h.2.2.1, h.2.2.2.2⟩

/-- Key rejection runs no trie operation and never reads the value span. -/
theorem metered_key_too_long (extra : Nat) (before : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key : List UInt8) (limit rest : Nat)
    (hview : before.host.context.isView = false)
    (hkey : getMemOrReg before keyPtr keyLen = some key)
    (hlimit : before.host.config.maxStorageKeyLen = some limit) (hlong : limit < key.length)
    (hcredits : before.host.gas.Credits
      (burnSum before.host.extCosts (keyCharges before keyLen keyPtr) + rest)) :
    (metered extra "storage_write" storageWriteFn).invoke before (args keyLen keyPtr valueLen valuePtr) =
      .Trap (rejected before (keyCharges before keyLen keyPtr) (.keyLengthExceeded key.length limit))
        (HostError.keyLengthExceeded key.length limit).message := by
  let charges := keyCharges before keyLen keyPtr
  have hburn : ∀ c ∈ charges, BurnsOnly c := by
    simpa [charges, keyCharges, BurnsOnly] using readSpan_burns before keyLen keyPtr
  have hf := StorageFrame.prepayment_frame before charges hburn
  have hp := applyCharges_credits before.host charges rest hburn hcredits
  apply metered_error extra before _ charges _ hview
    (plan_charges before _ charges _ (key_plan before _ _ _ _ key limit hkey hlimit hlong)) hp.1
  apply plan_error (paid before charges) _ (keyCharges (paid before charges) keyLen keyPtr) _
  apply key_plan
  · exact (frame_read hf keyLen keyPtr).trans hkey
  · exact (congrArg (fun c => c.maxStorageKeyLen) hf.config).trans hlimit
  · exact hlong

/-- Value rejection runs no trie operation after reading both argument spans. -/
theorem metered_value_too_long (extra : Nat) (before : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : List UInt8) (limit rest : Nat)
    (hview : before.host.context.isView = false)
    (hkey : getMemOrReg before keyPtr keyLen = some key)
    (hkeyLimit : ∀ n, before.host.config.maxStorageKeyLen = some n → key.length ≤ n)
    (hvalue : getMemOrReg before valuePtr valueLen = some value)
    (hlimit : before.host.config.maxStorageValueLen = some limit) (hlong : limit < value.length)
    (hcredits : before.host.gas.Credits
      (burnSum before.host.extCosts (valueCharges before keyLen keyPtr valueLen valuePtr) + rest)) :
    (metered extra "storage_write" storageWriteFn).invoke before (args keyLen keyPtr valueLen valuePtr) =
      .Trap (rejected before (valueCharges before keyLen keyPtr valueLen valuePtr)
        (.valueLengthExceeded value.length limit)) (HostError.valueLengthExceeded value.length limit).message := by
  let charges := valueCharges before keyLen keyPtr valueLen valuePtr
  have hburn : ∀ c ∈ charges, BurnsOnly c := by
    simp only [charges, valueCharges, keyCharges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    intro c hc
    rcases hc with ((rfl | rfl) | hk) | hv
    · trivial
    · trivial
    · exact readSpan_burns before keyLen keyPtr c hk
    · exact readSpan_burns before valueLen valuePtr c hv
  have hf := StorageFrame.prepayment_frame before charges hburn
  have hp := applyCharges_credits before.host charges rest hburn hcredits
  apply metered_error extra before _ charges _ hview
    (plan_charges before _ charges _ (value_plan before _ _ _ _ key value limit hkey hkeyLimit hvalue hlimit hlong)) hp.1
  apply plan_error (paid before charges) _ (valueCharges (paid before charges) keyLen keyPtr valueLen valuePtr) _
  apply value_plan
  · exact (frame_read hf keyLen keyPtr).trans hkey
  · intro n hn
    exact hkeyLimit n ((congrArg (fun c => c.maxStorageKeyLen) hf.config).symm.trans hn)
  · exact (frame_read hf valueLen valuePtr).trans hvalue
  · exact (congrArg (fun c => c.maxStorageValueLen) hf.config).trans hlimit
  · exact hlong

end Wasm.Near.MeteredHosts.StorageFailure
