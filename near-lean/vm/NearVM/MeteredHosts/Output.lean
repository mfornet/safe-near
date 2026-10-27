import NearVM.Metered
import NearVM.MeteredHosts.Charges

/-!
# Output host contracts

These equations specify the actual functional and metered output hosts.
Successful equations preserve the complete store except the stated log or
return-selector fields. Failure equations record the exact store and error;
rollback of account effects belongs to the receipt boundary.
-/

namespace Wasm.Near.MeteredHosts.Output

/-- Decoding and log-limit validation precede the append. The full store
update frames linear memory, storage, registers and every other host field. -/
theorem logUtf8_ok (st : HostStore NearState) (len ptr : UInt64) (msg : List UInt8)
    (hread : (logUtf8Read st len ptr).result = .ok msg) :
    logUtf8Fn.invoke st [.i64 len, .i64 ptr] =
      .Return [] { st with host := { st.host with logs := st.host.logs ++ [msg] } } := by
  simp only [logUtf8Fn, hread, appendLogResult]

/-- No log is appended on a decoding, memory or log-limit failure. -/
theorem logUtf8_error (st : HostStore NearState) (len ptr : UInt64) (error : HostError)
    (hread : (logUtf8Read st len ptr).result = .error error) :
    logUtf8Fn.invoke st [.i64 len, .i64 ptr] =
      .Trap { st with host := { st.host with lastError := some error } } error.message := by
  simp only [logUtf8Fn, hread, appendLogResult]

/-- Number-of-logs rejection happens before reading any memory. -/
theorem logUtf8_count_error (st : HostStore NearState) (len ptr : UInt64) (limit : Nat)
    (hlimit : st.host.config.maxNumberLogs = some limit) (hcount : limit ≤ st.host.logs.length) :
    logUtf8Fn.invoke st [.i64 len, .i64 ptr] =
      .Trap { st with host := { st.host with lastError := some (.numberOfLogsExceeded limit) } }
        (HostError.numberOfLogsExceeded limit).message := by
  apply logUtf8_error
  simp [logUtf8Read, logCountError, hlimit, hcount]

/-- A successful memory read and UTF-8 decode still require room for the
message in the cumulative log length. -/
theorem logUtf8_of_read (st : HostStore NearState) (len ptr : UInt64) (msg : List UInt8)
    (hcount : logCountError st = none)
    (hread : (readUtf8String st len ptr).result = .ok msg)
    (hspace : ∀ limit, st.host.config.maxLogLen = some limit →
      totalLogLength st + msg.length ≤ limit) :
    logUtf8Fn.invoke st [.i64 len, .i64 ptr] =
      .Return [] { st with host := { st.host with logs := st.host.logs ++ [msg] } } := by
  apply logUtf8_ok
  simp only [logUtf8Read, hcount, hread, finishLog]
  cases hlimit : st.host.config.maxLogLen with
  | none => rfl
  | some limit => simp [Nat.not_lt_of_ge (hspace limit hlimit)]

/-- A selected return value replaces any earlier value or promise selection.
Everything else, including memory, is preserved by the full store equation. -/
theorem valueReturn_ok (st : HostStore NearState) (len ptr : UInt64) (bytes : List UInt8)
    (hread : getMemOrReg st ptr len = some bytes)
    (hlimit : withinLimit st.host.config.maxReturnLen bytes.length = true) :
    valueReturnFn.invoke st [.i64 len, .i64 ptr] =
      .Return [] { st with host := { st.host with returnData := some bytes, returnedPromise := none } } := by
  simp only [valueReturnFn, hread, checkDataLimit, hlimit, ↓reduceIte, NearState.selectReturnValue]

/-- The `u64::MAX` sentinel reads the register, without copying it to memory. -/
theorem valueReturn_register (st : HostStore NearState) (register : UInt64) (bytes : List UInt8)
    (hregister : st.host.registers register.toNat = some bytes)
    (hlimit : withinLimit st.host.config.maxReturnLen bytes.length = true) :
    valueReturnFn.invoke st [.i64 u64Max, .i64 register] =
      .Return [] { st with host := { st.host with returnData := some bytes, returnedPromise := none } } :=
  valueReturn_ok st u64Max register bytes (by simp only [getMemOrReg, ↓reduceIte, hregister]) hlimit

/-- A failed memory-or-register read leaves the complete store unchanged. -/
theorem valueReturn_read_error (st : HostStore NearState) (len ptr : UInt64)
    (hread : getMemOrReg st ptr len = none) :
    valueReturnFn.invoke st [.i64 len, .i64 ptr] = .Trap st "value_return: invalid register" := by
  simp only [valueReturnFn, hread]

/-- The exact length-limit branch preserves the previous return selection
and records the length error. -/
theorem valueReturn_length_error (st : HostStore NearState) (len ptr : UInt64)
    (bytes : List UInt8) (limit : Nat) (hread : getMemOrReg st ptr len = some bytes)
    (hlimit : st.host.config.maxReturnLen = some limit) (hlength : limit < bytes.length) :
    valueReturnFn.invoke st [.i64 len, .i64 ptr] =
      .Trap { st with host := { st.host with
        lastError := some (.returnedValueLengthExceeded bytes.length limit) } }
        "value_return: return size exceeded" := by
  simp [valueReturnFn, hread, checkDataLimit, withinLimit, hlimit, Nat.not_le_of_gt hlength]
  rfl

/-- Output hosts do not need any post-invocation charges or storage adjustment. -/
theorem finish_logUtf8 (extra : Nat) (before : HostStore NearState) (args : List Value)
    (result : HostResult NearState) :
    finishMeteredCall extra "log_utf8" before args result = result := by
  cases result with
  | Trap st msg => rfl
  | Return values st =>
      simp [finishMeteredCall, chargesAfter, applyCharges, deductDeposit, promiseDeposit?,
        actionMethodEncodingError, actionMethodBytes?, usesKeyMethodFields, functionCallInputs?,
        cryptoHostNames, updateStorageUsage]

theorem finish_valueReturn (extra : Nat) (before : HostStore NearState) (args : List Value)
    (result : HostResult NearState) :
    finishMeteredCall extra "value_return" before args result = result := by
  cases result with
  | Trap st msg => rfl
  | Return values st =>
      simp [finishMeteredCall, chargesAfter, applyCharges, deductDeposit, promiseDeposit?,
        actionMethodEncodingError, actionMethodBytes?, usesKeyMethodFields, functionCallInputs?,
        cryptoHostNames, updateStorageUsage]

/-- The wrapper updates the guest's `used_gas` context after paying the
pre-invocation charges; memory is unchanged. -/
def paidStore (st : HostStore NearState) (paid : NearState) : HostStore NearState :=
  { st with host := { paid with context := { paid.context with usedGas := UInt64.ofNat paid.gas.used } } }

/-- No hidden post-call effects remain for logging. Both successful and
failed charge branches retain the exact charged store. -/
theorem metered_logUtf8_eq (extra : Nat) (st : HostStore NearState) (args : List Value) :
    (metered extra "log_utf8" logUtf8Fn).invoke st args =
      match applyCharges st.host (chargesBefore "log_utf8" st args) with
      | (paid, some error) => trapWith (paidStore st paid) error
      | (paid, none) => logUtf8Fn.invoke (paidStore st paid) args := by
  have hp (st' : HostStore NearState) : preInvokeError "log_utf8" st' args = none := rfl
  simp only [metered, show deprecatedRuntimeHost "log_utf8" = false by decide,
    show viewRestrictedHost "log_utf8" = false by decide, Bool.and_false, Bool.false_eq_true,
    ↓reduceIte]
  cases hc : applyCharges st.host (chargesBefore "log_utf8" st args) with
  | mk paid error =>
      cases error <;> simp only [hp, invokeStorageCall,
        prepareStorageCall_other "log_utf8" _ _ (by decide), finish_logUtf8] <;> rfl

/-- Returning a value also has no post-call charges. Invalid reads are
reported by pre-invocation validation, before the functional host runs. -/
theorem metered_valueReturn_eq (extra : Nat) (st : HostStore NearState) (args : List Value) :
    (metered extra "value_return" valueReturnFn).invoke st args =
      match applyCharges st.host (chargesBefore "value_return" st args) with
      | (paid, some error) => trapWith (paidStore st paid) error
      | (paid, none) =>
        match preInvokeError "value_return" (paidStore st paid) args with
        | some error => trapWith (paidStore st paid) error
        | none => valueReturnFn.invoke (paidStore st paid) args := by
  simp only [metered, show deprecatedRuntimeHost "value_return" = false by decide,
    show viewRestrictedHost "value_return" = false by decide, Bool.and_false, Bool.false_eq_true,
    ↓reduceIte]
  cases hc : applyCharges st.host (chargesBefore "value_return" st args) with
  | mk paid error =>
      cases error <;> simp only [invokeStorageCall,
        prepareStorageCall_other "value_return" _ _ (by decide), finish_valueReturn] <;> rfl

/-- A valid span passes pre-invocation validation for `value_return`. -/
theorem preInvoke_valueReturn_ok (st : HostStore NearState) (len ptr : UInt64) (bytes : List UInt8)
    (hread : getMemOrReg st ptr len = some bytes) :
    preInvokeError "value_return" st [.i64 len, .i64 ptr] = none := by
  change (match (if (getMemOrReg st ptr len).isNone then some (spanReadError len ptr) else none) with
    | some error => some error | none => none) = none
  simp only [hread, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]

/-- Logging after successful gas payment changes only the logs, in addition
to the wrapper's explicit gas/profile/context updates. -/
theorem metered_logUtf8_ok (extra : Nat) (st : HostStore NearState) (len ptr : UInt64)
    (paid : NearState) (msg : List UInt8)
    (hcharge : applyCharges st.host (chargesBefore "log_utf8" st [.i64 len, .i64 ptr]) = (paid, none))
    (hread : (logUtf8Read (paidStore st paid) len ptr).result = .ok msg) :
    (metered extra "log_utf8" logUtf8Fn).invoke st [.i64 len, .i64 ptr] =
      .Return [] { paidStore st paid with host :=
        { (paidStore st paid).host with logs := (paidStore st paid).host.logs ++ [msg] } } := by
  rw [metered_logUtf8_eq, hcharge]
  exact logUtf8_ok _ _ _ _ hread

/-- A successfully charged return selects the validated bytes and clears an
earlier promise return, preserving all other paid-store fields. -/
theorem metered_valueReturn_ok (extra : Nat) (st : HostStore NearState) (len ptr : UInt64)
    (paid : NearState) (bytes : List UInt8)
    (hcharge : applyCharges st.host (chargesBefore "value_return" st [.i64 len, .i64 ptr]) = (paid, none))
    (hread : getMemOrReg (paidStore st paid) ptr len = some bytes)
    (hlimit : withinLimit paid.config.maxReturnLen bytes.length = true) :
    (metered extra "value_return" valueReturnFn).invoke st [.i64 len, .i64 ptr] =
      .Return [] { paidStore st paid with host :=
        { (paidStore st paid).host with returnData := some bytes, returnedPromise := none } } := by
  rw [metered_valueReturn_eq, hcharge]
  simp only [preInvoke_valueReturn_ok _ _ _ _ hread]
  exact valueReturn_ok _ _ _ _ hread hlimit

/-- The string-reader's ordered external-cost plan is exactly what the
wrapper charges; failed decoding still pays that prefix. -/
theorem chargesBefore_logUtf8 (st : HostStore NearState) (len ptr : UInt64) :
    chargesBefore "log_utf8" st [.i64 len, .i64 ptr] =
      extCharges (logUtf8Read st len ptr).charges := by
  rfl

theorem logUtf8_burnsOnly (st : HostStore NearState) (len ptr : UInt64) :
    ∀ charge ∈ chargesBefore "log_utf8" st [.i64 len, .i64 ptr], BurnsOnly charge := by
  rw [chargesBefore_logUtf8]
  simp only [extCharges, List.mem_map]
  rintro _ ⟨_, _, rfl⟩
  trivial

/-- The `value_return` plan burns the base/read cost and, on a valid length,
the output-data receipt byte fees. It never reserves promise gas. -/
theorem valueReturn_burnsOnly (st : HostStore NearState) (len ptr : UInt64) :
    ∀ charge ∈ chargesBefore "value_return" st [.i64 len, .i64 ptr], BurnsOnly charge := by
  simp [chargesBefore, chargesBeforeUnvalidated, storageMutationPlan?, creationAccountArgs,
    argU64, readSpan, BurnsOnly]
  split <;> simp_all
  all_goals split <;> simp_all
  all_goals aesop

/-- Gas failure precedes reading or appending the log. The charged gas/profile
and used-gas context survive; this equation specifies the whole final store. -/
theorem metered_logUtf8_charge_error (extra : Nat) (st : HostStore NearState)
    (len ptr : UInt64) (paid : NearState) (error : HostError)
    (hcharge : applyCharges st.host (chargesBefore "log_utf8" st [.i64 len, .i64 ptr]) =
      (paid, some error)) :
    (metered extra "log_utf8" logUtf8Fn).invoke st [.i64 len, .i64 ptr] =
      trapWith (paidStore st paid) error := by
  rw [metered_logUtf8_eq, hcharge]

/-- After paying the reader's charge prefix, a failed log read appends no log. -/
theorem metered_logUtf8_error (extra : Nat) (st : HostStore NearState) (len ptr : UInt64)
    (paid : NearState) (error : HostError)
    (hcharge : applyCharges st.host (chargesBefore "log_utf8" st [.i64 len, .i64 ptr]) = (paid, none))
    (hread : (logUtf8Read (paidStore st paid) len ptr).result = .error error) :
    (metered extra "log_utf8" logUtf8Fn).invoke st [.i64 len, .i64 ptr] =
      .Trap { paidStore st paid with host :=
        { (paidStore st paid).host with lastError := some error } } error.message := by
  rw [metered_logUtf8_eq, hcharge]
  exact logUtf8_error _ _ _ _ hread

theorem metered_valueReturn_charge_error (extra : Nat) (st : HostStore NearState)
    (len ptr : UInt64) (paid : NearState) (error : HostError)
    (hcharge : applyCharges st.host (chargesBefore "value_return" st [.i64 len, .i64 ptr]) =
      (paid, some error)) :
    (metered extra "value_return" valueReturnFn).invoke st [.i64 len, .i64 ptr] =
      trapWith (paidStore st paid) error := by
  rw [metered_valueReturn_eq, hcharge]

/-- Insufficient return-length capacity records the precise protocol error
after paying for the argument read, without selecting a new return value. -/
theorem metered_valueReturn_length_error (extra : Nat) (st : HostStore NearState)
    (len ptr : UInt64) (paid : NearState) (bytes : List UInt8) (limit : Nat)
    (hcharge : applyCharges st.host (chargesBefore "value_return" st [.i64 len, .i64 ptr]) = (paid, none))
    (hread : getMemOrReg (paidStore st paid) ptr len = some bytes)
    (hlimit : paid.config.maxReturnLen = some limit) (hlength : limit < bytes.length) :
    (metered extra "value_return" valueReturnFn).invoke st [.i64 len, .i64 ptr] =
      .Trap { paidStore st paid with host := { (paidStore st paid).host with
        lastError := some (.returnedValueLengthExceeded bytes.length limit) } }
        "value_return: return size exceeded" := by
  rw [metered_valueReturn_eq, hcharge]
  simp only [preInvoke_valueReturn_ok _ _ _ _ hread]
  exact valueReturn_length_error _ _ _ _ _ hread hlimit hlength

/-- An invalid span is reported by the metered wrapper with the precise
memory/register error, before selecting a return value. -/
theorem metered_valueReturn_read_error (extra : Nat) (st : HostStore NearState)
    (len ptr : UInt64) (paid : NearState)
    (hcharge : applyCharges st.host (chargesBefore "value_return" st [.i64 len, .i64 ptr]) = (paid, none))
    (hread : getMemOrReg (paidStore st paid) ptr len = none) :
    (metered extra "value_return" valueReturnFn).invoke st [.i64 len, .i64 ptr] =
      trapWith (paidStore st paid) (spanReadError len ptr) := by
  have hpre : preInvokeError "value_return" (paidStore st paid) [.i64 len, .i64 ptr] =
      some (spanReadError len ptr) := by
    change (match (if (getMemOrReg (paidStore st paid) ptr len).isNone then
      some (spanReadError len ptr) else none) with
      | some error => some error | none => none) = _
    simp only [hread, Option.isNone_none, ↓reduceIte]
  rw [metered_valueReturn_eq, hcharge]
  simp only [hpre]

/-- Reading a return span after charging reads the original memory/registers. -/
theorem paidStore_read (st : HostStore NearState) (charges : List Charge) (len ptr : UInt64)
    (hburn : ∀ charge ∈ charges, BurnsOnly charge) :
    getMemOrReg (paidStore st (applyCharges st.host charges).1) ptr len =
      getMemOrReg st ptr len := by
  have hreg := congrArg NearState.registers (applyCharges_frame st.host charges hburn)
  dsimp only at hreg
  simp only [getMemOrReg, paidStore, hreg]

/-- The return-length limit is also unchanged by charging. -/
theorem paidStore_returnLimit (st : HostStore NearState) (charges : List Charge)
    (hburn : ∀ charge ∈ charges, BurnsOnly charge) :
    (applyCharges st.host charges).1.config.maxReturnLen = st.host.config.maxReturnLen := by
  have hcfg := congrArg NearState.config (applyCharges_frame st.host charges hburn)
  exact congrArg (·.maxReturnLen) hcfg

/-- Credits for the complete actual log-read charge list suffice for the
successful host call, with exact burn and an untouched reservation frame.
The read premise concerns the explicitly paid store, not an execution result. -/
theorem metered_logUtf8_credits (extra : Nat) (st : HostStore NearState) (len ptr : UInt64)
    (rest : Nat) (msg : List UInt8)
    (hcredits : st.host.gas.Credits
      (burnSum st.host.extCosts (chargesBefore "log_utf8" st [.i64 len, .i64 ptr]) + rest))
    (hread : (logUtf8Read (paidStore st
      (applyCharges st.host (chargesBefore "log_utf8" st [.i64 len, .i64 ptr])).1) len ptr).result = .ok msg) :
    let paid := (applyCharges st.host (chargesBefore "log_utf8" st [.i64 len, .i64 ptr])).1
    (metered extra "log_utf8" logUtf8Fn).invoke st [.i64 len, .i64 ptr] =
      .Return [] { paidStore st paid with host :=
        { (paidStore st paid).host with logs := (paidStore st paid).host.logs ++ [msg] } } ∧
      paid.gas.burnt = st.host.gas.burnt +
        burnSum st.host.extCosts (chargesBefore "log_utf8" st [.i64 len, .i64 ptr]) ∧
      paid.gas.promises = st.host.gas.promises ∧ paid.gas.Credits rest := by
  have hc := applyCharges_credits st.host (chargesBefore "log_utf8" st [.i64 len, .i64 ptr]) rest
    (logUtf8_burnsOnly st len ptr) hcredits
  exact ⟨metered_logUtf8_ok extra st len ptr _ msg (Prod.ext rfl hc.1) hread,
    hc.2.1, hc.2.2.1, hc.2.2.2.2⟩

/-- The return contract includes reading bytes and output-data receipt fees;
success leaves the unused gas credits available to its caller. -/
theorem metered_valueReturn_credits (extra : Nat) (st : HostStore NearState) (len ptr : UInt64)
    (rest : Nat) (bytes : List UInt8)
    (hcredits : st.host.gas.Credits
      (burnSum st.host.extCosts (chargesBefore "value_return" st [.i64 len, .i64 ptr]) + rest))
    (hread : getMemOrReg st ptr len = some bytes)
    (hlimit : withinLimit st.host.config.maxReturnLen bytes.length = true) :
    let paid := (applyCharges st.host (chargesBefore "value_return" st [.i64 len, .i64 ptr])).1
    (metered extra "value_return" valueReturnFn).invoke st [.i64 len, .i64 ptr] =
      .Return [] { paidStore st paid with host :=
        { (paidStore st paid).host with returnData := some bytes, returnedPromise := none } } ∧
      paid.gas.burnt = st.host.gas.burnt +
        burnSum st.host.extCosts (chargesBefore "value_return" st [.i64 len, .i64 ptr]) ∧
      paid.gas.promises = st.host.gas.promises ∧ paid.gas.Credits rest := by
  have hc := applyCharges_credits st.host (chargesBefore "value_return" st [.i64 len, .i64 ptr]) rest
    (valueReturn_burnsOnly st len ptr) hcredits
  exact ⟨metered_valueReturn_ok extra st len ptr _ bytes (Prod.ext rfl hc.1)
    (by rw [paidStore_read _ _ _ _ (valueReturn_burnsOnly st len ptr)]; exact hread)
    (by rw [paidStore_returnLimit _ _ (valueReturn_burnsOnly st len ptr)]; exact hlimit),
    hc.2.1, hc.2.2.1, hc.2.2.2.2⟩

end Wasm.Near.MeteredHosts.Output
