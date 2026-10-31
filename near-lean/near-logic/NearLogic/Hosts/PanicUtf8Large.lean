import NearLogic.Hosts.PanicUtf8

namespace NearLogic.PanicUtf8Large
open Wasm Wasm.Near
open private baseCharge u64Cap from NearVM.LogRead

/-- Oversized explicit-length panic messages fail before memory reads or UTF-8 decoding. -/
theorem panicUtf8Read_large (st : HostStore NearState) (len ptr : UInt64) (limit : Nat)
    (hlen : len ≠ u64Max) (hlimit : st.host.config.maxLogLen = some limit)
    (hlarge : limit - (st.host.logs.map List.length).sum < len.toNat) :
    panicUtf8Read st len ptr =
      ⟨[ext1 "base", ext1 "utf8_decoding_base"], .error (totalLogLengthExceeded st len.toNat)⟩ := by
  have hl : logSpace st < len.toNat := by simpa [logSpace, totalLogLength, hlimit] using hlarge
  simp [panicUtf8Read, readUtf8String, hlen, hl, baseCharge]

/-- Only these two base charges precede the controlled oversized-message failure. -/
def largeCharges : List Charge := [.ext "base", .ext "utf8_decoding_base"]
def largeUse (h : NearState) : Nat := chargesUse h largeCharges

theorem chargesBefore_large (st : HostStore NearState) (len ptr : UInt64) (limit : Nat)
    (hlen : len ≠ u64Max) (hlimit : st.host.config.maxLogLen = some limit)
    (hlarge : limit - (st.host.logs.map List.length).sum < len.toNat) :
    chargesBefore "panic_utf8" st [.i64 len, .i64 ptr] = largeCharges := by
  have hs : storageMutationPlan? "panic_utf8" st [.i64 len, .i64 ptr] = none := by simp [storageMutationPlan?]
  have hp : "panic_utf8".startsWith "promise_batch_action_" = false := by decide
  simp [chargesBefore, hs, creationAccountArgs, argU64, hp, chargesBeforeUnvalidated, stringHostRead?,
    panicUtf8Read_large st len ptr limit hlen hlimit hlarge, extCharges, ext1, largeCharges]

theorem panicUtf8_large (extra : Nat) (st : HostStore NearState) (len ptr : UInt64) (limit : Nat) {C : Nat}
    (hlen : len ≠ u64Max) (hlimit : st.host.config.maxLogLen = some limit)
    (hlarge : limit - (st.host.logs.map List.length).sum < len.toNat)
    (h1 : st.host.gas.used + largeUse st.host ≤ C)
    (h2 : C ≤ st.host.gas.maxBurnt) (h3 : C ≤ st.host.gas.prepaid) :
    ∃ host', (metered extra "panic_utf8" panicUtf8Metered).invoke st [.i64 len, .i64 ptr] =
        .Trap { mem := st.mem, host := host' } (totalLogLengthExceeded st len.toNat).message ∧
      erase host' = erase { st.host with lastError := some (totalLogLengthExceeded st len.toNat) } ∧
      host'.gas.used = st.host.gas.used + largeUse st.host ∧
      host'.gas.maxBurnt = st.host.gas.maxBurnt ∧ host'.gas.prepaid = st.host.gas.prepaid := by
  have hd : deprecatedRuntimeHost "panic_utf8" = false := by decide
  have hv : viewRestrictedHost "panic_utf8" = false := by decide
  have ho : ["storage_read", "storage_has_key", "storage_write", "storage_remove"].contains "panic_utf8" = false := by decide
  obtain ⟨hok, hch⟩ := applyCharges_ok st.host largeCharges h1 h2 h3
  simp only [metered, hd, hv, Bool.and_false, Bool.false_eq_true, ite_false]
  rw [chargesBefore_large st len ptr limit hlen hlimit hlarge]
  generalize hac : applyCharges st.host largeCharges = ac at hok hch
  obtain ⟨ns, err⟩ := ac
  simp only at hok hch
  subst hok
  simp only
  rw [preInvokeError_panicUtf8]
  simp only
  show ∃ host', invokeStorageCall extra "panic_utf8" panicUtf8Metered
    { mem := st.mem, host := afterCharges ns } [.i64 len, .i64 ptr] = _ ∧ _
  have he : erase (afterCharges ns) = erase st.host := by rw [erase_afterCharges, hch.erase]
  have hc : (afterCharges ns).config = st.host.config := erase_field he NearState.config fun _ => rfl
  have hl : (afterCharges ns).logs = st.host.logs := erase_field he NearState.logs fun _ => rfl
  have hr := panicUtf8Read_large { mem := st.mem, host := afterCharges ns } len ptr limit hlen
    (by rw [hc]; exact hlimit) (by rw [hl]; exact hlarge)
  have herr : totalLogLengthExceeded { mem := st.mem, host := afterCharges ns } len.toNat =
      totalLogLengthExceeded st len.toNat := by simp only [totalLogLengthExceeded, totalLogLength, hc, hl]
  rw [herr] at hr
  simp only [invokeStorageCall, prepareStorageCall_other _ _ _ ho, panicUtf8Metered, hr, finishMeteredCall, trapWith]
  refine ⟨_, rfl, ?_, hch.used, hch.maxBurnt, hch.prepaid⟩
  exact congrArg (fun x : NearState => { x with lastError := some (totalLogLengthExceeded st len.toNat) }) he

/-- The protocol failure reported without inspecting an oversized message. -/
def largeError (h : NearState) (n limit : Nat) : HostError :=
  .totalLogLengthExceeded (min ((h.logs.map List.length).sum + n) (2 ^ 64 - 1)) limit

theorem panicUtf8_large_contract (extra : Nat) (h : NearState) (len ptr : UInt64) (limit : Nat)
    {C : Nat} (hlen : len ≠ u64Max) (hlimit : h.config.maxLogLen = some limit)
    (hlarge : limit - (h.logs.map List.length).sum < len.toNat) :
    TrapContractP (metered extra "panic_utf8" panicUtf8Metered).toHostFn h
      (fun h' => erase h' = erase { h with lastError := some (largeError h len.toNat limit) })
      [.i64 len, .i64 ptr] (.host (largeError h len.toNat limit).message) ptr.toNat [] (largeUse h) C := by
  intro host mem hwf he hrd hu hmb hpp
  have hc : host.config = h.config := erase_field he NearState.config fun _ => rfl
  have hl : host.logs = h.logs := erase_field he NearState.logs fun _ => rfl
  have huse : largeUse host = largeUse h := chargesUse_erase he _
  have herr : totalLogLengthExceeded { mem, host } len.toNat = largeError h len.toNat limit := by
    simp only [totalLogLengthExceeded, totalLogLength, hc, hl, hlimit, Option.getD_some, largeError, u64Cap]
  obtain ⟨host', hinv, her, hused, hmb', hpp'⟩ := panicUtf8_large extra { mem, host } len ptr limit (C := C)
    hlen (by rw [hc]; exact hlimit) (by rw [hl]; exact hlarge)
    (by simpa only [huse] using hu) hmb hpp
  rw [herr] at hinv her
  refine ⟨host', ?_, ?_, ?_, hmb', hpp'⟩
  · simp only [NearHostFn.toHostFn, Option.getD_some, hinv]
  · show erase host' = _
    rw [her]
    exact congrArg (fun x : NearState => { x with lastError := some (largeError h len.toNat limit) }) he
  · simpa only [huse] using Nat.le_of_eq hused
/-- The oversize result is a concrete protocol failure, not an interpreter/model issue. -/
theorem largeError_no_issue (h : NearState) (n limit : Nat) :
    FunctionCallError.issue? (.hostError (largeError h n limit)) = none := rfl

theorem largeError_not_out_of_gas (h : NearState) (n limit : Nat) :
    FunctionCallError.isOutOfGas (.hostError (largeError h n limit)) = false := rfl

/-- Nonempty messages either fit or follow the explicit controlled oversize branch. -/
theorem log_length_cases (h : NearState) (n : Nat) (hn : 0 < n) :
    LogFits h n ∨ ∃ limit : Nat, h.config.maxLogLen = some limit ∧
      limit - (h.logs.map List.length).sum < n := by
  cases hc : h.config.maxLogLen with
  | none =>
    left
    intro limit hl
    rw [hc] at hl
    contradiction
  | some limit =>
    by_cases hfit : (h.logs.map List.length).sum + n ≤ limit
    · left
      intro lim hl
      rw [hc] at hl
      have : limit = lim := Option.some.inj hl
      simpa [← this] using hfit
    · right
      exact ⟨limit, rfl, by omega⟩
end NearLogic.PanicUtf8Large
