import NearLogic.Charges

/-!
# `value_return`, metered

The host contract of `value_return(len, ptr)` with the value in memory:
when its charges fit the credits, it returns with no values, leaves memory
alone, selects the bytes as the call's return data, and uses exactly its
charges (`valueReturnCharges`).
-/

namespace NearLogic

open Wasm Wasm.Near

/-- The charges of `value_return(len, ptr)` before it runs. -/
def valueReturnCharges (st : HostStore NearState) (len ptr : UInt64) : List Charge :=
  chargesBefore "value_return" st [.i64 len, .i64 ptr]

theorem erase_selectReturnValue (h : NearState) (v : List UInt8) :
    erase (h.selectReturnValue v) = (erase h).selectReturnValue v := rfl

theorem erase_usedGas (h : NearState) (n : UInt64) :
    erase { h with context := { h.context with usedGas := n } } = erase h := rfl

theorem getMemOrReg_mem {s s' : HostStore NearState} {ptr len : UInt64} (hlen : len ≠ u64Max)
    (hm : s'.mem = s.mem) : getMemOrReg s' ptr len = getMemOrReg s ptr len := by
  simp [getMemOrReg, hlen, hm]

theorem preInvokeError_valueReturn (s : HostStore NearState) (len ptr : UInt64)
    (h : (getMemOrReg s ptr len).isSome = true) :
    preInvokeError "value_return" s [.i64 len, .i64 ptr] = none := by
  have hs : storageMutationPlan? "value_return" s [.i64 len, .i64 ptr] = none := by
    simp [storageMutationPlan?]
  have hg : globalContractInputs? "value_return" = none := by decide
  have hne : getMemOrReg s ptr len ≠ none := by
    intro e; rw [e] at h; exact Bool.false_ne_true h
  simp only [preInvokeError, invocationArgumentError, hs, hg, argU64]
  simp [hne, allocatesPromise, functionCallInputError, functionCallInputs?]

/-- After the charges, `value_return` itself and its post-call metering. -/
theorem valueReturn_after (extra : Nat) (s : HostStore NearState) (len ptr : UInt64) (v : List UInt8)
    (hv : getMemOrReg s ptr len = some v) (hlim : withinLimit s.host.config.maxReturnLen v.length = true) :
    invokeStorageCall extra "value_return" valueReturnFn s [.i64 len, .i64 ptr] =
      .Return [] { s with host := s.host.selectReturnValue v } := by
  have hother : ["storage_read", "storage_has_key", "storage_write", "storage_remove"].contains
      "value_return" = false := by decide
  simp only [invokeStorageCall, prepareStorageCall_other _ _ _ hother]
  simp only [valueReturnFn, hv, checkDataLimit, hlim, ite_true, finishMeteredCall]
  have hc : ¬ "value_return" ∈ cryptoHostNames := by decide
  simp [chargesAfter, hc, applyCharges, deductDeposit, promiseDeposit?, actionMethodEncodingError,
    actionMethodBytes?, usesKeyMethodFields, functionCallInputs?, updateStorageUsage]

theorem valueReturn_ok (extra : Nat) (st : HostStore NearState) (len ptr : UInt64) {C : Nat}
    (hlen : len ≠ u64Max) (hin : ptr.toNat + len.toNat ≤ st.mem.size * 65536)
    (hlim : withinLimit st.host.config.maxReturnLen len.toNat = true)
    (h1 : st.host.gas.used + chargesUse st.host (valueReturnCharges st len ptr) ≤ C)
    (h2 : C ≤ st.host.gas.maxBurnt) (h3 : C ≤ st.host.gas.prepaid) :
    ∃ host', (metered extra "value_return" valueReturnFn).invoke st [.i64 len, .i64 ptr] =
        .Return [] { mem := st.mem, host := host' } ∧
      erase host' = (erase st.host).selectReturnValue (st.mem.readList ptr.toNat len.toNat) ∧
      host'.gas.used = st.host.gas.used + chargesUse st.host (valueReturnCharges st len ptr) ∧
      host'.gas.maxBurnt = st.host.gas.maxBurnt ∧ host'.gas.prepaid = st.host.gas.prepaid := by
  obtain ⟨hok, hch⟩ := applyCharges_ok st.host (valueReturnCharges st len ptr) h1 h2 h3
  have hget : getMemOrReg st ptr len = some (st.mem.readList ptr.toNat len.toNat) := by
    simp only [getMemOrReg, hlen, ite_false]
    rw [if_neg (by omega)]
  have hdep : deprecatedRuntimeHost "value_return" = false := by decide
  have hview : viewRestrictedHost "value_return" = false := by decide
  simp only [metered, hdep, hview, Bool.and_false, Bool.false_eq_true, ite_false]
  rw [show chargesBefore "value_return" st [.i64 len, .i64 ptr] = valueReturnCharges st len ptr from rfl]
  generalize hac : applyCharges st.host (valueReturnCharges st len ptr) = ac at hok hch
  obtain ⟨ns, err⟩ := ac
  simp only at hok hch
  subst hok
  simp only
  set st1 : HostStore NearState := { mem := st.mem, host := { ns with context := { ns.context with
    usedGas := UInt64.ofNat ns.gas.used } } } with hst1
  have hget1 : getMemOrReg st1 ptr len = some (st.mem.readList ptr.toNat len.toNat) := by
    rw [getMemOrReg_mem (s := st) (s' := st1) hlen rfl, hget]
  rw [preInvokeError_valueReturn st1 len ptr (by rw [hget1]; rfl)]
  simp only
  rw [valueReturn_after extra st1 len ptr _ hget1 (by
    simp only [st1, Memory.readList_length, hch.config]; exact hlim)]
  refine ⟨_, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [st1, erase_selectReturnValue, erase_usedGas, hch.erase]
  · exact hch.used
  · exact hch.maxBurnt
  · exact hch.prepaid

end NearLogic
