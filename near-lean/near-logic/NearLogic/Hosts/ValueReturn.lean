import NearLogic.Charges
import NearLogic.Call

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

/-- The data receipt bytes `value_return` burns for `n` bytes. -/
def valueReturnDataGas (h : NearState) (n : Nat) : Nat :=
  (h.outputDataReceivers.map fun r =>
    let sir := r == h.context.currentAccountId
    h.fees.newDataReceiptByte.send sir * n + h.fees.newDataReceiptByte.execution * n).sum

/-- The charges of `value_return` of `n` bytes in memory, within the return limit. -/
def valueReturnChargeList (h : NearState) (n : Nat) : List Charge :=
  [.ext "base", .ext "read_memory_base", .ext "read_memory_byte" n, .burn (valueReturnDataGas h n)]

/-- The gas `value_return` of `n` bytes uses. -/
def valueReturnUse (h : NearState) (n : Nat) : Nat := chargesUse h (valueReturnChargeList h n)

theorem valueReturnCharges_eq (st : HostStore NearState) (len ptr : UInt64) (hlen : len ≠ u64Max)
    (hin : ptr.toNat + len.toNat ≤ st.mem.size * 65536)
    (hlim : withinLimit st.host.config.maxReturnLen len.toNat = true) :
    valueReturnCharges st len ptr = valueReturnChargeList st.host len.toNat := by
  have hs : storageMutationPlan? "value_return" st [.i64 len, .i64 ptr] = none := by
    simp [storageMutationPlan?]
  have hget : getMemOrReg st ptr len = some (st.mem.readList ptr.toNat len.toNat) := by
    simp only [getMemOrReg, hlen, ite_false]
    rw [if_neg (by omega)]
  have hpre : "value_return".startsWith "promise_batch_action_" = false := by decide
  simp only [valueReturnCharges, chargesBefore, hs, creationAccountArgs, argU64, hpre]
  simp [chargesBeforeUnvalidated, argU64, spanLen, hlen, readSpan, hget, Memory.readList_length, hlim,
    valueReturnChargeList, valueReturnDataGas]

/-- A field that erasure keeps is equal on hosts equal up to gas. -/
theorem erase_field {α : Type} {h h' : NearState} (he : erase h = erase h') (f : NearState → α)
    (hf : ∀ x, f (erase x) = f x) : f h = f h' := by
  rw [← hf h, ← hf h', he]

/-- The fee tables and the fields charges read survive erasure. -/
theorem chargesUse_erase {h h' : NearState} (he : erase h = erase h') (cs : List Charge) :
    chargesUse h cs = chargesUse h' cs := by
  have hf : h.fees = h'.fees := erase_field he NearState.fees fun _ => rfl
  have hx : h.extCosts = h'.extCosts := erase_field he NearState.extCosts fun _ => rfl
  unfold chargesUse
  congr 1
  exact List.map_congr_left fun c _ => chargeUse_congr (ns' := h) (ns := h') hf hx c

theorem valueReturnUse_erase {h h' : NearState} (he : erase h = erase h') (n : Nat) :
    valueReturnUse h n = valueReturnUse h' n := by
  have hr : h.outputDataReceivers = h'.outputDataReceivers :=
    erase_field he NearState.outputDataReceivers fun _ => rfl
  have hc : h.context.currentAccountId = h'.context.currentAccountId :=
    erase_field he (fun x : NearState => x.context.currentAccountId) fun _ => rfl
  have hf : h.fees = h'.fees := erase_field he NearState.fees fun _ => rfl
  have hd : valueReturnDataGas h n = valueReturnDataGas h' n := by
    simp [valueReturnDataGas, hr, hc, hf]
  unfold valueReturnUse valueReturnChargeList
  rw [hd]
  exact chargesUse_erase he _

theorem readList_eq_map (m : Memory) (addr len : Nat) :
    m.readList addr len = (List.range len).map fun i => m.read8 (addr + i) := by
  unfold Memory.readList; rfl

theorem readList_eq {m : Memory} {addr : Nat} {bs : List UInt8}
    (h : ∀ k, k < bs.length → m.read8 (addr + k) = bs[k]!) : m.readList addr bs.length = bs := by
  rw [readList_eq_map]
  apply List.ext_getElem?
  intro k
  by_cases hk : k < bs.length
  · simp [hk, h k hk]
  · simp [hk, List.getElem?_eq_none (Nat.le_of_not_lt hk)]

/-- `value_return` of the `len` bytes `bs` at `ptr`, as a read contract. -/
theorem valueReturn_readContract (extra : Nat) (h : NearState) (len ptr : UInt64) (bs : List UInt8)
    {C : Nat} (hlen : len ≠ u64Max) (hbs : bs.length = len.toNat)
    (hlim : withinLimit h.config.maxReturnLen len.toNat = true) (hpos : 0 < len.toNat) :
    ReadContract (metered extra "value_return" valueReturnFn).toHostFn h (h.selectReturnValue bs)
      [.i64 len, .i64 ptr] [] ptr.toNat bs (valueReturnUse h len.toNat) C := by
  intro host mem hwf he hrd hu hmb hpp
  have hin : ptr.toNat + len.toNat ≤ mem.size * 65536 := by
    have := (hrd (len.toNat - 1) (by omega)).1
    unfold Memory.byteSize at this
    show _ ≤ mem.pages.size * 65536
    unfold pageSize at this
    omega
  have hlim' : withinLimit host.config.maxReturnLen len.toNat = true := by
    rw [show host.config = h.config from erase_field he NearState.config fun _ => rfl]; exact hlim
  have hcs := valueReturnCharges_eq { mem, host } len ptr hlen hin hlim'
  obtain ⟨host', hinv, her, hused, hmb', hpp'⟩ := valueReturn_ok extra { mem, host } len ptr hlen hin hlim'
    (C := C) (by rw [hcs]; rw [← valueReturnUse_erase he] at hu; exact hu) hmb hpp
  have hread : mem.readList ptr.toNat len.toNat = bs := by
    rw [← hbs]; exact readList_eq fun k hk => (hrd k hk).2
  refine ⟨host', ?_, ?_, ?_, hmb', hpp'⟩
  · simp only [NearHostFn.toHostFn, Option.getD_some, hinv]
  · rw [her, hread, erase_selectReturnValue, he]
  · rw [hused, hcs, show chargesUse host (valueReturnChargeList host len.toNat) = valueReturnUse host len.toNat
      from rfl, valueReturnUse_erase he]
    exact Nat.le_refl _

end NearLogic
