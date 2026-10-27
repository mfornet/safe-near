import NearLogic.Hosts.ValueReturn
import NearLogic.Relax

/-!
# `value_return` under raised gas limits

With the value in memory and within the return limit, metered
`value_return` either fails a charge (a gas error) or, run on the host with
raised limits, gives the same result with those limits.
-/

namespace NearLogic

open Wasm Wasm.Near

/-- A host result with its host's limits raised. -/
def _root_.Wasm.HostResult.relax (p m : Nat) : HostResult NearState → HostResult NearState
  | .Return vals st => .Return vals (relaxSt st p m)
  | .Trap st msg => .Trap (relaxSt st p m) msg

set_option maxRecDepth 100000 in
theorem chargesBefore_valueReturn_relax (st : HostStore NearState) (args : List Value) (p m : Nat) :
    chargesBefore "value_return" (relaxSt st p m) args = chargesBefore "value_return" st args := by
  simp only [relaxSt, relax, chargesBefore, chargesBeforeUnvalidated, storageMutationPlan?, creationAccountArgs]
  rfl

/-- `value_return`'s argument check: the value must be readable. -/
theorem preInvokeError_valueReturn_eq (s : HostStore NearState) (args : List Value) :
    preInvokeError "value_return" s args =
      if (getMemOrReg s (argU64 args 1) (argU64 args 0)).isNone then
        some (spanReadError (argU64 args 0) (argU64 args 1)) else none := by
  have hs : storageMutationPlan? "value_return" s args = none := by simp [storageMutationPlan?]
  have hg : globalContractInputs? "value_return" = none := by decide
  simp only [preInvokeError, invocationArgumentError, hs, hg]
  simp (config := { decide := true }) only [ite_false, ite_true, allocatesPromise, functionCallInputError,
    functionCallInputs?]
  split <;> rename_i h <;> first | exact h.symm | (rw [h]; rfl)

theorem preInvokeError_valueReturn_relax (st : HostStore NearState) (args : List Value) (p m : Nat) :
    preInvokeError "value_return" (relaxSt st p m) args = preInvokeError "value_return" st args := by
  rw [preInvokeError_valueReturn_eq, preInvokeError_valueReturn_eq]
  rfl

theorem getMemOrReg_relaxSt (st : HostStore NearState) (p m : Nat) (ptr len : UInt64) :
    getMemOrReg (relaxSt st p m) ptr len = getMemOrReg st ptr len := rfl

theorem config_relaxSt (st : HostStore NearState) (p m : Nat) :
    (relaxSt st p m).host.config = st.host.config := rfl

/-- The functional `value_return` commutes with raising the limits. -/
theorem valueReturnFn_relax (st : HostStore NearState) (args : List Value) (p m : Nat) :
    valueReturnFn.invoke (relaxSt st p m) args = (valueReturnFn.invoke st args).relax p m := by
  unfold valueReturnFn
  dsimp only
  split
  · rw [getMemOrReg_relaxSt]
    split
    · rfl
    · unfold checkDataLimit
      rw [config_relaxSt]
      split
      · rfl
      · rfl
  · rfl

/-- `value_return`'s post-call metering changes nothing. -/
theorem finishMeteredCall_valueReturn (extra : Nat) (before : HostStore NearState) (args : List Value)
    (r : HostResult NearState) : finishMeteredCall extra "value_return" before args r = r := by
  cases r with
  | Trap st msg => rfl
  | Return vals st =>
    have hc : ¬ "value_return" ∈ cryptoHostNames := by decide
    simp [finishMeteredCall, chargesAfter, hc, applyCharges, deductDeposit, promiseDeposit?,
      actionMethodEncodingError, actionMethodBytes?, usesKeyMethodFields, functionCallInputs?,
      updateStorageUsage]

theorem valueReturn_relax (extra : Nat) (st : HostStore NearState) (len ptr : UInt64) (p m : Nat)
    (hlen : len ≠ u64Max) (hin : ptr.toNat + len.toNat ≤ st.mem.size * 65536)
    (hlim : withinLimit st.host.config.maxReturnLen len.toNat = true)
    (hp : st.host.gas.prepaid ≤ p) (hm : st.host.gas.maxBurnt ≤ m) :
    (∃ st' e, (metered extra "value_return" valueReturnFn).invoke st [.i64 len, .i64 ptr] =
        trapWith st' e ∧ isGasError e) ∨
      (metered extra "value_return" valueReturnFn).invoke (relaxSt st p m) [.i64 len, .i64 ptr] =
        ((metered extra "value_return" valueReturnFn).invoke st [.i64 len, .i64 ptr]).relax p m := by
  have hcs := valueReturnCharges_eq st len ptr hlen hin hlim
  have hcs' : valueReturnCharges (relaxSt st p m) len ptr = valueReturnChargeList st.host len.toNat :=
    valueReturnCharges_eq (relaxSt st p m) len ptr hlen hin hlim
  have hdep : deprecatedRuntimeHost "value_return" = false := by decide
  have hview : viewRestrictedHost "value_return" = false := by decide
  have hget : getMemOrReg st ptr len = some (st.mem.readList ptr.toNat len.toNat) := by
    simp only [getMemOrReg, hlen, ite_false]
    rw [if_neg (by omega)]
  simp only [metered, hdep, hview, Bool.and_false, Bool.false_eq_true, ite_false]
  rw [show chargesBefore "value_return" st [.i64 len, .i64 ptr] = valueReturnCharges st len ptr from rfl,
    show chargesBefore "value_return" (relaxSt st p m) [.i64 len, .i64 ptr] =
      valueReturnCharges (relaxSt st p m) len ptr from rfl, hcs, hcs']
  cases hac : applyCharges st.host (valueReturnChargeList st.host len.toNat) with
  | mk ns err =>
    cases err with
    | some e =>
      left
      exact ⟨_, e, rfl, applyCharges_error _ _ (by rw [hac])⟩
    | none =>
      right
      have hrel := applyCharges_relax st.host (valueReturnChargeList st.host len.toNat) p m hp hm (by rw [hac])
      rw [hac] at hrel
      simp only [relaxSt] at hrel ⊢
      rw [hrel]
      simp only
      have hcfg : ns.config = st.host.config := by
        have := applyCharges_gas_config st.host (valueReturnChargeList st.host len.toNat)
        rw [hac] at this
        exact this
      have hv : withinLimit ns.config.maxReturnLen (st.mem.readList ptr.toNat len.toNat).length = true := by
        rw [Memory.readList_length, hcfg]; exact hlim
      have hgm : ∀ s' : HostStore NearState, s'.mem = st.mem →
          getMemOrReg s' ptr len = some (st.mem.readList ptr.toNat len.toNat) := fun s' h => by
        rw [getMemOrReg_mem (s := st) (s' := s') hlen h, hget]
      have hpre : ∀ s' : HostStore NearState, s'.mem = st.mem →
          preInvokeError "value_return" s' [.i64 len, .i64 ptr] = none := fun s' h =>
        preInvokeError_valueReturn s' len ptr (by rw [hgm s' h]; rfl)
      rw [hpre, hpre]
      rotate_left
      · rfl
      · rfl
      simp only
      have haft : ∀ s' : HostStore NearState, s'.mem = st.mem → s'.host.config = ns.config →
          invokeStorageCall extra "value_return" valueReturnFn s' [.i64 len, .i64 ptr] =
            .Return [] { s' with host := s'.host.selectReturnValue (st.mem.readList ptr.toNat len.toNat) } :=
        fun s' h hc => valueReturn_after extra s' len ptr _ (hgm s' h) (by rw [hc]; exact hv)
      rw [haft, haft]
      all_goals rfl

/-- Metered `value_return` with any arguments, under raised limits: it fails a
charge (a gas error), or it gives the same result with those limits. -/
theorem meteredValueReturn_relax (extra : Nat) (st : HostStore NearState) (args : List Value) (p m : Nat)
    (hp : st.host.gas.prepaid ≤ p) (hm : st.host.gas.maxBurnt ≤ m) :
    (∃ st' e, (metered extra "value_return" valueReturnFn).invoke st args = trapWith st' e ∧ isGasError e) ∨
      (metered extra "value_return" valueReturnFn).invoke (relaxSt st p m) args =
        ((metered extra "value_return" valueReturnFn).invoke st args).relax p m := by
  have hdep : deprecatedRuntimeHost "value_return" = false := by decide
  have hview : viewRestrictedHost "value_return" = false := by decide
  have hother : ["storage_read", "storage_has_key", "storage_write", "storage_remove"].contains
      "value_return" = false := by decide
  simp only [metered, hdep, hview, Bool.and_false, Bool.false_eq_true, ite_false]
  rw [chargesBefore_valueReturn_relax]
  cases hac : applyCharges st.host (chargesBefore "value_return" st args) with
  | mk ns err =>
    cases err with
    | some e =>
      left
      exact ⟨_, e, rfl, applyCharges_error _ _ (by rw [hac])⟩
    | none =>
      right
      have hrel := applyCharges_relax st.host (chargesBefore "value_return" st args) p m hp hm (by rw [hac])
      rw [hac] at hrel
      rw [show (relaxSt st p m).host = relax st.host p m from rfl, hrel]
      simp only
      have hrest : ∀ s : HostStore NearState,
          (match preInvokeError "value_return" (relaxSt s p m) args with
            | some error => trapWith (relaxSt s p m) error
            | none => invokeStorageCall extra "value_return" valueReturnFn (relaxSt s p m) args) =
          (match preInvokeError "value_return" s args with
            | some error => trapWith s error
            | none => invokeStorageCall extra "value_return" valueReturnFn s args).relax p m := by
        intro s
        rw [preInvokeError_valueReturn_relax]
        split
        · rfl
        · simp only [invokeStorageCall, prepareStorageCall_other _ _ _ hother, finishMeteredCall_valueReturn]
          exact valueReturnFn_relax _ args p m
      exact hrest { mem := st.mem, host := { ns with context := { ns.context with
        usedGas := UInt64.ofNat ns.gas.used } } }

end NearLogic
