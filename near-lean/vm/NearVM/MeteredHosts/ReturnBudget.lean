import NearVM.MeteredHosts.Budget
import NearVM.MeteredHosts.Output

/-!
# Budget replay for actual `value_return`

Both memory spans and the register sentinel are covered. Charge plans and
validation depend only on functional state, while billing updates the separate
internal counter and synchronizes the guest-visible used-gas field.
-/
namespace Wasm.Near.MeteredHosts.ReturnBudget
open Budget

/-- Register and memory reads agree across internal budget changes. -/
theorem read_eq {small large : HostStore NearState} (h : StoreBelow small large)
    (len ptr : UInt64) : getMemOrReg small ptr len = getMemOrReg large ptr len := by
  have hreg := congrArg NearState.registers h.host.fields
  simp only [functional] at hreg
  simp only [getMemOrReg, h.mem, hreg]

/-- The exact return plan includes output-data receiver byte fees; it is still
independent of the internal budget limits and diagnostic profiles. -/
theorem plan_eq {small large : HostStore NearState} (h : StoreBelow small large)
    (len ptr : UInt64) :
    chargesBefore "value_return" small [.i64 len, .i64 ptr] =
      chargesBefore "value_return" large [.i64 len, .i64 ptr] := by
  have hreg := congrArg NearState.registers h.host.fields
  have hfees := congrArg NearState.fees h.host.fields
  have hreceivers := congrArg NearState.outputDataReceivers h.host.fields
  simp only [functional] at hreg hfees hreceivers
  simp [chargesBefore, chargesBeforeUnvalidated, storageMutationPlan?, creationAccountArgs,
    argU64, spanLen, readSpan, read_eq h len ptr, hreg, hfees, hreceivers,
    h.host.context, h.host.config]

private theorem selected_below {small large : NearState} (h : HostBelow small large)
    (bytes : List UInt8) : HostBelow (small.selectReturnValue bytes) (large.selectReturnValue bytes) := by
  have hf := congrArg (fun ns : NearState => ns.selectReturnValue bytes) h.fields
  exact ⟨by simpa only [functional, NearState.selectReturnValue] using hf, h.gas⟩

private theorem error_below {small large : NearState} (h : HostBelow small large)
    (error : HostError) :
    HostBelow { small with lastError := some error } { large with lastError := some error } := by
  have hf := congrArg (fun ns : NearState => { ns with lastError := some error }) h.fields
  exact ⟨by simpa only [functional] using hf, h.gas⟩

/-- Functional success, raw read failure, and return-length failure all replay. -/
theorem raw_below {small large : HostStore NearState} (h : StoreBelow small large)
    (len ptr : UInt64) :
    ResultBelow (valueReturnFn.invoke small [.i64 len, .i64 ptr])
      (valueReturnFn.invoke large [.i64 len, .i64 ptr]) := by
  cases hr : getMemOrReg small ptr len with
  | none =>
    have hl : getMemOrReg large ptr len = none := (read_eq h len ptr).symm.trans hr
    rw [Output.valueReturn_read_error small len ptr hr, Output.valueReturn_read_error large len ptr hl]
    exact .trapped _ h
  | some bytes =>
    have hl : getMemOrReg large ptr len = some bytes := (read_eq h len ptr).symm.trans hr
    cases hlimit : small.host.config.maxReturnLen with
    | none =>
      have hlarge : large.host.config.maxReturnLen = none := by
        simpa only [← h.host.config] using hlimit
      rw [Output.valueReturn_ok small len ptr bytes hr (by simp [withinLimit, hlimit]),
        Output.valueReturn_ok large len ptr bytes hl (by simp [withinLimit, hlarge])]
      exact .returned [] ⟨h.mem, selected_below h.host bytes⟩
    | some limit =>
      have hlarge : large.host.config.maxReturnLen = some limit := by
        simpa only [← h.host.config] using hlimit
      by_cases hlength : bytes.length ≤ limit
      · rw [Output.valueReturn_ok small len ptr bytes hr (by simp [withinLimit, hlimit, hlength]),
          Output.valueReturn_ok large len ptr bytes hl (by simp [withinLimit, hlarge, hlength])]
        exact .returned [] ⟨h.mem, selected_below h.host bytes⟩
      · rw [Output.valueReturn_length_error small len ptr bytes limit hr hlimit (by omega),
          Output.valueReturn_length_error large len ptr bytes limit hl hlarge (by omega)]
        exact .trapped _ ⟨h.mem, error_below h.host _⟩

/-- Include the wrapper's precise memory/register read validation, before the
functional return selector is invoked. -/
def validated (st : HostStore NearState) (len ptr : UInt64) : HostResult NearState :=
  match preInvokeError "value_return" st [.i64 len, .i64 ptr] with
  | some error => trapWith st error
  | none => valueReturnFn.invoke st [.i64 len, .i64 ptr]

private theorem pre_eq {small large : HostStore NearState} (h : StoreBelow small large)
    (len ptr : UInt64) :
    preInvokeError "value_return" small [.i64 len, .i64 ptr] =
      preInvokeError "value_return" large [.i64 len, .i64 ptr] := by
  change (match (if (getMemOrReg small ptr len).isNone then some (spanReadError len ptr) else none) with
      | some error => some error | none => none) =
    (match (if (getMemOrReg large ptr len).isNone then some (spanReadError len ptr) else none) with
      | some error => some error | none => none)
  rw [read_eq h len ptr]

theorem validated_below {small large : HostStore NearState} (h : StoreBelow small large)
    (len ptr : UInt64) : ResultBelow (validated small len ptr) (validated large len ptr) := by
  unfold validated
  rw [pre_eq h len ptr]
  cases he : preInvokeError "value_return" large [.i64 len, .i64 ptr] with
  | none => exact raw_below h len ptr
  | some error => exact .trapped _ ⟨h.mem, error_below h.host error⟩

private theorem metered_charged (st : HostStore NearState) (extra : Nat) (len ptr : UInt64)
    (hok : (applyCharges st.host (chargesBefore "value_return" st [.i64 len, .i64 ptr])).2 = none) :
    (metered extra "value_return" valueReturnFn).invoke st [.i64 len, .i64 ptr] =
      validated (Output.paidStore st
        (applyCharges st.host (chargesBefore "value_return" st [.i64 len, .i64 ptr])).1) len ptr := by
  rw [Output.metered_valueReturn_eq]
  cases hc : applyCharges st.host (chargesBefore "value_return" st [.i64 len, .i64 ptr]) with
  | mk paid error =>
    cases error with
    | none => rfl
    | some error => simp only [hc] at hok; contradiction

/-- Successful low-budget charging replays the actual complete wrapper:
normal returns, raw size failures, and pre-invocation span failures all match. -/
theorem metered_below {small large : HostStore NearState} (h : StoreBelow small large)
    (extra : Nat) (len ptr : UInt64)
    (hok : (applyCharges small.host (chargesBefore "value_return" small [.i64 len, .i64 ptr])).2 = none) :
    ResultBelow ((metered extra "value_return" valueReturnFn).invoke small [.i64 len, .i64 ptr])
      ((metered extra "value_return" valueReturnFn).invoke large [.i64 len, .i64 ptr]) := by
  have hc := applyCharges_below h.host (chargesBefore "value_return" small [.i64 len, .i64 ptr])
    (Output.valueReturn_burnsOnly small len ptr) hok
  have hhigh : (applyCharges large.host (chargesBefore "value_return" large [.i64 len, .i64 ptr])).2 = none := by
    rw [← plan_eq h len ptr]
    exact hc.1
  have hp : StoreBelow
      (Output.paidStore small (applyCharges small.host
        (chargesBefore "value_return" small [.i64 len, .i64 ptr])).1)
      (Output.paidStore large (applyCharges large.host
        (chargesBefore "value_return" large [.i64 len, .i64 ptr])).1) := by
    rw [← plan_eq h len ptr]
    exact ⟨h.mem, hc.2.syncUsed⟩
  rw [metered_charged small extra len ptr hok, metered_charged large extra len ptr hhigh]
  exact validated_below hp len ptr

private theorem raw_frame (store : HostStore NearState) (len ptr : UInt64) :
    (resultStore (valueReturnFn.invoke store [.i64 len, .i64 ptr])).mem = store.mem ∧
    (resultStore (valueReturnFn.invoke store [.i64 len, .i64 ptr])).host.logs = store.host.logs := by
  dsimp only [valueReturnFn, checkDataLimit]
  repeat' (first | exact ⟨rfl, rfl⟩ | split)

private theorem validated_frame (store : HostStore NearState) (len ptr : UInt64) :
    (resultStore (validated store len ptr)).mem = store.mem ∧
    (resultStore (validated store len ptr)).host.logs = store.host.logs := by
  unfold validated
  cases preInvokeError "value_return" store [.i64 len, .i64 ptr] with
  | none => exact raw_frame store len ptr
  | some error => exact ⟨rfl, rfl⟩

private theorem paid_logs (store : HostStore NearState) (len ptr : UInt64) :
    (Output.paidStore store (applyCharges store.host
      (chargesBefore "value_return" store [.i64 len, .i64 ptr])).1).host.logs = store.host.logs := by
  have hf := congrArg NearState.logs (applyCharges_frame store.host
    (chargesBefore "value_return" store [.i64 len, .i64 ptr]) (Output.valueReturn_burnsOnly store len ptr))
  exact hf

/-- Every actual return-host exit preserves memory and logs, including gas
failure, an invalid register/span, and a rejected return length. -/
theorem metered_frame (store : HostStore NearState) (extra : Nat) (len ptr : UInt64) :
    (resultStore ((metered extra "value_return" valueReturnFn).invoke store [.i64 len, .i64 ptr])).mem =
      store.mem ∧
    (resultStore ((metered extra "value_return" valueReturnFn).invoke store [.i64 len, .i64 ptr])).host.logs =
      store.host.logs := by
  have hlogs := paid_logs store len ptr
  rw [Output.metered_valueReturn_eq]
  cases hc : applyCharges store.host (chargesBefore "value_return" store [.i64 len, .i64 ptr]) with
  | mk paid error =>
    rw [hc] at hlogs
    cases error with
    | some error => exact ⟨rfl, hlogs⟩
    | none =>
      have hraw := validated_frame (Output.paidStore store paid) len ptr
      exact ⟨hraw.1, hraw.2.trans hlogs⟩

/-- Full local return-host replay under different internal budgets. Failed low
billing is precisely a protocol gas trap; its logs equal the high call's logs.
No premise assumes a whole-run simulation or an abstract host implementation. -/
theorem metered_replay {small large : HostStore NearState} (h : StoreBelow small large)
    (extra : Nat) (len ptr : UInt64) :
    ResultBelow ((metered extra "value_return" valueReturnFn).invoke small [.i64 len, .i64 ptr])
      ((metered extra "value_return" valueReturnFn).invoke large [.i64 len, .i64 ptr]) ∨
    ∃ error, (error = .gasLimitExceeded ∨ error = .gasExceeded) ∧
      (metered extra "value_return" valueReturnFn).invoke small [.i64 len, .i64 ptr] =
        trapWith (Output.paidStore small (applyCharges small.host
          (chargesBefore "value_return" small [.i64 len, .i64 ptr])).1) error ∧
      (Output.paidStore small (applyCharges small.host
        (chargesBefore "value_return" small [.i64 len, .i64 ptr])).1).host.logs =
        (resultStore ((metered extra "value_return" valueReturnFn).invoke large [.i64 len, .i64 ptr])).host.logs := by
  cases herr : (applyCharges small.host (chargesBefore "value_return" small [.i64 len, .i64 ptr])).2 with
  | none => exact Or.inl (metered_below h extra len ptr herr)
  | some error =>
    right
    have hgas := applyCharges_error_is_gas small.host
      (chargesBefore "value_return" small [.i64 len, .i64 ptr])
      (Output.valueReturn_burnsOnly small len ptr) herr
    refine ⟨error, hgas, ?_, ?_⟩
    · exact Output.metered_valueReturn_charge_error extra small len ptr _ error (Prod.ext rfl herr)
    · exact (paid_logs small len ptr).trans
        (h.host.logs.trans (metered_frame large extra len ptr).2.symm)

end Wasm.Near.MeteredHosts.ReturnBudget
