import NearVM.MeteredHosts.Budget
import NearVM.MeteredHosts.Output

/-!
# Budget replay for actual UTF-8 logging

Fixed-length and NUL-terminated reads, decoding errors and both log limits
share the actual string-reader/charge plan. The reader observes memory and
functional host fields, never internal gas limits or billing profiles.
-/
namespace Wasm.Near.MeteredHosts.LogBudget
open Budget

private def withBilling (st : HostStore NearState) (gas : GasCounter)
    (profile : GasProfile) (actions : List (String × Nat)) : HostStore NearState :=
  { st with host := { st.host with gas, gasProfile := profile, actionProfile := actions } }

private theorem scan_billing (st : HostStore NearState) (gas : GasCounter)
    (profile : GasProfile) (actions : List (String × Nat)) (ptr maxLen fuel index : Nat)
    (acc : List UInt8) :
    scanNulBytes (withBilling st gas profile actions) ptr maxLen fuel index acc =
      scanNulBytes st ptr maxLen fuel index acc := by
  induction fuel generalizing index acc with
  | zero => rfl
  | succ fuel ih =>
    simp only [scanNulBytes,
      show memorySize (withBilling st gas profile actions) = memorySize st from rfl,
      show (withBilling st gas profile actions).mem = st.mem from rfl,
      show totalLogLengthExceeded (withBilling st gas profile actions) (maxLen + 1) =
        totalLogLengthExceeded st (maxLen + 1) from rfl, ih]

private theorem utf8_billing (st : HostStore NearState) (gas : GasCounter)
    (profile : GasProfile) (actions : List (String × Nat)) (len ptr : UInt64) :
    readUtf8String (withBilling st gas profile actions) len ptr = readUtf8String st len ptr := by
  unfold readUtf8String
  simp only [show logSpace (withBilling st gas profile actions) = logSpace st from rfl,
    scan_billing]
  rfl

private theorem log_billing (st : HostStore NearState) (gas : GasCounter)
    (profile : GasProfile) (actions : List (String × Nat)) (len ptr : UInt64) :
    logUtf8Read (withBilling st gas profile actions) len ptr = logUtf8Read st len ptr := by
  unfold logUtf8Read
  simp only [show logCountError (withBilling st gas profile actions) = logCountError st from rfl,
    utf8_billing]
  rfl

/-- The complete decoder and ordered charge plan agree across budget changes,
including the unbounded-length sentinel's byte-by-byte NUL scan. -/
theorem read_eq {small large : HostStore NearState} (h : StoreBelow small large)
    (len ptr : UInt64) : logUtf8Read small len ptr = logUtf8Read large len ptr := by
  have hs := congrArg₂ (fun mem host => (⟨mem, host⟩ : HostStore NearState)) h.mem h.host.fields
  have hr := congrArg (fun st : HostStore NearState => logUtf8Read st len ptr) hs
  exact (log_billing small {} {} [] len ptr).symm.trans
    (hr.trans (log_billing large {} {} [] len ptr))

theorem plan_eq {small large : HostStore NearState} (h : StoreBelow small large)
    (len ptr : UInt64) :
    chargesBefore "log_utf8" small [.i64 len, .i64 ptr] =
      chargesBefore "log_utf8" large [.i64 len, .i64 ptr] := by
  rw [Output.chargesBefore_logUtf8, Output.chargesBefore_logUtf8, read_eq h len ptr]

private theorem append_below {small large : NearState} (h : HostBelow small large)
    (msg : List UInt8) :
    HostBelow { small with logs := small.logs ++ [msg] } { large with logs := large.logs ++ [msg] } := by
  have hf := congrArg (fun ns : NearState => { ns with logs := ns.logs ++ [msg] }) h.fields
  exact ⟨by simpa only [functional] using hf, h.gas⟩

private theorem error_below {small large : NearState} (h : HostBelow small large)
    (error : HostError) :
    HostBelow { small with lastError := some error } { large with lastError := some error } := by
  have hf := congrArg (fun ns : NearState => { ns with lastError := some error }) h.fields
  exact ⟨by simpa only [functional] using hf, h.gas⟩

/-- The real functional logger either appends the same decoded message, or
records the same precise decoding/limit/read error. -/
theorem raw_below {small large : HostStore NearState} (h : StoreBelow small large)
    (len ptr : UInt64) :
    ResultBelow (logUtf8Fn.invoke small [.i64 len, .i64 ptr])
      (logUtf8Fn.invoke large [.i64 len, .i64 ptr]) := by
  have heq := congrArg StringRead.result (read_eq h len ptr)
  cases hr : (logUtf8Read small len ptr).result with
  | ok msg =>
    have hl := heq.symm.trans hr
    rw [Output.logUtf8_ok small len ptr msg hr, Output.logUtf8_ok large len ptr msg hl]
    exact .returned [] ⟨h.mem, append_below h.host msg⟩
  | error error =>
    have hl := heq.symm.trans hr
    rw [Output.logUtf8_error small len ptr error hr, Output.logUtf8_error large len ptr error hl]
    exact .trapped _ ⟨h.mem, error_below h.host error⟩

private theorem metered_charged (st : HostStore NearState) (extra : Nat) (len ptr : UInt64)
    (hok : (applyCharges st.host (chargesBefore "log_utf8" st [.i64 len, .i64 ptr])).2 = none) :
    (metered extra "log_utf8" logUtf8Fn).invoke st [.i64 len, .i64 ptr] =
      logUtf8Fn.invoke (Output.paidStore st
        (applyCharges st.host (chargesBefore "log_utf8" st [.i64 len, .i64 ptr])).1) [.i64 len, .i64 ptr] := by
  rw [Output.metered_logUtf8_eq]
  cases hc : applyCharges st.host (chargesBefore "log_utf8" st [.i64 len, .i64 ptr]) with
  | mk paid error =>
    cases error with
    | none => rfl
    | some error => simp only [hc] at hok; contradiction

/-- Successful low billing replays the actual metered logger. This also covers
all ordinary errors after reading, including invalid UTF-8 and exceeded limits. -/
theorem metered_below {small large : HostStore NearState} (h : StoreBelow small large)
    (extra : Nat) (len ptr : UInt64)
    (hok : (applyCharges small.host (chargesBefore "log_utf8" small [.i64 len, .i64 ptr])).2 = none) :
    ResultBelow ((metered extra "log_utf8" logUtf8Fn).invoke small [.i64 len, .i64 ptr])
      ((metered extra "log_utf8" logUtf8Fn).invoke large [.i64 len, .i64 ptr]) := by
  have hc := applyCharges_below h.host (chargesBefore "log_utf8" small [.i64 len, .i64 ptr])
    (Output.logUtf8_burnsOnly small len ptr) hok
  have hhigh : (applyCharges large.host (chargesBefore "log_utf8" large [.i64 len, .i64 ptr])).2 = none := by
    rw [← plan_eq h len ptr]
    exact hc.1
  have hp : StoreBelow
      (Output.paidStore small (applyCharges small.host
        (chargesBefore "log_utf8" small [.i64 len, .i64 ptr])).1)
      (Output.paidStore large (applyCharges large.host
        (chargesBefore "log_utf8" large [.i64 len, .i64 ptr])).1) := by
    rw [← plan_eq h len ptr]
    exact ⟨h.mem, hc.2.syncUsed⟩
  rw [metered_charged small extra len ptr hok, metered_charged large extra len ptr hhigh]
  exact raw_below hp len ptr

private theorem raw_frame (store : HostStore NearState) (len ptr : UInt64) :
    (resultStore (logUtf8Fn.invoke store [.i64 len, .i64 ptr])).mem = store.mem ∧
    List.IsPrefix store.host.logs (resultStore (logUtf8Fn.invoke store [.i64 len, .i64 ptr])).host.logs := by
  cases hr : (logUtf8Read store len ptr).result with
  | ok msg =>
    rw [Output.logUtf8_ok store len ptr msg hr]
    exact ⟨rfl, [msg], rfl⟩
  | error error =>
    rw [Output.logUtf8_error store len ptr error hr]
    exact ⟨rfl, [], List.append_nil _⟩

private theorem paid_logs (store : HostStore NearState) (len ptr : UInt64) :
    (Output.paidStore store (applyCharges store.host
      (chargesBefore "log_utf8" store [.i64 len, .i64 ptr])).1).host.logs = store.host.logs := by
  have hf := congrArg NearState.logs (applyCharges_frame store.host
    (chargesBefore "log_utf8" store [.i64 len, .i64 ptr]) (Output.logUtf8_burnsOnly store len ptr))
  exact hf

/-- The actual logger retains memory and only extends logs. Its gas failures
and ordinary failures retain the original logs exactly. -/
theorem metered_frame (store : HostStore NearState) (extra : Nat) (len ptr : UInt64) :
    (resultStore ((metered extra "log_utf8" logUtf8Fn).invoke store [.i64 len, .i64 ptr])).mem = store.mem ∧
    List.IsPrefix store.host.logs
      (resultStore ((metered extra "log_utf8" logUtf8Fn).invoke store [.i64 len, .i64 ptr])).host.logs := by
  have hlogs := paid_logs store len ptr
  rw [Output.metered_logUtf8_eq]
  cases hc : applyCharges store.host (chargesBefore "log_utf8" store [.i64 len, .i64 ptr]) with
  | mk paid error =>
    rw [hc] at hlogs
    cases error with
    | some error =>
      refine ⟨rfl, [], ?_⟩
      simpa only [List.append_nil, resultStore, trapWith] using hlogs.symm
    | none =>
      have hraw := raw_frame (Output.paidStore store paid) len ptr
      exact ⟨hraw.1, by simpa only [hlogs] using hraw.2⟩

/-- Full local budget replay, with an actual protocol gas error at the first
failed low charge. Its retained logs precede the high host's final logs, even
when the high host appends the message that the low host cannot afford. -/
theorem metered_replay {small large : HostStore NearState} (h : StoreBelow small large)
    (extra : Nat) (len ptr : UInt64) :
    ResultBelow ((metered extra "log_utf8" logUtf8Fn).invoke small [.i64 len, .i64 ptr])
      ((metered extra "log_utf8" logUtf8Fn).invoke large [.i64 len, .i64 ptr]) ∨
    ∃ error, (error = .gasLimitExceeded ∨ error = .gasExceeded) ∧
      (metered extra "log_utf8" logUtf8Fn).invoke small [.i64 len, .i64 ptr] =
        trapWith (Output.paidStore small (applyCharges small.host
          (chargesBefore "log_utf8" small [.i64 len, .i64 ptr])).1) error ∧
      List.IsPrefix (Output.paidStore small (applyCharges small.host
        (chargesBefore "log_utf8" small [.i64 len, .i64 ptr])).1).host.logs
        (resultStore ((metered extra "log_utf8" logUtf8Fn).invoke large [.i64 len, .i64 ptr])).host.logs := by
  cases herr : (applyCharges small.host (chargesBefore "log_utf8" small [.i64 len, .i64 ptr])).2 with
  | none => exact Or.inl (metered_below h extra len ptr herr)
  | some error =>
    right
    have hgas := applyCharges_error_is_gas small.host
      (chargesBefore "log_utf8" small [.i64 len, .i64 ptr])
      (Output.logUtf8_burnsOnly small len ptr) herr
    refine ⟨error, hgas, ?_, ?_⟩
    · exact Output.metered_logUtf8_charge_error extra small len ptr _ error (Prod.ext rfl herr)
    · rw [paid_logs small len ptr, h.host.logs]
      exact (metered_frame large extra len ptr).2

end Wasm.Near.MeteredHosts.LogBudget
