import NearVM.GasBudget
import NearVM.MeteredHosts.Charges
import NearVM.MeteredHosts.Input

/-!
# Local budget compatibility for actual host charges

Functional host state, including the entire guest-visible context, is fixed.
Only internal gas limits and diagnostic billing profiles may differ. These
lemmas compare the actual charge executors, rather than idealized cost bounds.
-/
namespace Wasm.Near.MeteredHosts.Budget

/-- Forget billing counters and profiles, retaining every functional field. -/
def functional (host : NearState) : NearState :=
  { host with gas := {}, gasProfile := {}, actionProfile := [] }

structure HostBelow (small large : NearState) : Prop where
  fields : functional small = functional large
  gas : GasCounter.Below small.gas large.gas

namespace HostBelow

/-- Equivalent concrete frame form, useful when rebuilding machine relations. -/
theorem restore {small large : NearState} (h : HostBelow small large) :
    { small with
      gas := large.gas
      gasProfile := large.gasProfile
      actionProfile := large.actionProfile } = large := by
  have hf := congrArg (fun ns : NearState =>
    { ns with
      gas := large.gas
      gasProfile := large.gasProfile
      actionProfile := large.actionProfile }) h.fields
  simpa only [functional] using hf

theorem extCosts {small large : NearState} (h : HostBelow small large) :
    small.extCosts = large.extCosts := congrArg (·.extCosts) h.fields

theorem context {small large : NearState} (h : HostBelow small large) :
    small.context = large.context := congrArg (·.context) h.fields

theorem logs {small large : NearState} (h : HostBelow small large) :
    small.logs = large.logs := congrArg (·.logs) h.fields

theorem config {small large : NearState} (h : HostBelow small large) :
    small.config = large.config := congrArg (·.config) h.fields

/-- Equal accounting gives equal guest-visible `used_gas` after synchronization. -/
theorem syncUsed {small large : NearState} (h : HostBelow small large) :
    HostBelow
      { small with context := { small.context with usedGas := UInt64.ofNat small.gas.used } }
      { large with context := { large.context with usedGas := UInt64.ofNat large.gas.used } } := by
  have hused : small.gas.used = large.gas.used := by
    simp only [GasCounter.used, h.gas.burnt, h.gas.promises]
  have hf := congrArg (fun ns : NearState =>
    { ns with context := { ns.context with usedGas := UInt64.ofNat large.gas.used } }) h.fields
  exact ⟨by simpa only [functional, hused] using hf, h.gas⟩

theorem setRegister {small large : NearState} (h : HostBelow small large)
    (index : Nat) (bytes : List UInt8) :
    HostBelow (small.setRegister index bytes) (large.setRegister index bytes) := by
  have hf := congrArg (fun ns : NearState => ns.setRegister index bytes) h.fields
  exact ⟨by simpa only [functional, NearState.setRegister] using hf, h.gas⟩

end HostBelow

/-- Successful and failed charge lists retain every functional field. -/
theorem applyCharges_functional (host : NearState) (charges : List Charge)
    (hburn : ∀ charge ∈ charges, BurnsOnly charge) :
    functional (applyCharges host charges).1 = functional host := by
  have h := congrArg functional (applyCharges_frame host charges hburn)
  simpa only [functional] using h

theorem applyCharge_functional (host : NearState) (charge : Charge) (hburn : BurnsOnly charge) :
    functional (applyCharge host charge).1 = functional host := by
  have h := congrArg functional (applyCharge_frame host charge hburn)
  simpa only [functional] using h

/-- A successful low-budget charge replays with equal accounting and all
functional fields under the larger limits. -/
theorem applyCharge_below {small large : NearState} (h : HostBelow small large)
    (charge : Charge) (hburn : BurnsOnly charge)
    (hok : (applyCharge small charge).2 = none) :
    (applyCharge large charge).2 = none ∧
      HostBelow (applyCharge small charge).1 (applyCharge large charge).1 := by
  have hfields := (applyCharge_functional small charge hburn).trans
    (h.fields.trans (applyCharge_functional large charge hburn).symm)
  cases charge <;> simp only [BurnsOnly] at hburn
  case ext name times =>
    have hg := h.gas.burn (small.extCosts.cost name * times) hok
    refine ⟨?_, hfields, ?_⟩
    · simpa only [applyCharge, h.extCosts] using hg.1
    · simpa only [applyCharge, h.extCosts] using hg.2
  case burn cost =>
    have hg := h.gas.burn cost hok
    exact ⟨hg.1, hfields, hg.2⟩

/-- Local compatibility composes through the actual short-circuiting list. -/
theorem applyCharges_below {small large : NearState} (h : HostBelow small large)
    (charges : List Charge) (hburn : ∀ charge ∈ charges, BurnsOnly charge)
    (hok : (applyCharges small charges).2 = none) :
    (applyCharges large charges).2 = none ∧
      HostBelow (applyCharges small charges).1 (applyCharges large charges).1 := by
  induction charges generalizing small large with
  | nil => exact ⟨rfl, h⟩
  | cons charge charges ih =>
    cases hs : applyCharge small charge with
    | mk next error =>
      cases error with
      | some error => simp only [applyCharges, hs] at hok; contradiction
      | none =>
        have hc := applyCharge_below h charge (hburn charge (by simp)) (by simp only [hs])
        have ht := ih hc.2 (fun c hm => hburn c (by simp [hm]))
          (by simpa only [applyCharges, hs] using hok)
        have hl : applyCharge large charge = ((applyCharge large charge).1, none) := Prod.ext rfl hc.1
        simp only [hs] at ht
        simp only [applyCharges, hs]
        rw [hl]
        exact ht

/-- Every failure in a burn-only plan is one of the two protocol gas errors. -/
theorem applyCharge_error_is_gas (host : NearState) (charge : Charge) (hburn : BurnsOnly charge)
    {error : HostError} (herr : (applyCharge host charge).2 = some error) :
    error = .gasLimitExceeded ∨ error = .gasExceeded := by
  cases charge <;> simp only [BurnsOnly] at hburn
  case ext name times => exact GasCounter.deduct_error_is_gas host.gas _ _ herr
  case burn cost => exact GasCounter.deduct_error_is_gas host.gas _ _ herr

theorem applyCharges_error_is_gas (host : NearState) (charges : List Charge)
    (hburn : ∀ charge ∈ charges, BurnsOnly charge)
    {error : HostError} (herr : (applyCharges host charges).2 = some error) :
    error = .gasLimitExceeded ∨ error = .gasExceeded := by
  induction charges generalizing host with
  | nil => simp only [applyCharges] at herr; contradiction
  | cons charge charges ih =>
    cases hc : applyCharge host charge with
    | mk next failure =>
      cases failure with
      | none =>
        exact ih next (fun c hm => hburn c (by simp [hm]))
          (by simpa only [applyCharges, hc] using herr)
      | some failure =>
        have heq : failure = error := by simpa only [applyCharges, hc, Option.some.injEq] using herr
        subst failure
        exact applyCharge_error_is_gas host charge (hburn charge (by simp)) (by simp only [hc])

/-- A host sees identical memory and functional state across a budget replay. -/
structure StoreBelow (small large : HostStore NearState) : Prop where
  mem : small.mem = large.mem
  host : HostBelow small.host large.host

/-- Normal values and trap messages match; only billing fields may differ. -/
inductive ResultBelow : HostResult NearState → HostResult NearState → Prop
  | returned {small large : HostStore NearState} (values : List Value)
      (h : StoreBelow small large) : ResultBelow (.Return values small) (.Return values large)
  | trapped {small large : HostStore NearState} (message : String)
      (h : StoreBelow small large) : ResultBelow (.Trap small message) (.Trap large message)

/-- Functional input semantics do not inspect internal metering limits. -/
theorem raw_input_below {small large : HostStore NearState} (h : StoreBelow small large)
    (register : UInt64) :
    ResultBelow (inputFn.invoke small [.i64 register]) (inputFn.invoke large [.i64 register]) := by
  have hinput := congrArg (·.input) h.host.context
  by_cases hregister : register = u64Max
  · subst register
    rw [Input.raw_discard, Input.raw_discard]
    exact .returned [] h
  · cases hl : withinLimit small.host.config.maxRegisterLen small.host.context.input.length with
    | true =>
      have hlarge : withinLimit large.host.config.maxRegisterLen large.host.context.input.length = true := by
        simpa only [← h.host.config, ← hinput] using hl
      rw [Input.raw_ok small register hregister hl, Input.raw_ok large register hregister hlarge]
      apply ResultBelow.returned []
      exact ⟨h.mem, by simpa only [hinput] using h.host.setRegister register.toNat small.host.context.input⟩
    | false =>
      have hlarge : withinLimit large.host.config.maxRegisterLen large.host.context.input.length = false := by
        simpa only [← h.host.config, ← hinput] using hl
      rw [Input.raw_too_long small register hregister hl, Input.raw_too_long large register hregister hlarge]
      exact .trapped _ h

/-- Successful low-budget input billing replays under the high budget,
including the wrapper's synchronization of the observed gas counter. -/
theorem input_paid_below {small large : HostStore NearState} (h : StoreBelow small large)
    (hok : (applyCharges small.host [.ext "base", .ext "write_register_base"]).2 = none) :
    (applyCharges large.host [.ext "base", .ext "write_register_base"]).2 = none ∧
      StoreBelow (Input.paid small) (Input.paid large) := by
  have hc := applyCharges_below h.host [.ext "base", .ext "write_register_base"]
    (by simp [BurnsOnly]) hok
  exact ⟨hc.1, h.mem, hc.2.syncUsed⟩

/-- The actual metered input wrappers return the same result after any
successful low-budget charge plan, even when raw input rejects its size. -/
theorem metered_input_below {small large : HostStore NearState} (h : StoreBelow small large)
    (extra : Nat) (register : UInt64)
    (hok : (applyCharges small.host [.ext "base", .ext "write_register_base"]).2 = none) :
    ResultBelow ((metered extra "input" inputFn).invoke small [.i64 register])
      ((metered extra "input" inputFn).invoke large [.i64 register]) := by
  have hp := input_paid_below h hok
  rw [Input.metered_eq, Input.metered_eq, hok, hp.1]
  exact raw_input_below hp.2 register

/-- The store carried by either host-call exit. -/
def resultStore : HostResult NearState → HostStore NearState
  | .Return _ store => store
  | .Trap store _ => store

theorem raw_input_frame (store : HostStore NearState) (register : UInt64) :
    (resultStore (inputFn.invoke store [.i64 register])).mem = store.mem ∧
    (resultStore (inputFn.invoke store [.i64 register])).host.logs = store.host.logs := by
  by_cases hregister : register = u64Max
  · subst register
    rw [Input.raw_discard]
    exact ⟨rfl, rfl⟩
  · cases hl : withinLimit store.host.config.maxRegisterLen store.host.context.input.length with
    | true => rw [Input.raw_ok store register hregister hl]; exact ⟨rfl, rfl⟩
    | false => rw [Input.raw_too_long store register hregister hl]; exact ⟨rfl, rfl⟩

/-- Input never appends logs or writes memory, on gas failures and raw failures
as well as successful calls. -/
theorem metered_input_frame (store : HostStore NearState) (extra : Nat) (register : UInt64) :
    (resultStore ((metered extra "input" inputFn).invoke store [.i64 register])).mem = store.mem ∧
    (resultStore ((metered extra "input" inputFn).invoke store [.i64 register])).host.logs =
      store.host.logs := by
  have hlogs : (Input.paid store).host.logs = store.host.logs := by
    have hf := congrArg (fun st : HostStore NearState => st.host.logs) (Input.paid_frame store)
    exact hf
  rw [Input.metered_eq]
  cases herr : (applyCharges store.host [.ext "base", .ext "write_register_base"]).2 with
  | some error => exact ⟨rfl, hlogs⟩
  | none =>
    have hraw := raw_input_frame (Input.paid store) register
    exact ⟨hraw.1, hraw.2.trans hlogs⟩

/-- Full local replay for actual metered input: identical functional results,
or a low-budget protocol gas error before any functional input effect. Input
logs remain equal, which is stronger than the prefix needed by the runner. -/
theorem metered_input_replay {small large : HostStore NearState} (h : StoreBelow small large)
    (extra : Nat) (register : UInt64) :
    ResultBelow ((metered extra "input" inputFn).invoke small [.i64 register])
      ((metered extra "input" inputFn).invoke large [.i64 register]) ∨
    ∃ error, (error = .gasLimitExceeded ∨ error = .gasExceeded) ∧
      (metered extra "input" inputFn).invoke small [.i64 register] = trapWith (Input.paid small) error ∧
      (Input.paid small).host.logs =
        (resultStore ((metered extra "input" inputFn).invoke large [.i64 register])).host.logs := by
  cases herr : (applyCharges small.host [.ext "base", .ext "write_register_base"]).2 with
  | none => exact Or.inl (metered_input_below h extra register herr)
  | some error =>
    right
    have hgas := applyCharges_error_is_gas small.host [.ext "base", .ext "write_register_base"]
      (by simp [BurnsOnly]) herr
    refine ⟨error, hgas, ?_, ?_⟩
    · rw [Input.metered_eq, herr]
    · have hpaid : (Input.paid small).host.logs = small.host.logs := by
        have hf := congrArg (fun st : HostStore NearState => st.host.logs) (Input.paid_frame small)
        exact hf
      exact hpaid.trans (h.host.logs.trans (metered_input_frame large extra register).2.symm)

end Wasm.Near.MeteredHosts.Budget
