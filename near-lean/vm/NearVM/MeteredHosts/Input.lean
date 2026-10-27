import NearVM.MeteredLogic
import NearVM.MeteredHosts.Charges

/-!
# The metered `env.input` contract

The input buffer is shared with a register: its cost is `base` plus
`write_register_base`, independent of the input length. Oversized inputs trap
only after those charges. The discard-register sentinel bypasses the size limit.
-/

namespace Wasm.Near.MeteredHosts.Input

/-- Successful raw input writes precisely one register, framing all other host
state and the complete memory. -/
theorem raw_ok (st : HostStore NearState) (register : UInt64)
    (hregister : register ≠ u64Max)
    (hlimit : withinLimit st.host.config.maxRegisterLen st.host.context.input.length = true) :
    inputFn.invoke st [.i64 register] =
      .Return [] { st with host := st.host.setRegister register.toNat st.host.context.input } := by
  simp only [inputFn, writeRegisterResult, checkedSetRegister?, hregister, ↓reduceIte, hlimit]

/-- The maximum register id discards input without checking its length. -/
theorem raw_discard (st : HostStore NearState) :
    inputFn.invoke st [.i64 u64Max] = .Return [] st := by
  simp only [inputFn, writeRegisterResult, checkedSetRegister?, ↓reduceIte]

/-- A size failure retains the entire original store. -/
theorem raw_too_long (st : HostStore NearState) (register : UInt64)
    (hregister : register ≠ u64Max)
    (hlimit : withinLimit st.host.config.maxRegisterLen st.host.context.input.length = false) :
    inputFn.invoke st [.i64 register] = .Trap st "input: register size exceeded" := by
  simp only [inputFn, writeRegisterResult, checkedSetRegister?, hregister, ↓reduceIte,
    hlimit, Bool.false_eq_true]
  rfl

/-- The host charge, with no per-byte input-copy charge. -/
def cost (host : NearState) : Nat :=
  host.extCosts.cost "base" + host.extCosts.cost "write_register_base"

theorem charges_before (st : HostStore NearState) (args : List Value) :
    chargesBefore "input" st args = [.ext "base", .ext "write_register_base"] := by
  simp [chargesBefore, storageMutationPlan?, creationAccountArgs, chargesBeforeUnvalidated]

theorem pre_error (st : HostStore NearState) (args : List Value) :
    preInvokeError "input" st args = none := by
  simp [preInvokeError, invocationArgumentError, storageMutationPlan?, globalContractInputs?,
    creationPrefixError, creationAccountError, creationAccountArgs, allocatesPromise,
    functionCallInputError, functionCallInputs?]

/-- Input has no post-call charges, deposits, storage mutation or encoding check. -/
theorem finish (extra : Nat) (before : HostStore NearState) (args : List Value)
    (result : HostResult NearState) :
    finishMeteredCall extra "input" before args result = result := by
  cases result <;>
    simp [finishMeteredCall, chargesAfter, cryptoHostNames, applyCharges,
      deductDeposit, promiseDeposit?, actionMethodEncodingError, actionMethodBytes?,
      usesKeyMethodFields, functionCallInputs?, updateStorageUsage]

/-- The store after pre-call charges, including the observable `used_gas`
context synchronization performed by the actual metered wrapper. -/
def paid (st : HostStore NearState) : HostStore NearState :=
  let ns := (applyCharges st.host [.ext "base", .ext "write_register_base"]).1
  { st with host := { ns with context := { ns.context with usedGas := UInt64.ofNat ns.gas.used } } }

/-- Billing and synchronizing `used_gas` preserve the input and register limit. -/
theorem paid_input (st : HostStore NearState) :
    (paid st).host.context.input = st.host.context.input := by
  simp only [paid, applyCharges, applyCharge]
  cases hfirst : (st.host.gas.burn (st.host.extCosts.cost "base" * 1)).2 <;>
    cases hsecond : ((st.host.gas.burn (st.host.extCosts.cost "base" * 1)).1.burn
      (st.host.extCosts.cost "write_register_base" * 1)).2 <;>
    simp only [hsecond]

theorem paid_config (st : HostStore NearState) :
    (paid st).host.config = st.host.config := by
  simp only [paid, applyCharges, applyCharge]
  cases hfirst : (st.host.gas.burn (st.host.extCosts.cost "base" * 1)).2 <;>
    cases hsecond : ((st.host.gas.burn (st.host.extCosts.cost "base" * 1)).1.burn
      (st.host.extCosts.cost "write_register_base" * 1)).2 <;>
    simp only [hsecond]

/-- Every host field outside gas, gas profiling and the observed gas counter is
framed by input's pre-call charges, including storage, logs and other registers. -/
theorem paid_frame (st : HostStore NearState) :
    paid st = { st with host := { st.host with
      gas := (paid st).host.gas
      gasProfile := (paid st).host.gasProfile
      context := { st.host.context with usedGas := (paid st).host.context.usedGas } } } := by
  simp only [paid, applyCharges, applyCharge]
  cases hfirst : (st.host.gas.burn (st.host.extCosts.cost "base" * 1)).2 <;>
    cases hsecond : ((st.host.gas.burn (st.host.extCosts.cost "base" * 1)).1.burn
      (st.host.extCosts.cost "write_register_base" * 1)).2 <;>
    simp only [hsecond]

/-- Exact operational contract for the actual metered wrapper, including both
gas failures and the raw register-length trap. -/
theorem metered_eq (extra : Nat) (st : HostStore NearState) (register : UInt64) :
    (metered extra "input" inputFn).invoke st [.i64 register] =
      match (applyCharges st.host [.ext "base", .ext "write_register_base"]).2 with
      | some error => trapWith (paid st) error
      | none => inputFn.invoke (paid st) [.i64 register] := by
  simp only [metered]
  have hdeprecated : deprecatedRuntimeHost "input" = false := by decide
  have hview : viewRestrictedHost "input" = false := by decide
  simp only [hdeprecated, Bool.false_eq_true, ↓reduceIte, hview, Bool.and_false,
    charges_before, paid]
  cases hc : applyCharges st.host [.ext "base", .ext "write_register_base"] with
  | mk ns error =>
    cases error with
    | some error => rfl
    | none =>
      simp only [pre_error, invokeStorageCall,
        prepareStorageCall_other "input" _ _ (by decide), finish]

/-- Sufficient charging and the register limit give an exact final store. -/
theorem metered_ok (extra : Nat) (st : HostStore NearState) (register : UInt64)
    (hcharge : (applyCharges st.host [.ext "base", .ext "write_register_base"]).2 = none)
    (hregister : register ≠ u64Max)
    (hlimit : withinLimit st.host.config.maxRegisterLen st.host.context.input.length = true) :
    (metered extra "input" inputFn).invoke st [.i64 register] =
      .Return [] { paid st with host :=
        (paid st).host.setRegister register.toNat st.host.context.input } := by
  rw [metered_eq, hcharge]
  simpa only [paid_input, paid_config] using raw_ok (paid st) register hregister
    (by simpa only [paid_input, paid_config] using hlimit)

theorem metered_too_long (extra : Nat) (st : HostStore NearState) (register : UInt64)
    (hcharge : (applyCharges st.host [.ext "base", .ext "write_register_base"]).2 = none)
    (hregister : register ≠ u64Max)
    (hlimit : withinLimit st.host.config.maxRegisterLen st.host.context.input.length = false) :
    (metered extra "input" inputFn).invoke st [.i64 register] =
      .Trap (paid st) "input: register size exceeded" := by
  rw [metered_eq, hcharge]
  exact raw_too_long (paid st) register hregister
    (by simpa only [paid_input, paid_config] using hlimit)

/-- The fixed host cost is affordable from the offered reservation, and the
unused gas frame survives with unchanged promise obligations. -/
theorem paid_credits (st : HostStore NearState) (rest : Nat)
    (hcredits : st.host.gas.Credits (cost st.host + rest)) :
    (applyCharges st.host [.ext "base", .ext "write_register_base"]).2 = none ∧
    (paid st).host.gas.burnt = st.host.gas.burnt + cost st.host ∧
    (paid st).host.gas.promises = st.host.gas.promises ∧
    (paid st).host.gas.Credits rest := by
  have h := applyCharges_credits st.host [.ext "base", .ext "write_register_base"] rest
    (by simp [BurnsOnly]) (by simpa [burnSum, burnCost, cost] using hcredits)
  refine ⟨h.1, ?_, h.2.2.1, h.2.2.2.2⟩
  simpa only [paid, cost, burnSum, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, burnCost, Nat.mul_one, Nat.add_zero] using h.2.1

/-- The gas-threaded semantic contract used by the walking skeleton. The exact
store equation frames every effect except the target register and gas fields.
The caller-owned residual credits survive both host charges. -/
theorem contract (extra : Nat) (st : HostStore NearState) (register : UInt64) (rest : Nat)
    (hcredits : st.host.gas.Credits (cost st.host + rest))
    (hregister : register ≠ u64Max)
    (hlimit : withinLimit st.host.config.maxRegisterLen st.host.context.input.length = true) :
    let final : HostStore NearState :=
      ⟨st.mem, NearState.setRegister (paid st).host register.toNat st.host.context.input⟩
    (metered extra "input" inputFn).invoke st [.i64 register] = .Return [] final ∧
    final.mem = st.mem ∧
    final.host.registers register.toNat = some st.host.context.input ∧
    final.host.gas.burnt = st.host.gas.burnt + cost st.host ∧
    final.host.gas.promises = st.host.gas.promises ∧
    final.host.gas.Credits rest := by
  have hp := paid_credits st rest hcredits
  refine ⟨metered_ok extra st register hp.1 hregister hlimit, rfl, ?_, hp.2⟩
  simp only [NearState.setRegister, ↓reduceIte]

theorem metered_discard (extra : Nat) (st : HostStore NearState) (rest : Nat)
    (hcredits : st.host.gas.Credits (cost st.host + rest)) :
    (metered extra "input" inputFn).invoke st [.i64 u64Max] = .Return [] (paid st) := by
  rw [metered_eq, (paid_credits st rest hcredits).1]
  exact raw_discard _
/-- Register-size rejection spends the same fixed charge and preserves the
residual credit frame. The register update and memory effects never occur. -/
theorem too_long_contract (extra : Nat) (st : HostStore NearState) (register : UInt64) (rest : Nat)
    (hcredits : st.host.gas.Credits (cost st.host + rest))
    (hregister : register ≠ u64Max)
    (hlimit : withinLimit st.host.config.maxRegisterLen st.host.context.input.length = false) :
    (metered extra "input" inputFn).invoke st [.i64 register] =
      .Trap (paid st) "input: register size exceeded" ∧
    (paid st).host.gas.burnt = st.host.gas.burnt + cost st.host ∧
    (paid st).host.gas.Credits rest := by
  have hp := paid_credits st rest hcredits
  exact ⟨metered_too_long extra st register hp.1 hregister hlimit, hp.2.1, hp.2.2.2⟩

/-- The first matching linked host is the actual metered input wrapper. -/
theorem lookup (cfg : RuntimeConfig) :
    (meteredHostFns cfg).find? (fun p => importMatches p.1
      { «module» := "env", name := "input", params := [.i64], results := [] }) =
      some ({ «module» := "env", name := "input", params := [.i64], results := [] },
        metered cfg.fees.numExtraBytesRecord "input" inputFn) := by
  rfl

end Wasm.Near.MeteredHosts.Input
