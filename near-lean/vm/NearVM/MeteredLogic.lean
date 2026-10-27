import NearVM.GasCredits
import NearVM.Run

/-!
# Contracts for the gas-metered machine

These total execution contracts carry gas credits through `runMetered`, including
its trap, host-error and fuel-exhaustion exits. They are a small foundation for
M2: memory and host-state separation assertions can be supplied as part of the
postcondition, without replacing the actual NEAR interpreter by an unmetered one.
A proof of `WP` alone does not exclude fuel exhaustion or traps: a successful
contract must exclude them explicitly in its postcondition.
-/

namespace Wasm.Near.MeteredLogic

/-- A postcondition sees the credits left, final machine and outer execution
error. A Wasm trap is in the machine, rather than the outer error. -/
abbrev Post := Nat → Machine → Option FunctionCallError → Prop

/-- Credits pay for increases in both burnt and used gas and remain available in
the final counter. Promise reservations consume credits even when they burn
nothing; failed calls may drop reservations. Credits cannot be manufactured. -/
def Pays (before : Machine) (credits : Nat) (after : Machine) (remaining : Nat) : Prop :=
  remaining ≤ credits ∧
  after.host.gas.burnt + remaining ≤ before.host.gas.burnt + credits ∧
  after.host.gas.used + remaining ≤ before.host.gas.used + credits ∧
  after.host.gas.Credits remaining

/-- A zero charge is the identity when the current gas counter is valid. -/
theorem chargeWasm_zero (m : Machine) (hcredits : m.host.gas.Credits 0) :
    chargeWasm m 0 = (m, none) := by
  have hlimits : m.host.gas.burnt + 0 ≤ m.host.gas.maxBurnt ∧
      m.host.gas.burnt + 0 + (m.host.gas.promises + (0 - 0)) ≤ m.host.gas.prepaid := by
    simpa only [GasCounter.Credits, GasCounter.used, Nat.add_zero, Nat.sub_self] using hcredits
  cases m <;>
    simp only [chargeWasm, chargeConfig, chargeHost, GasCounter.burn, GasCounter.deduct,
      StepResult.host] at *
  all_goals simp only [Nat.add_zero, Nat.sub_self] at hlimits
  all_goals simp only [Nat.add_zero, Nat.sub_self, ite_eq_left hlimits]

/-- The initial counter has the offered credits, and actual execution satisfies
the postcondition while retaining the unspent credit frame. -/
def WP (cfg : WasmConfig) (fuel : Nat) (m : Machine) (credits : Nat) (post : Post) : Prop :=
  m.host.gas.Credits credits ∧
  ∃ remaining, Pays m credits (runMetered cfg fuel m).1 remaining ∧
    post remaining (runMetered cfg fuel m).1 (runMetered cfg fuel m).2

namespace Pays

theorem refl {m : Machine} {credits : Nat} (h : m.host.gas.Credits credits) :
    Pays m credits m credits := ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, h⟩

/-- Gas accounting composes across function and instruction boundaries. -/
theorem trans {a b c : Machine} {initial middle final : Nat}
    (hab : Pays a initial b middle) (hbc : Pays b middle c final) :
    Pays a initial c final := by
  obtain ⟨hab_le, hab_burn, hab_used, _⟩ := hab
  obtain ⟨hbc_le, hbc_burn, hbc_used, hcredits⟩ := hbc
  exact ⟨Nat.le_trans hbc_le hab_le, by omega, by omega, hcredits⟩

theorem burnt_le {before after : Machine} {credits remaining : Nat}
    (h : Pays before credits after remaining) :
    after.host.gas.burnt ≤ before.host.gas.burnt + credits := by
  obtain ⟨_, heq, _, _⟩ := h
  omega

/-- Burning a known cost preserves a caller's remaining gas frame. -/
theorem chargeWasm (m : Machine) (cost rest : Nat)
    (hcredits : m.host.gas.Credits (cost + rest)) :
    (Wasm.Near.chargeWasm m cost).2 = none ∧
      Pays m (cost + rest) (Wasm.Near.chargeWasm m cost).1 rest := by
  have hburn := GasCounter.burn_credits m.host.gas cost rest hcredits
  obtain ⟨hok, hburnt, hpromises, hrest⟩ := hburn
  cases m <;> simp only [Pays, Wasm.Near.chargeWasm, chargeConfig, chargeHost, StepResult.host] at *
  all_goals refine ⟨hok, Nat.le_add_left _ _, ?_, ?_, hrest⟩
  all_goals simp only [GasCounter.used, hburnt, hpromises]
  all_goals omega

/-- The configuration form is convenient before the instruction has run. -/
theorem chargeConfig (c : Config NearState) (cost rest : Nat)
    (hcredits : c.store.host.gas.Credits (cost + rest)) :
    (Wasm.Near.chargeConfig c cost).2 = none ∧
      Pays (.next c) (cost + rest) (.next (Wasm.Near.chargeConfig c cost).1) rest :=
  chargeWasm (.next c) cost rest hcredits

/-- A machine step preserving the gas counter preserves the whole credit frame. -/
theorem of_gas_eq {before after : Machine} {credits : Nat}
    (heq : after.host.gas = before.host.gas) (hcredits : before.host.gas.Credits credits) :
    Pays before credits after credits := by
  simp only [Pays, heq]
  exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, hcredits⟩

end Pays

/-- Change the postcondition without replaying execution or reproving gas. -/
theorem WP.mono {cfg : WasmConfig} {fuel : Nat} {m : Machine} {credits : Nat}
    {post post' : Post} (h : WP cfg fuel m credits post)
    (hpost : ∀ remaining final error, post remaining final error → post' remaining final error) :
    WP cfg fuel m credits post' := by
  obtain ⟨hcredits, remaining, hpays, hresult⟩ := h
  exact ⟨hcredits, remaining, hpays, hpost _ _ _ hresult⟩

/-- Adequacy uses the actual metered execution, including its final host state. -/
theorem WP.result {cfg : WasmConfig} {fuel : Nat} {m : Machine} {credits : Nat}
    {post : Post} (h : WP cfg fuel m credits post) :
    ∃ remaining, post remaining (runMetered cfg fuel m).1 (runMetered cfg fuel m).2 ∧
      remaining ≤ credits ∧
      (runMetered cfg fuel m).1.host.gas.burnt + remaining ≤ m.host.gas.burnt + credits ∧
      (runMetered cfg fuel m).1.host.gas.used + remaining ≤ m.host.gas.used + credits ∧
      (runMetered cfg fuel m).1.host.gas.Credits remaining := by
  obtain ⟨_, remaining, hpays, hpost⟩ := h
  exact ⟨remaining, hpost, hpays⟩

theorem WP.burnt_le {cfg : WasmConfig} {fuel : Nat} {m : Machine} {credits : Nat}
    {post : Post} (h : WP cfg fuel m credits post) :
    (runMetered cfg fuel m).1.host.gas.burnt ≤ m.host.gas.burnt + credits := by
  obtain ⟨_, _, hpays, _⟩ := h
  exact hpays.burnt_le

/-- Total gas includes gas reserved for promises, not only burnt gas. -/
theorem WP.used_le {cfg : WasmConfig} {fuel : Nat} {m : Machine} {credits : Nat}
    {post : Post} (h : WP cfg fuel m credits post) :
    (runMetered cfg fuel m).1.host.gas.used ≤ m.host.gas.used + credits := by
  obtain ⟨_, _, hpays, _⟩ := h
  obtain ⟨_, _, hused, _⟩ := hpays
  omega

/-- Reusing an interpreter run equation preserves both the logical result and
all gas accounting; useful for fuel stability and interpreter optimizations. -/
theorem WP.of_run_eq {cfg : WasmConfig} {fuel fuel' : Nat} {m : Machine} {credits : Nat}
    {post : Post} (h : WP cfg fuel m credits post)
    (heq : runMetered cfg fuel' m = runMetered cfg fuel m) :
    WP cfg fuel' m credits post := by
  unfold WP at *
  simpa only [heq] using h

/-- A concrete run equation can discharge either a normal or an error exit. -/
theorem wp_of_run {cfg : WasmConfig} {fuel : Nat} {m final : Machine}
    {error : Option FunctionCallError} {credits remaining : Nat} {post : Post}
    (hrun : runMetered cfg fuel m = (final, error))
    (hcredits : m.host.gas.Credits credits) (hpays : Pays m credits final remaining)
    (hpost : post remaining final error) : WP cfg fuel m credits post := by
  exact ⟨hcredits, remaining, by simpa only [hrun] using hpays,
    by simpa only [hrun] using hpost⟩

theorem wp_done (cfg : WasmConfig) (fuel : Nat) (values : List Value)
    (store : Store NearState) (credits : Nat) (post : Post)
    (hcredits : store.host.gas.Credits credits) (hpost : post credits (.done values store) none) :
    WP cfg fuel (.done values store) credits post :=
  wp_of_run (runMetered_done cfg fuel values store) hcredits (Pays.refl hcredits) hpost

theorem wp_trap (cfg : WasmConfig) (fuel : Nat) (reason : Trap)
    (store : Store NearState) (credits : Nat) (post : Post)
    (hcredits : store.host.gas.Credits credits) (hpost : post credits (.trap reason store) none) :
    WP cfg fuel (.trap reason store) credits post :=
  wp_of_run (runMetered_trapped cfg fuel reason store) hcredits (Pays.refl hcredits) hpost

/-- Fuel exhaustion is an explicit exit, with no gas spent by the absent step.
Successful contracts must reject this postcondition. -/
theorem wp_zero (cfg : WasmConfig) (c : Config NearState) (credits : Nat) (post : Post)
    (hcredits : c.store.host.gas.Credits credits)
    (hpost : post credits (.next c) (some (.executionIssue .fuelExhausted))) :
    WP cfg 0 (.next c) credits post :=
  wp_of_run (runMetered_zero cfg c) hcredits (Pays.refl hcredits) hpost

/-- Expose both charges of one interpreter step. Contracts for host calls must
include their own gas; the `Pays` premise covers those charges as well. -/
theorem wp_next {cfg : WasmConfig} {fuel : Nat} {c charged : Config NearState}
    {next : Machine} {credits middle : Nat} {post : Post}
    (hcredits : c.store.host.gas.Credits credits)
    (hop : chargeConfig c (nextInstructionGas cfg c) = (charged, none))
    (hframe : chargeWasm (Exec.step charged)
      (frameTransitionGas cfg charged (Exec.step charged)) = (next, none))
    (hpays : Pays (.next c) credits next middle)
    (hnext : WP cfg fuel next middle post) :
    WP cfg (fuel + 1) (.next c) credits post := by
  have hrun : runMetered cfg (fuel + 1) (.next c) = runMetered cfg fuel next := by
    simp only [runMetered, hop, hframe]
  obtain ⟨_, remaining, htail, hpost⟩ := hnext
  exact ⟨hcredits, remaining, by simpa only [hrun] using hpays.trans htail,
    by simpa only [hrun] using hpost⟩

/-- Straight-line instructions only need their concrete interpreter equation
and the fact that they preserve gas. Instruction and activation charges are
handled by the rule, retaining all unused credits for the continuation. -/
theorem wp_pure_next {cfg : WasmConfig} {fuel : Nat} {c : Config NearState}
    {rest : Nat} {post : Post}
    (hcredits : c.store.host.gas.Credits (nextInstructionGas cfg c + rest))
    (hgas : (Exec.step (chargeConfig c (nextInstructionGas cfg c)).1).host.gas =
      (chargeConfig c (nextInstructionGas cfg c)).1.store.host.gas)
    (hframe : frameTransitionGas cfg (chargeConfig c (nextInstructionGas cfg c)).1
      (Exec.step (chargeConfig c (nextInstructionGas cfg c)).1) = 0)
    (hnext : WP cfg fuel (Exec.step (chargeConfig c (nextInstructionGas cfg c)).1) rest post) :
    WP cfg (fuel + 1) (.next c) (nextInstructionGas cfg c + rest) post := by
  have hcharge := Pays.chargeConfig c (nextInstructionGas cfg c) rest hcredits
  have hstep : Pays (.next (chargeConfig c (nextInstructionGas cfg c)).1) rest
      (Exec.step (chargeConfig c (nextInstructionGas cfg c)).1) rest :=
    Pays.of_gas_eq hgas hcharge.2.2.2.2
  apply wp_next hcredits (Prod.ext rfl hcharge.1) ?_ (hcharge.2.trans hstep) hnext
  rw [hframe]
  exact chargeWasm_zero _ (hnext.1.mono (Nat.zero_le rest))

/-- A rejected instruction charge stops before executing the instruction. -/
theorem wp_instruction_error {cfg : WasmConfig} {fuel : Nat} {c charged : Config NearState}
    {error : HostError} {credits remaining : Nat} {post : Post}
    (hop : chargeConfig c (nextInstructionGas cfg c) = (charged, some error))
    (hcredits : c.store.host.gas.Credits credits)
    (hpays : Pays (.next c) credits (.next charged) remaining)
    (hpost : post remaining (.next charged) (some (.hostError error))) :
    WP cfg (fuel + 1) (.next c) credits post := by
  exact wp_of_run (m := .next c) (fuel := fuel + 1)
    (by simp only [runMetered, hop]) hcredits hpays hpost

/-- A rejected activation charge retains the effects of the instruction. -/
theorem wp_frame_error {cfg : WasmConfig} {fuel : Nat} {c charged : Config NearState}
    {next : Machine} {error : HostError} {credits remaining : Nat} {post : Post}
    (hop : chargeConfig c (nextInstructionGas cfg c) = (charged, none))
    (hframe : chargeWasm (Exec.step charged)
      (frameTransitionGas cfg charged (Exec.step charged)) = (next, some error))
    (hcredits : c.store.host.gas.Credits credits)
    (hpays : Pays (.next c) credits next remaining)
    (hpost : post remaining next (some (.hostError error))) :
    WP cfg (fuel + 1) (.next c) credits post := by
  exact wp_of_run (m := .next c) (fuel := fuel + 1)
    (by simp only [runMetered, hop, hframe]) hcredits hpays hpost

end Wasm.Near.MeteredLogic
