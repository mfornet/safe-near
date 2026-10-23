import NearVM.HostGasFloor
import NearVM.ExecutionGas
import Wasm.Fuel
import Wasm.LinkFuncs

/-!
# Enough fuel

`runMetered` steps the machine at most `fuel` times and reports
`fuelExhausted` when it runs out: an interpreter limit, not a protocol
outcome. This file proves that a call given `fuelFor` steps never reaches it.

Instructions burn at least `minOpCost` gas each, so gas bounds how many run.
Steps that run no instruction are bounded by `Wasm.Fuel`: each strictly
decreases a measure that never exceeds `span` (call depth times the largest
function body). Host functions never lower burnt gas (`HostGasFloor`). So
`potential` (remaining gas in instructions, times `span + 1`, plus the
measure) strictly decreases with every step.
-/

namespace Wasm.Near

open Exec

/-! ## The code a resolved call can run -/

theorem HostEnv.allocate_wasm (store : Store α) (env : HostEnv α) {t : FuncType} {i : Nat} {f : Func}
    (h : FuncInst.wasm t i f ∈ (env.allocate store).1.funcs) : FuncInst.wasm t i f ∈ store.funcs := by
  unfold HostEnv.allocate at h
  suffices key : ∀ (init : Store α × List ExternVal) (fns : List (NearHostFn α)),
      FuncInst.wasm t i f ∈ (fns.foldl (fun (store, exts) fn =>
        let (store, addr) := store.allocFunc (.host fn.toHostFn)
        (store, exts ++ [.func addr])) init).1.funcs →
      FuncInst.wasm t i f ∈ init.1.funcs by
    exact key (store, []) env.funcs h
  intro init fns
  induction fns generalizing init with
  | nil => exact id
  | cons head tail ih =>
    intro h
    obtain ⟨st, exts⟩ := init
    simp only [List.foldl_cons] at h
    have hin := ih _ h
    simp only [Store.allocFunc, Array.mem_push] at hin
    rcases hin with hin | hin
    · exact hin
    · cases hin

theorem le_foldl_max (fs : List Func) (acc : Nat) :
    acc ≤ fs.foldl (fun acc f => max acc (codeSize f.body)) acc := by
  induction fs generalizing acc with
  | nil => exact Nat.le_refl _
  | cons f fs ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem le_moduleBody {m : Module} {f : Func} (h : f ∈ m.funcs.toList) : codeSize f.body ≤ moduleBody m := by
  unfold moduleBody
  rw [← Array.foldl_toList]
  generalize m.funcs.toList = fs at h
  suffices key : ∀ acc, codeSize f.body ≤ fs.foldl (fun acc f => max acc (codeSize f.body)) acc from
    key 0
  intro acc
  induction fs generalizing acc with
  | nil => simp at h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Nat.le_trans (Nat.le_max_right _ _) (le_foldl_max _ _)
    · exact ih h _

theorem maxBody_le {s : Store H} {B : Nat}
    (h : ∀ t i f, FuncInst.wasm t i f ∈ s.funcs → codeSize f.body ≤ B) : maxBody s ≤ B := by
  unfold maxBody
  rw [← Array.foldl_toList]
  have h' : ∀ fn ∈ s.funcs.toList, ∀ t i f, fn = FuncInst.wasm t i f → codeSize f.body ≤ B :=
    fun fn hfn t i f heq => h t i f (by rw [← heq]; exact Array.mem_toList_iff.mp hfn)
  generalize s.funcs.toList = fs at h'
  suffices key : ∀ acc ≤ B, fs.foldl (fun m fn => match fn with
      | .wasm _ _ code => max m (codeSize code.body)
      | .host _ => m) acc ≤ B from key 0 (Nat.zero_le _)
  intro acc hacc
  induction fs generalizing acc with
  | nil => exact hacc
  | cons fn fs ih =>
    simp only [List.foldl_cons]
    apply ih (fun g hg => h' g (by simp [hg]))
    cases fn with
    | wasm t i f => exact Nat.max_le.mpr ⟨hacc, h' _ (by simp) t i f rfl⟩
    | host _ => exact hacc

theorem validate_module {features : Features} {m : Module} {vm : ValidModule}
    (h : m.validate features = .ok vm) : vm.module = m := by
  unfold Module.validate at h
  cases hv : Validate.module features m with
  | error e => simp [hv, bind, Except.bind] at h
  | ok u => simp only [hv, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h; subst h; rfl

/-- A call into an instantiated module only ever runs the module's code. -/
theorem resolved_maxBody {env : HostEnv NearState} {host : NearState}
    {store store' : Store NearState} {imports : List ExternVal} {vm : ValidModule} {inst : ModuleInst}
    (halloc : env.allocate (Store.empty host) = (store, imports))
    (hinst : Link.instantiateModule store vm imports = .ok (store', inst)) :
    maxBody store' ≤ moduleBody vm.module := by
  apply maxBody_le
  intro t i f hmem
  rcases Link.instantiateModule_from store vm imports hinst _ hmem with hold | ⟨t', i', f', heq, hf⟩
  · have := HostEnv.allocate_wasm (Store.empty host) env (t := t) (i := i) (f := f)
    rw [halloc] at this
    have := this hold
    simp [Store.empty] at this
  · cases heq
    exact le_moduleBody hf

/-- Host functions that keep burnt gas at or above any floor. -/
def FloorHosts (store : Store NearState) : Prop :=
  StoreHosts (fun fn => ∀ b prepaid maxBurnt, HostFn.Preserves (GasFloor b prepaid maxBurnt) fn) store

theorem resolved_floorHosts {cfg : RuntimeConfig} {code : Module} {env : HostEnv NearState}
    {host : NearState} {store store' : Store NearState} {imports : List ExternVal} {vm : ValidModule}
    {inst : ModuleInst} (hresolve : resolveMetered cfg code = .ok env)
    (halloc : env.allocate (Store.empty host) = (store, imports))
    (hinst : Link.instantiateModule store vm imports = .ok (store', inst)) : FloorHosts store' := by
  intro fn hmem b prepaid maxBurnt
  have hold := (Link.instantiateModule_same store vm imports hinst).2 fn hmem
  have := HostEnv.allocate_funcs (Store.empty host) env fn
  rw [halloc] at this
  rcases this hold with hempty | ⟨nfn, hn, rfl⟩
  · simp [Store.empty] at hempty
  · exact (resolveMetered_gasFloor cfg code env hresolve nfn hn b prepaid maxBurnt).toHostFn

/-! ## One metered iteration -/

/-- An instruction is charged at least `minOpCost`; only block entries and
fall-throughs are free. -/
theorem nextInstructionGas_cases (cfg : WasmConfig) (c : Config NearState) :
    FreeStep c ∨ minOpCost cfg ≤ nextInstructionGas cfg c := by
  unfold nextInstructionGas FreeStep minOpCost
  split
  · rename_i h; exact Or.inl (Or.inl h)
  · rename_i bt body h; exact Or.inl (Or.inr ⟨bt, body, h⟩)
  · right
    split
    · exact Nat.le_trans (Nat.min_le_right _ _) (Nat.le_add_right _ _)
    · exact Nat.le_trans (Nat.min_le_left _ _) (Nat.le_add_right _ _)

@[simp] theorem chargeConfig_thread (c : Config NearState) (cost : Nat) :
    (chargeConfig c cost).1.thread = c.thread := rfl

@[simp] theorem chargeConfig_limits (c : Config NearState) (cost : Nat) :
    (chargeConfig c cost).1.limits = c.limits := rfl

@[simp] theorem chargeConfig_funcs (c : Config NearState) (cost : Nat) :
    (chargeConfig c cost).1.store.funcs = c.store.funcs := rfl

theorem chargeConfig_bounded {c : Config NearState} (cost : Nat) (h : Bounded c) :
    Bounded (chargeConfig c cost).1 :=
  ⟨by rw [maxBody_congr (chargeConfig_funcs c cost)]; exact h.fits, h.depth⟩

theorem chargeConfig_floor {b prepaid maxBurnt : Nat} {c : Config NearState} (cost : Nat)
    (h : GasFloor b prepaid maxBurnt c.store.host) :
    GasFloor b prepaid maxBurnt (chargeConfig c cost).1.store.host :=
  GasCounter.deduct_floor cost cost h

theorem chargeConfig_burnt {c : Config NearState} {cost : Nat} (h : (chargeConfig c cost).2 = none) :
    (chargeConfig c cost).1.store.host.gas.burnt = c.store.host.gas.burnt + cost :=
  (GasCounter.deduct_success _ cost cost (Nat.le_refl _) h).1

/-! ## The potential -/

/-- How far a configuration of this run can be from executing an instruction. -/
def span (c : Config NearState) : Nat := max 1 c.limits.maxCallDepth * (maxBody c.store + 1)

/-- Remaining gas, counted in cheapest instructions, weighted by `span + 1`,
plus the distance to the next instruction. -/
def potential (cfg : WasmConfig) (maxBurnt : Nat) (c : Config NearState) : Nat :=
  (maxBurnt - c.store.host.gas.burnt) / minOpCost cfg * (span c + 1) + c.measure

/-- What every configuration of a metered run satisfies. -/
structure FuelInv (prepaid maxBurnt : Nat) (c : Config NearState) : Prop where
  bounded : Bounded c
  hosts : FloorHosts c.store
  floor : GasFloor 0 prepaid maxBurnt c.store.host

theorem step_floor {b prepaid maxBurnt : Nat} {c c' : Config NearState} (hh : FloorHosts c.store)
    (hf : GasFloor b prepaid maxBurnt c.store.host) (hs : Exec.step c = .next c') :
    GasFloor b prepaid maxBurnt c'.store.host ∧ FloorHosts c'.store := by
  refine ⟨(step_preserves_hostInvariant (P := GasFloor b prepaid maxBurnt)
    ⟨fun fn hm => hh fn hm b prepaid maxBurnt, hf⟩ hs).2, ?_⟩
  intro fn hm
  exact hh fn (by rw [← step_store_funcs hs]; exact hm)

theorem GasFloor.weaken {b b' prepaid maxBurnt : Nat} {ns : NearState} (h : GasFloor b prepaid maxBurnt ns)
    (hb : b' ≤ b) : GasFloor b' prepaid maxBurnt ns :=
  ⟨Nat.le_trans hb h.1, h.2⟩

theorem GasFloor.self {prepaid maxBurnt : Nat} {ns : NearState} (h : GasFloor 0 prepaid maxBurnt ns) :
    GasFloor ns.gas.burnt prepaid maxBurnt ns :=
  ⟨Nat.le_refl _, h.2⟩

/-- One iteration of the metered loop that continues: the invariant holds
after it and the potential strictly decreased. -/
theorem iteration {cfg : WasmConfig} (hpos : 0 < minOpCost cfg) {prepaid maxBurnt : Nat}
    {c c' : Config NearState} (cost : Nat) (hinv : FuelInv prepaid maxBurnt c)
    (hcharge : (chargeConfig c (nextInstructionGas cfg c)).2 = none)
    (hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 = .next c') :
    FuelInv prepaid maxBurnt (chargeConfig c' cost).1 ∧
      potential cfg maxBurnt (chargeConfig c' cost).1 < potential cfg maxBurnt c := by
  set k := nextInstructionGas cfg c with hk
  set c1 := (chargeConfig c k).1 with hc1
  set c3 := (chargeConfig c' cost).1 with hc3
  have hB1 : c1.store.host.gas.burnt = c.store.host.gas.burnt + k := chargeConfig_burnt hcharge
  have hf1 : GasFloor c1.store.host.gas.burnt prepaid maxBurnt c1.store.host :=
    (chargeConfig_floor k hinv.floor).self
  have hh1 : FloorHosts c1.store := fun fn hm => hinv.hosts fn hm
  obtain ⟨hf2, hh2⟩ := step_floor hh1 hf1 hstep
  have hf3 : GasFloor c1.store.host.gas.burnt prepaid maxBurnt c3.store.host :=
    chargeConfig_floor cost hf2
  have hb3 : Bounded c3 :=
    chargeConfig_bounded cost (step_bounded hstep (chargeConfig_bounded k hinv.bounded))
  have hinv3 : FuelInv prepaid maxBurnt c3 :=
    ⟨hb3, fun fn hm => hh2 fn hm, hf3.weaken (Nat.zero_le _)⟩
  refine ⟨hinv3, ?_⟩
  have hspan : span c3 = span c := by
    unfold span
    rw [show c3.limits = c.limits from (step_limits _ hstep).trans rfl,
      show maxBody c3.store = maxBody c.store from
        maxBody_congr ((step_store_funcs hstep).trans rfl)]
  have hmeasure3 : c3.measure = c'.measure := rfl
  -- Gas: `c3` burnt at least `c`'s plus `k`, within `maxBurnt`.
  have hle3 : c.store.host.gas.burnt + k ≤ c3.store.host.gas.burnt := hB1 ▸ hf3.1
  have hmax3 : c3.store.host.gas.burnt ≤ maxBurnt := hf3.2.1
  have hq : (maxBurnt - c3.store.host.gas.burnt) / minOpCost cfg ≤
      (maxBurnt - c.store.host.gas.burnt) / minOpCost cfg :=
    Nat.div_le_div_right (by omega)
  unfold potential
  rw [hspan, hmeasure3]
  rcases nextInstructionGas_cases cfg c with hfree | hcharged
  · have hdec : c'.measure < c1.measure :=
      step_free_decreases hstep (by unfold FreeStep at hfree ⊢; exact hfree)
    have : c1.measure = c.measure := rfl
    have := Nat.mul_le_mul_right (span c + 1) hq
    omega
  · have hk' : minOpCost cfg ≤ k := hcharged
    have hgap : k ≤ maxBurnt - c.store.host.gas.burnt := by omega
    have hq' : (maxBurnt - c3.store.host.gas.burnt) / minOpCost cfg + 1 ≤
        (maxBurnt - c.store.host.gas.burnt) / minOpCost cfg := by
      have hsub : maxBurnt - c3.store.host.gas.burnt ≤
          (maxBurnt - c.store.host.gas.burnt) - minOpCost cfg := by omega
      rw [Nat.div_eq_sub_div hpos (by omega : minOpCost cfg ≤ maxBurnt - c.store.host.gas.burnt)]
      exact Nat.add_le_add_right (Nat.div_le_div_right hsub) 1
    have hmeas : c'.measure ≤ span c := by
      have := hb3.measure_le
      rw [← hspan]
      exact this
    have := Nat.mul_le_mul_right (span c + 1) hq'
    rw [Nat.add_mul, Nat.one_mul] at this
    omega

/-- With more fuel than the potential, the metered loop never runs out. -/
theorem runMetered_enough_fuel {cfg : WasmConfig} (hpos : 0 < minOpCost cfg) (fuel : Nat)
    {c : Config NearState} {prepaid maxBurnt : Nat} (hinv : FuelInv prepaid maxBurnt c)
    (hfuel : potential cfg maxBurnt c < fuel) :
    (runMetered cfg fuel (.next c)).2 ≠ some (.executionIssue .fuelExhausted) := by
  induction fuel generalizing c with
  | zero => omega
  | succ fuel ih =>
    simp only [runMetered]
    split
    · simp
    · rename_i hcharge
      cases hnext : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 with
      | next c' =>
        obtain ⟨hinv', hdec⟩ := iteration hpos
          (frameTransitionGas cfg (chargeConfig c (nextInstructionGas cfg c)).1 (.next c')) hinv
          hcharge hnext
        simp only [chargeWasm]
        split
        · simp
        · exact ih hinv' (by omega)
      | done values store =>
        simp only [chargeWasm]
        split
        · simp
        · rw [runMetered_done]; simp
      | trap reason store =>
        simp only [chargeWasm]
        split
        · simp
        · rw [runMetered_trapped]; simp

/-- A run that did not exhaust its fuel is the same with more. -/
theorem runMetered_extra_fuel (cfg : WasmConfig) (fuel : Nat) (m : Machine)
    (h : (runMetered cfg fuel m).2 ≠ some (.executionIssue .fuelExhausted)) (n : Nat) :
    runMetered cfg (fuel + n) m = runMetered cfg fuel m := by
  induction fuel generalizing m with
  | zero =>
    cases m with
    | next c => exact absurd rfl h
    | done values store => rw [runMetered_done, runMetered_done]
    | trap reason store => rw [runMetered_trapped, runMetered_trapped]
  | succ fuel ih =>
    cases m with
    | done values store => rw [runMetered_done, runMetered_done]
    | trap reason store => rw [runMetered_trapped, runMetered_trapped]
    | next c =>
      rw [show fuel + 1 + n = (fuel + n) + 1 by omega]
      simp only [runMetered] at h ⊢
      split
      · rfl
      · rename_i hcharge
        rw [hcharge] at h
        dsimp only at h ⊢
        split
        · rfl
        · rename_i hcharge'
          rw [hcharge'] at h
          exact ih _ h

/-! ## A whole call -/

theorem startWasm_bounded {store : Store H} {limits : ExecLimits} {addr : Nat} {args : List Value}
    {c : Config H} (h : Exec.startWasm store limits addr args = some c) : Bounded c := by
  unfold Exec.startWasm at h
  split at h
  · rename_i type inst code heq
    cases h
    refine ⟨?_, by simp only [List.length_singleton]; exact Nat.le_max_left _ _⟩
    intro f hf
    simp only [List.mem_singleton] at hf
    subst hf
    exact ⟨by simpa [CallFrame.measure, labelsWeight] using le_maxBody heq, trivial⟩
  · cases h

theorem runInitialized_enough_fuel {cfg : WasmConfig} (hpos : 0 < minOpCost cfg) {c : Config NearState}
    {prepaid maxBurnt : Nat} (hinv : FuelInv prepaid maxBurnt c) {fuel : Nat}
    (hfuel : (maxBurnt / minOpCost cfg + 1) * (span c + 1) ≤ fuel) :
    (runInitialized cfg fuel (.next c)).2 ≠ some (.executionIssue .fuelExhausted) := by
  unfold runInitialized
  dsimp only [chargeWasm]
  split
  · simp
  · set e := entryCost cfg (.next c)
    have hinv' : FuelInv prepaid maxBurnt (chargeConfig c e).1 :=
      ⟨chargeConfig_bounded e hinv.bounded, fun fn hm => hinv.hosts fn hm, chargeConfig_floor e hinv.floor⟩
    apply runMetered_enough_fuel hpos fuel hinv'
    have hspan : span (chargeConfig c e).1 = span c := rfl
    have hmeas := hinv'.bounded.measure_le
    have hq : (maxBurnt - (chargeConfig c e).1.store.host.gas.burnt) / minOpCost cfg ≤
        maxBurnt / minOpCost cfg := Nat.div_le_div_right (Nat.sub_le _ _)
    unfold potential
    rw [hspan]
    have := Nat.mul_le_mul_right (span c + 1) hq
    have : (chargeConfig c e).1.measure ≤ span c := hmeas
    rw [Nat.add_mul, Nat.one_mul] at hfuel
    omega

theorem runInitialized_extra_fuel (cfg : WasmConfig) (fuel : Nat) (m : Machine)
    (h : (runInitialized cfg fuel m).2 ≠ some (.executionIssue .fuelExhausted)) (n : Nat) :
    runInitialized cfg (fuel + n) m = runInitialized cfg fuel m := by
  unfold runInitialized at h ⊢
  dsimp only at h ⊢
  split
  · rfl
  · rename_i hcharge
    rw [hcharge] at h
    exact runMetered_extra_fuel cfg fuel _ h n

/-- With at least `fuelFor`, a call's outcome does not depend on fuel: the
interpreter never stops it for want of steps. -/
theorem runAttempt_fuel_independent (cfg : RuntimeConfig) (code : Module) (codeSize : Nat)
    (method : String) (ctx : VMContext) (storage : List (List UInt8 × List UInt8))
    (hpos : 0 < minOpCost cfg.wasm) {fuel : Nat} (hfuel : fuelFor cfg code ctx ≤ fuel) (n : Nat) :
    runAttempt cfg code codeSize method ctx storage (fuel + n) =
      runAttempt cfg code codeSize method ctx storage fuel := by
  unfold runAttempt
  dsimp only
  repeat' (first | rfl | split)
  rename_i _ _ hload _ valid hvalid _ _ entry _ _ sig _ _ _ env hresolve _ store inst hinst _ c hstart
  set host1 := (applyCharges (VMContext.toNearState cfg ctx storage) (loadingCharges codeSize)).1
  have halloc : env.allocate (Store.empty host1) =
      ((env.allocate (Store.empty host1)).1, (env.allocate (Store.empty host1)).2) := rfl
  have hfloor0 : GasFloor 0 ctx.prepaidGas (ctx.maxBurnt cfg) (VMContext.toNearState cfg ctx storage) := by
    refine ⟨Nat.zero_le _, Nat.zero_le _, Nat.zero_le _, rfl, ?_⟩
    unfold VMContext.toNearState VMContext.maxBurnt
    cases ctx.viewConfig <;> rfl
  have hhost : c.store.host = host1 := resolvedStart_gas halloc hinst hstart
  have hcstore : c.store = store := Exec.startWasm_store hstart
  have hinv : FuelInv ctx.prepaidGas (ctx.maxBurnt cfg) c := by
    refine ⟨startWasm_bounded hstart, ?_, ?_⟩
    · rw [hcstore]; exact resolved_floorHosts hresolve halloc hinst
    · rw [hhost]; exact applyCharges_floor _ _ hfloor0
  have hlimits : c.limits = execLimits := by
    unfold Exec.startWasm at hstart
    split at hstart
    · cases hstart; rfl
    · cases hstart
  have hspan : span c ≤ max 1 execLimits.maxCallDepth * (moduleBody code + 1) := by
    unfold span
    rw [hlimits, hcstore]
    have hb := resolved_maxBody halloc hinst
    rw [validate_module hvalid] at hb
    exact Nat.mul_le_mul_left _ (Nat.add_le_add_right hb 1)
  have hfuel' : (ctx.maxBurnt cfg / minOpCost cfg.wasm + 1) * (span c + 1) ≤ fuel :=
    Nat.le_trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right hspan 1)) hfuel
  rw [runInitialized_extra_fuel cfg.wasm fuel _ (runInitialized_enough_fuel hpos hinv hfuel') n]

/-- `run` defaults to `fuelFor`, and more fuel never changes its outcome: no
call stops for want of interpreter steps. -/
theorem run_fuel_independent (cfg : RuntimeConfig) (code : Module) (codeSize : Nat)
    (method : String) (ctx : VMContext) (storage : List (List UInt8 × List UInt8))
    (hpos : 0 < minOpCost cfg.wasm) (n : Nat) :
    run cfg code codeSize method ctx storage (fuelFor cfg code ctx + n) =
      run cfg code codeSize method ctx storage := by
  unfold run
  rw [runAttempt_fuel_independent cfg code codeSize method ctx storage hpos (Nat.le_refl _) n]

end Wasm.Near
