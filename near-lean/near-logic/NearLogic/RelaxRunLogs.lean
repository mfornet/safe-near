import NearLogic.RelaxRun
import NearLogic.Hosts.RelaxLogs
import NearVM.MeteredLiveInvariant

/-!
# Runs under raised gas limits, with logs

`runMetered_relax` with its gas case strengthened: when the lower run ends
with a failed charge, its final host keeps the execution issue it started
with, and its logs are a prefix of the raised run's final logs. This is the
out-of-gas clause of `Refines` for a contract that logs.
-/

namespace NearLogic

open Wasm Wasm.Near

/-- A host function respects raised limits, and its failed charges keep
the issue and log no more than the raised call. -/
def RelaxFnL (fn : HostFn NearState) : Prop :=
  ∀ host mem args p m, host.gas.prepaid ≤ p → host.gas.maxBurnt ≤ m →
    (∃ r h mem' e, fn.call host mem args = .trap r h mem' ∧ h.lastError = some e ∧ isGasError e ∧
      h.lastExecutionIssue = host.lastExecutionIssue ∧ h.logs <+: (fn.call (relax host p m) mem args).host.logs) ∨
    fn.call (relax host p m) mem args = (fn.call host mem args).relax p m

theorem toHostFn_call_host (fn : NearHostFn NearState) (host : NearState) (mem : Option Memory)
    (args : List Value) :
    (fn.toHostFn.call host mem args).host = resHost (fn.invoke { mem := mem.getD (Memory.new 0 none), host } args) := by
  simp only [NearHostFn.toHostFn]
  cases fn.invoke { mem := mem.getD (Memory.new 0 none), host } args <;> rfl

theorem relaxFnL_metered (extra : Nat) {name : String} (hn : name ∈ gasNames) (fn : NearHostFn NearState)
    (hinv : InvokeRelaxL extra name fn) (hmono : FnMono fn) : RelaxFnL (metered extra name fn).toHostFn := by
  intro host mem args p m hp hm
  rcases metered_relaxL extra name fn (fun st args p m => chargesBefore_relax hn st args p m)
    (fun st args p m => preInvokeError_relax hn st args p m) hinv hmono
    { mem := mem.getD (Memory.new 0 none), host } args p m hp hm with ⟨st', e, hinv', he, hi, hl⟩ | hrel
  · left
    refine ⟨.host e.message, { st'.host with lastError := some e }, some st'.mem, e, ?_, rfl, he, hi, ?_⟩
    · simp only [NearHostFn.toHostFn, hinv', trapWith]
    · rw [toHostFn_call_host]
      exact hl
  · right
    simp only [NearHostFn.toHostFn]
    have : ({ mem := mem.getD (Memory.new 0 none), host := relax host p m } : HostStore NearState) =
        relaxSt { mem := mem.getD (Memory.new 0 none), host } p m := rfl
    rw [this, hrel]
    cases (metered extra name fn).invoke { mem := mem.getD (Memory.new 0 none), host } args <;> rfl

/-- Every host function of the store respects raised limits, with logs. -/
def StoreRelaxFnsL (σ : Store NearState) : Prop :=
  ∀ (a : Nat) (fn : HostFn NearState), σ.funcs[a]? = some (FuncInst.host fn) → RelaxFnL fn

/-- A failed charge in a step: a trap recording a gas error, keeping the
issue, with no more logs than the raised step. -/
def GasStepL (c : Config NearState) (p m : Nat) (r r' : StepResult NearState) : Prop :=
  ∃ reason s e, r = .trap reason s ∧ s.host.lastError = some e ∧ isGasError e ∧
    s.host.lastExecutionIssue = c.store.host.lastExecutionIssue ∧ s.host.logs <+: r'.store.host.logs

theorem enter_relaxL (c : Config NearState) (stack : Array Value) (frames : List CallFrame) (addr : Nat)
    (p m : Nat) (hp : c.store.host.gas.prepaid ≤ p) (hm : c.store.host.gas.maxBurnt ≤ m)
    (hf : StoreRelaxFnsL c.store) :
    GasStepL c p m (Exec.enter c stack frames addr)
        (Exec.enter { c with store := relaxStore c.store p m } stack frames addr) ∨
      Exec.enter { c with store := relaxStore c.store p m } stack frames addr =
        (Exec.enter c stack frames addr).relax p m := by
  unfold Exec.enter
  dsimp only
  cases hfn : c.store.funcs[addr]? with
  | none => right; simp only [relaxStore, hfn]; rfl
  | some f =>
    have hfn' : (relaxStore c.store p m).funcs[addr]? = some f := hfn
    rw [hfn']
    cases f with
    | wasm type inst code => right; simp only [relaxStore]; split <;> rfl
    | host fn =>
      simp only
      have hmemOf : (relaxStore c.store p m).memOf = c.store.memOf := rfl
      have hmods : (relaxStore c.store p m).modules = c.store.modules := rfl
      have hhost : (relaxStore c.store p m).host = relax c.store.host p m := rfl
      simp only [hmemOf, hmods, hhost]
      rcases hf addr fn hfn c.store.host _ _ p m hp hm with ⟨r, h, mem, e, hcall, hl, he, hi, hlog⟩ | hrel
      · left
        rw [hcall]
        refine ⟨r, _, e, rfl, by rw [Exec.commitHost_host]; exact hl, he, by rw [Exec.commitHost_host]; exact hi, ?_⟩
        rw [Exec.commitHost_host]
        revert hlog
        cases fn.call (relax c.store.host p m) _ _ with
        | «return» values host' mem' =>
          intro hlog
          simp only
          split <;> simp only [StepResult.store, Exec.commitHost_host] <;> exact hlog
        | trap reason host' mem' =>
          intro hlog
          simp only [StepResult.store, Exec.commitHost_host]
          exact hlog
      · right
        rw [hrel]
        cases fn.call c.store.host _ _ with
        | «return» values host mem' =>
          simp only [HostOutcome.relax]
          rw [commitHost_relaxStore]
          split <;> rfl
        | trap reason host mem' =>
          simp only [HostOutcome.relax]
          rw [commitHost_relaxStore]
          rfl

/-- One step under raised limits, with logs. -/
theorem step_relaxL (c : Config NearState) (p m : Nat) (hp : c.store.host.gas.prepaid ≤ p)
    (hm : c.store.host.gas.maxBurnt ≤ m) (hf : StoreRelaxFnsL c.store) :
    GasStepL c p m (Exec.step c) (Exec.step { c with store := relaxStore c.store p m }) ∨
      Exec.step { c with store := relaxStore c.store p m } = (Exec.step c).relax p m := by
  obtain ⟨σ, ⟨stack, frames⟩, lim⟩ := c
  cases frames with
  | nil => right; rfl
  | cons frame frames =>
    simp only [Exec.step]
    split
    · right
      rw [Exec.leave_congr (c' := ⟨σ, ⟨stack, frame :: frames⟩, lim⟩) rfl]
      exact leave_relax _ σ stack frame frames p m
    · right; rfl
    · rename_i _ i rest _
      have hmods : (relaxStore σ p m).modules = σ.modules := rfl
      rw [hmods, show relaxStore σ p m = { σ with host := relax σ.host p m } from rfl,
        instr_withHost σ (relax σ.host p m) σ.modules[frame.inst]! frame.locals stack frame.labels i rest]
      obtain ⟨hsh, hsf⟩ := Exec.instr_store σ σ.modules[frame.inst]! frame.locals stack frame.labels i rest
      generalize Exec.instr σ σ.modules[frame.inst]! frame.locals stack frame.labels i rest = eff at hsh hsf ⊢
      obtain ⟨st, kind⟩ := eff
      simp only at hsh hsf
      have hst : ({ st with host := relax σ.host p m } : Store NearState) = relaxStore st p m := by
        rw [← hsh]; rfl
      cases kind with
      | «continue» stack' labels' code' locals' =>
        right; simp only [Exec.Effect.withHost, hst]; rfl
      | call stack' addr rest' =>
        simp only [Exec.Effect.withHost, hst]
        have := enter_relaxL { store := st, thread := { stack := stack, frames := frame :: frames }, limits := lim }
          stack' ({ frame with code := rest' } :: frames) addr p m (by rw [hsh]; exact hp) (by rw [hsh]; exact hm)
          (fun a fn h => hf a fn (by rw [← hsf]; exact h))
        rcases this with ⟨reason, s, e, h1, h2, h3, h4, h5⟩ | h
        · left
          exact ⟨reason, s, e, h1, h2, h3, by rw [h4]; simp only; rw [hsh], h5⟩
        · exact Or.inr h
      | «return» stack' =>
        right; simp only [Exec.Effect.withHost, hst]
        rw [Exec.leave_congr (c' := ⟨σ, ⟨stack, frame :: frames⟩, lim⟩) rfl]
        exact leave_relax _ st stack' frame frames p m
      | trap reason =>
        right; simp only [Exec.Effect.withHost, hst]; rfl

/-! ## Runs -/

/-- Every host function of the store only grows the logs. -/
def StoreLogsMono (σ : Store NearState) : Prop :=
  Exec.StoreHosts (fun fn => ∀ L, Exec.HostFn.Preserves (fun h => L <+: h.logs) fn) σ

theorem stepResult_host (r : StepResult NearState) : r.host = r.store.host := by cases r <;> rfl

theorem chargeWasm_logs (r : Machine) (k : Nat) :
    (chargeWasm r k).1.host.logs = r.host.logs ∧
      (chargeWasm r k).1.host.lastExecutionIssue = r.host.lastExecutionIssue := by
  cases r <;> exact ⟨rfl, rfl⟩

/-- Along a run, the logs only grow. -/
theorem runMetered_logs (cfg : WasmConfig) (fuel : Nat) (r : Machine) (h : StoreLogsMono r.store) :
    r.host.logs <+: (runMetered cfg fuel r).1.host.logs := by
  have hinv : MachineHostInvariant (fun x => r.host.logs <+: x.logs) r :=
    MachineHostInvariant.of_parts (fun fn hm => h fn hm _) (List.prefix_refl _)
  exact (runMetered_hostInvariant _ (fun ns cost hp => hp) cfg fuel r hinv).host

theorem storeLogsMono_relax (r : Machine) (p m : Nat) (h : StoreLogsMono r.store) :
    StoreLogsMono (r.relax p m).store := by
  cases r <;> exact h

/-- After a successful instruction charge, the run's final logs extend its step's. -/
theorem runMetered_succ_logs (cfg : WasmConfig) (fuel : Nat) (c : Config NearState) (hmono : StoreLogsMono c.store)
    (h1 : (chargeConfig c (nextInstructionGas cfg c)).2 = none) :
    (Exec.step (chargeConfig c (nextInstructionGas cfg c)).1).store.host.logs <+:
      (runMetered cfg (fuel + 1) (.next c)).1.host.logs := by
  generalize hc1 : (chargeConfig c (nextInstructionGas cfg c)).1 = c1
  have hm1 : StoreLogsMono (Exec.step c1).store := fun fn h =>
    hmono fn (by rw [← hc1, step_funcs_eq] at h; exact h)
  simp only [runMetered, h1, hc1]
  have hw := chargeWasm_logs (Exec.step c1) (frameTransitionGas cfg c1 (Exec.step c1))
  split
  · rw [hw.1, stepResult_host]; exact List.prefix_refl _
  · have := runMetered_logs cfg fuel (chargeWasm (Exec.step c1) (frameTransitionGas cfg c1 (Exec.step c1))).1
      (by cases hs : Exec.step c1 <;> rw [hs] at hm1 <;> exact hm1)
    rw [hw.1, stepResult_host] at this
    exact this

/-- After a successful instruction charge, a trapping step never ends the run normally. -/
theorem runMetered_succ_trap (cfg : WasmConfig) (fuel : Nat) (c : Config NearState)
    (h1 : (chargeConfig c (nextInstructionGas cfg c)).2 = none) {reason : Trap} {s : Store NearState}
    (hs : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 = .trap reason s) :
    ¬ ∃ vs s', (runMetered cfg (fuel + 1) (.next c)).1 = .done vs s' := by
  simp only [runMetered, h1, hs]
  split
  · simp [chargeWasm]
  · rename_i h2
    rw [show (chargeWasm (StepResult.trap reason s) _).1 = .trap reason _ from rfl, runMetered_trapped]
    simp

/-- A step that traps ends the run in a trap whose host keeps the step's execution issue. -/
theorem runMetered_succ_trap_issue (cfg : WasmConfig) (fuel : Nat) (c : Config NearState)
    (h1 : (chargeConfig c (nextInstructionGas cfg c)).2 = none) {reason : Trap} {s : Store NearState}
    (hs : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 = .trap reason s) :
    ∃ s', (runMetered cfg (fuel + 1) (.next c)).1 = .trap reason s' ∧
      s'.host.lastExecutionIssue = s.host.lastExecutionIssue := by
  simp only [runMetered, h1, hs]
  split
  · exact ⟨_, rfl, (chargeWasm_logs (.trap reason s) _).2⟩
  · rw [show (chargeWasm (StepResult.trap reason s) _).1 = .trap reason _ from rfl, runMetered_trapped]
    exact ⟨_, rfl, (chargeWasm_logs (.trap reason s) _).2⟩

/-- **Runs under raised limits, with logs.** The run with raised limits ends
as the lower run, up to the limits; or the lower run ends with a gas
failure whose logs are a prefix of the raised run's, and which keeps the
execution issue `I` the run started with when the raised run ends normally. -/
theorem runMetered_relaxL (cfg : WasmConfig) (p0 m0 p m : Nat) (hp : p0 ≤ p) (hm : m0 ≤ m)
    (I : Option ExecutionIssue) (fuel : Nat) :
    ∀ (r : Machine), MachineHostInvariant (GasLimits p0 m0) r → StoreRelaxFnsL r.store → StoreLogsMono r.store →
      MachineLiveInvariant (fun h => h.lastExecutionIssue = I) r →
      (GasEnd (runMetered cfg fuel r) ∧
          (runMetered cfg fuel r).1.host.logs <+: (runMetered cfg fuel (r.relax p m)).1.host.logs ∧
          ((∃ vs s, (runMetered cfg fuel (r.relax p m)).1 = .done vs s) →
            (runMetered cfg fuel r).1.host.lastExecutionIssue = I) ∧
          (∀ rs ss, (runMetered cfg fuel (r.relax p m)).1 = .trap rs ss → ss.host.lastExecutionIssue = I →
            (runMetered cfg fuel r).1.host.lastExecutionIssue = I)) ∨
        runMetered cfg fuel (r.relax p m) = ((runMetered cfg fuel r).1.relax p m, (runMetered cfg fuel r).2) := by
  have hcharge : ∀ (ns : NearState) (cost : Nat), GasLimits p0 m0 ns → GasLimits p0 m0 (chargeHost ns cost).1 :=
    fun ns cost h => by
      have hl := chargeHost_gas_limits ns cost
      exact ⟨hl.1.trans h.1, hl.2.trans h.2⟩
  induction fuel with
  | zero =>
    intro r _ _ _ _
    right
    cases r <;> rfl
  | succ fuel ih =>
    intro r hinv hf hmono hlive
    cases r with
    | done vs s => right; rfl
    | trap reason s => right; rfl
    | next c =>
      have hlim : c.store.host.gas.prepaid ≤ p ∧ c.store.host.gas.maxBurnt ≤ m := by
        have := hinv.2; exact ⟨this.1 ▸ hp, this.2 ▸ hm⟩
      have hk : nextInstructionGas cfg { c with store := relaxStore c.store p m } = nextInstructionGas cfg c := rfl
      have hmr : StoreLogsMono { c with store := relaxStore c.store p m }.store := hmono
      cases h1 : (chargeConfig c (nextInstructionGas cfg c)).2 with
      | some e =>
        left
        have hR := runMetered_logs cfg (fuel + 1) ((StepResult.next c).relax p m) hmr
        unfold runMetered
        simp only [h1]
        exact ⟨Or.inl ⟨e, rfl, chargeHost_error _ _ h1⟩, hR, fun _ => hlive.2, fun _ _ _ _ => hlive.2⟩
      | none =>
        have h1r : (chargeConfig { c with store := relaxStore c.store p m }
            (nextInstructionGas cfg { c with store := relaxStore c.store p m })).2 = none := by
          rw [hk, chargeConfig_relax c _ p m hlim.1 hlim.2 h1]
        have hc1r : (chargeConfig { c with store := relaxStore c.store p m }
            (nextInstructionGas cfg { c with store := relaxStore c.store p m })).1 =
            { (chargeConfig c (nextInstructionGas cfg c)).1 with
              store := relaxStore (chargeConfig c (nextInstructionGas cfg c)).1.store p m } := by
          rw [hk, chargeConfig_relax c _ p m hlim.1 hlim.2 h1]
        have hRstep := runMetered_succ_logs cfg fuel _ hmr h1r
        have hRtrap := fun {reason} {s} (h : Exec.step _ = StepResult.trap reason s) =>
          runMetered_succ_trap cfg fuel { c with store := relaxStore c.store p m } h1r (reason := reason) (s := s) h
        have hRtrapI := fun {reason} {s} (h : Exec.step _ = StepResult.trap reason s) =>
          runMetered_succ_trap_issue cfg fuel { c with store := relaxStore c.store p m } h1r (reason := reason) (s := s) h
        rw [hc1r, show (StepResult.next { c with store := relaxStore c.store p m }) = (StepResult.next c).relax p m
          from rfl] at hRstep hRtrap hRtrapI
        generalize hRR : runMetered cfg (fuel + 1) ((StepResult.next c).relax p m) = RR at hRstep hRtrap hRtrapI ⊢
        set c1 := (chargeConfig c (nextInstructionGas cfg c)).1 with hc1
        have hinv1 : Exec.ConfigHostInvariant (GasLimits p0 m0) c1 := chargeConfig_hostInvariant hcharge c _ hinv
        have hlive1 : Exec.ConfigLiveInvariant (fun h => h.lastExecutionIssue = I) c1 := ⟨hlive.1, hlive.2⟩
        have hlim1 : c1.store.host.gas.prepaid ≤ p ∧ c1.store.host.gas.maxBurnt ≤ m := by
          have := hinv1.2; exact ⟨this.1 ▸ hp, this.2 ▸ hm⟩
        have hf1 : StoreRelaxFnsL c1.store := fun a fn h => hf a fn h
        have hm1 : StoreLogsMono c1.store := hmono
        have hinvs : MachineHostInvariant (GasLimits p0 m0) (Exec.step c1) := Wasm.step_hostInvariant hinv1
        have hlives : MachineLiveInvariant (fun h => h.lastExecutionIssue = I) (Exec.step c1) :=
          step_liveInvariant hlive1
        have hfs : StoreRelaxFnsL (Exec.step c1).store := fun a fn h =>
          hf1 a fn (by rw [← step_funcs_eq c1]; exact h)
        have hms : StoreLogsMono (Exec.step c1).store := fun fn h =>
          hm1 fn (by rw [← step_funcs_eq c1]; exact h)
        rcases step_relaxL c1 p m hlim1.1 hlim1.2 hf1 with ⟨reason, s, e, hst, hle, hge, hiss, hlog⟩ | hst
        · left
          unfold runMetered
          simp only [h1, ← hc1]
          rw [hst]
          have hr := chargeWasm_logs (StepResult.trap reason s) (frameTransitionGas cfg c1 (.trap reason s))
          have hfin : s.host.logs <+: RR.1.host.logs := hlog.trans hRstep
          have hiss' : s.host.lastExecutionIssue = I := hiss.trans hlive1.2
          cases h2 : (chargeWasm (StepResult.trap reason s) (frameTransitionGas cfg c1 (.trap reason s))).2 with
          | some e' =>
            simp only [h2]
            refine ⟨Or.inl ⟨e', rfl, chargeWasm_error _ _ h2⟩, ?_, fun _ => ?_, fun _ _ _ _ => ?_⟩
            · rw [hr.1]; exact hfin
            · rw [hr.2]; exact hiss'
            · rw [hr.2]; exact hiss'
          | none =>
            simp only [h2]
            have hgs : GasStep (chargeWasm (StepResult.trap reason s) (frameTransitionGas cfg c1 (.trap reason s))).1 :=
              gasStep_chargeWasm _ ⟨reason, s, e, rfl, hle, hge⟩
            rw [runMetered_gasStep cfg fuel hgs]
            refine ⟨Or.inr ⟨rfl, hgs⟩, ?_, fun _ => ?_, fun _ _ _ _ => ?_⟩
            · rw [hr.1]; exact hfin
            · rw [hr.2]; exact hiss'
            · rw [hr.2]; exact hiss'
        · cases h2 : (chargeWasm (Exec.step c1) (frameTransitionGas cfg c1 (Exec.step c1))).2 with
          | some e =>
            left
            unfold runMetered
            simp only [h1, ← hc1, h2]
            have hw := chargeWasm_logs (Exec.step c1) (frameTransitionGas cfg c1 (Exec.step c1))
            rw [hst] at hRstep hRtrap hRtrapI
            refine ⟨Or.inl ⟨e, rfl, chargeWasm_error _ _ h2⟩, ?_, fun hdone => ?_, fun rs ss htr hss => ?_⟩
            · rw [hw.1, stepResult_host]
              have : ((Exec.step c1).relax p m).store.host.logs = (Exec.step c1).store.host.logs := by
                cases Exec.step c1 <;> rfl
              rw [← this]; exact hRstep
            · rw [hw.2]
              have hl := hlives.live
              revert hl hRtrap
              cases Exec.step c1 with
              | next c' => intro _ hl; exact hl
              | done vs' s' => intro _ hl; exact hl
              | trap reason s' => intro hRtrap _; exact absurd hdone (hRtrap rfl)
            · rw [hw.2]
              cases hsc : Exec.step c1 with
              | next c' => have hl := hlives.live; rw [hsc] at hl; exact hl
              | done vs' s' => have hl := hlives.live; rw [hsc] at hl; exact hl
              | trap reason' s' =>
                rw [hsc] at hRtrapI
                obtain ⟨s'', hrt, his⟩ := hRtrapI rfl
                rw [htr] at hrt
                simp only [StepResult.trap.injEq] at hrt
                obtain ⟨-, rfl⟩ := hrt
                rw [his] at hss
                exact hss
          | none =>
            subst hRR
            unfold runMetered
            simp only [StepResult.relax]
            rw [hk, chargeConfig_relax c _ p m hlim.1 hlim.2 h1]
            simp only [h1, ← hc1]
            rw [hst, frameTransitionGas_relax]
            have hlims : (Exec.step c1).store.host.gas.prepaid ≤ p ∧
                (Exec.step c1).store.host.gas.maxBurnt ≤ m := by
              have := hinvs.host
              rw [show (Exec.step c1).host = (Exec.step c1).store.host by cases Exec.step c1 <;> rfl] at this
              exact ⟨this.1 ▸ hp, this.2 ▸ hm⟩
            rw [chargeWasm_relax _ _ p m hlims.1 hlims.2 h2]
            simp only [h2]
            apply ih
            · exact chargeWasm_hostInvariant hcharge _ _ hinvs
            · intro a fn h
              apply hfs a fn
              cases hs : Exec.step c1 <;> rw [hs] at h <;> simp_all [chargeWasm, chargeConfig, StepResult.store]
            · intro fn h
              apply hms fn
              cases hs : Exec.step c1 <;> rw [hs] at h <;> simp_all [chargeWasm, chargeConfig, StepResult.store]
            · exact chargeWasm_liveInvariant (fun ns cost h => h) _ _ hlives

theorem fnMono_logs {fn : NearHostFn NearState} (h : FnMono fn) (L : List (List UInt8)) :
    Exec.HostFn.Preserves (fun x => L <+: x.logs) fn.toHostFn := by
  intro host mem args hL
  rw [toHostFn_call_host]
  exact hL.trans (h { mem := mem.getD (Memory.new 0 none), host } args).1

theorem fnMono_live {fn : NearHostFn NearState} (h : FnMono fn) (I : Option ExecutionIssue) :
    Exec.HostFn.PreservesLive (fun x => x.lastExecutionIssue = I) fn.toHostFn := by
  apply NearHostFn.PreservesLive.toHostFn
  intro st args hI
  have := (h st args).2
  revert this
  cases fn.invoke st args with
  | Return vals st' => intro h'; exact (h' vals st' rfl).trans hI
  | Trap st' msg => intro _; trivial

/-- **A method run under raised limits, with logs**: the entry charge, then
the metered loop. -/
theorem runInitialized_relaxL (cfg : WasmConfig) (p0 m0 p m : Nat) (hp : p0 ≤ p) (hm : m0 ≤ m)
    (I : Option ExecutionIssue) (fuel : Nat) (c : Config NearState)
    (hgl : Exec.ConfigHostInvariant (GasLimits p0 m0) c) (hf : StoreRelaxFnsL c.store) (hmono : StoreLogsMono c.store)
    (hlive : Exec.ConfigLiveInvariant (fun h => h.lastExecutionIssue = I) c) :
    let lo := runInitialized cfg fuel (.next c)
    let hi := runInitialized cfg fuel (.next { c with store := relaxStore c.store p m })
    (GasEnd lo ∧ lo.1.host.logs <+: hi.1.host.logs ∧
        ((∃ vs s, hi.1 = .done vs s) → lo.1.host.lastExecutionIssue = I) ∧
        (∀ rs ss, hi.1 = .trap rs ss → ss.host.lastExecutionIssue = I → lo.1.host.lastExecutionIssue = I)) ∨
      hi = (lo.1.relax p m, lo.2) := by
  intro lo hi
  have hlim : c.store.host.gas.prepaid ≤ p ∧ c.store.host.gas.maxBurnt ≤ m := by
    have := hgl.2; exact ⟨this.1 ▸ hp, this.2 ▸ hm⟩
  have hcharge : ∀ (ns : NearState) (cost : Nat), GasLimits p0 m0 ns → GasLimits p0 m0 (chargeHost ns cost).1 :=
    fun ns cost h => by
      have hl := chargeHost_gas_limits ns cost
      exact ⟨hl.1.trans h.1, hl.2.trans h.2⟩
  have hentry : entryCost cfg (.next { c with store := relaxStore c.store p m }) = entryCost cfg (.next c) := rfl
  have hhi := runMetered_logs cfg fuel
    (chargeWasm (.next { c with store := relaxStore c.store p m }) (entryCost cfg (.next c))).1 hmono
  simp only [lo, hi, runInitialized]
  rw [hentry]

  cases hent : (chargeWasm (.next c) (entryCost cfg (.next c))).2 with
  | some e =>
    left
    simp only
    have hw := chargeWasm_logs (.next c) (entryCost cfg (.next c))
    have hw' := chargeWasm_logs (.next { c with store := relaxStore c.store p m }) (entryCost cfg (.next c))
    refine ⟨Or.inl ⟨e, rfl, chargeWasm_error _ _ hent⟩, ?_, fun _ => by rw [hw.2]; exact hlive.2,
      fun _ _ _ _ => by rw [hw.2]; exact hlive.2⟩
    rw [hw.1]
    split
    · rw [hw'.1]; exact List.prefix_refl _
    · exact (by rw [hw'.1] at hhi; exact hhi)
  | none =>
    rw [show (StepResult.next { c with store := relaxStore c.store p m }) = (StepResult.next c).relax p m from rfl,
      chargeWasm_relax (.next c) _ p m hlim.1 hlim.2 hent]
    simp only
    have hr := runMetered_relaxL cfg p0 m0 p m hp hm I fuel (chargeWasm (.next c) (entryCost cfg (.next c))).1
      (chargeWasm_hostInvariant hcharge _ _ hgl) hf hmono
      (chargeWasm_liveInvariant (fun ns cost h => h) _ _ hlive)
    exact hr

end NearLogic
