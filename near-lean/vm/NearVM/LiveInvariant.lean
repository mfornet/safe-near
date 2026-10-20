import NearVM.InterpreterInvariant

namespace Wasm

/-- Catchable host exceptions must preserve the invariant; terminal traps need
not, because the caller rolls back their speculative state. -/
def HostResult.LiveSatisfies (P : α → Prop) : HostResult α → Prop
  | .Return _ st | .Throw st _ _ => P st.host
  | .Trap _ _ => True

def HostFn.PreservesLive (P : α → Prop) (fn : HostFn α) : Prop :=
  ∀ st args, P st.host → HostResult.LiveSatisfies P (fn.invoke st args)

def RuntimePreservesLive (P : α → Prop) (runtime : SmallStep.RuntimeEnv α) : Prop :=
  ∀ (index : Nat) (fn : HostFn α), (fn ∈ (runtime.instances[index]!).host.funcs ∨
    fn ∈ (runtime.instances[index]!).host.foreignFuncs) → HostFn.PreservesLive P fn

variable {α : Type} {P : α → Prop}

theorem RuntimePreservesLive.of_hosts_eq {before after : SmallStep.RuntimeEnv α}
    (h : ∀ (slot : Nat), (after.instances[slot]!).host = (before.instances[slot]!).host)
    (hhosts : RuntimePreservesLive P before) : RuntimePreservesLive P after := by
  intro slot fn hmember
  apply hhosts slot fn
  simpa only [h slot] using hmember

theorem hostReturn_liveInvariant {runtime : SmallStep.RuntimeEnv α}
    {fn : HostFn α} {st after : Store α} {args : List Value}
    (values : List Value) (hcall : fn.invoke st args = .Return values after)
    (hhosts : RuntimePreservesLive P runtime) (hwf : P st.host)
    (hmember : fn ∈ runtime.currentHost.funcs ∨ fn ∈ runtime.currentHost.foreignFuncs) : P after.host := by
  have hp := hhosts runtime.entry.id fn hmember st args hwf
  rw [hcall] at hp
  exact hp

theorem hostThrow_liveInvariant {runtime : SmallStep.RuntimeEnv α}
    {fn : HostFn α} {st after : Store α} {args : List Value}
    (tag : Nat) (values : List Value) (hcall : fn.invoke st args = .Throw after tag values)
    (hhosts : RuntimePreservesLive P runtime) (hwf : P st.host)
    (hmember : fn ∈ runtime.currentHost.funcs ∨ fn ∈ runtime.currentHost.foreignFuncs) : P after.host := by
  have hp := hhosts runtime.entry.id fn hmember st args hwf
  rw [hcall] at hp
  exact hp

set_option maxHeartbeats 2000000 in
theorem step_liveInvariant {before after : SmallStep.Config α} {kind : SmallStep.StepKind}
    (h : SmallStep.Step before kind after)
    (hhosts : RuntimePreservesLive P before.store.runtime)
    (hwf : P before.store.wasm.host) : after.LiveHost P := by
  revert hhosts hwf
  induction h <;> intro hhosts hwf <;> try exact hwf <;> try trivial
  all_goals try (solve | simp only [SmallStep.Config.LiveHost])
  all_goals first
    | simpa only [SmallStep.Config.LiveHost, SmallStep.prepareCatch_host, SmallStep.setMemoryAt_host] using hwf
    | (rename_i hcall
       first
       | apply hostReturn_liveInvariant _ hcall hhosts hwf
       | apply hostThrow_liveInvariant _ _ hcall hhosts hwf
       solve_by_elim [Or.inl, Or.inr, List.mem_of_getElem?])
    | (rename_i heval
       have hp := execGcOp_fallthrough_host heval
       simpa only [SmallStep.Config.LiveHost, hp] using hwf)
    | (rename_i heval
       have hp := execGcOp_trap_host heval
       simpa only [SmallStep.Config.LiveHost, hp] using hwf)
    | (rename_i heval htarget
       have hp := execGcOp_break_host heval
       simpa only [SmallStep.Config.LiveHost, hp] using hwf)
    | skip
  case memOp =>
    rename_i henter hstep ih
    rw [SmallStep.resumeAfterIndexedMemory_liveHost]
    apply ih
    · exact RuntimePreservesLive.of_hosts_eq (SmallStep.enterIndexedMemory_hosts henter) hhosts
    · simpa only [SmallStep.enterIndexedMemory_host henter] using hwf

/-- A terminal trap cannot step back into a live execution. -/
theorem step_source_running {before after : SmallStep.Config α} {kind : SmallStep.StepKind}
    (h : SmallStep.Step before kind after) : ∃ thread, before.expr = .running thread := by
  cases h <;> exact ⟨_, rfl⟩

def ConfigLiveInvariant (P : α → Prop) (config : SmallStep.Config α) : Prop :=
  RuntimePreservesLive P config.store.runtime ∧ config.LiveHost P

theorem step_preserves_liveInvariant {before after : SmallStep.Config α} {kind : SmallStep.StepKind}
    (hstep : SmallStep.Step before kind after) (h : ConfigLiveInvariant P before) :
    ConfigLiveInvariant P after := by
  obtain ⟨thread, he⟩ := step_source_running hstep
  have hp : P before.store.wasm.host := by simpa only [SmallStep.Config.LiveHost, he] using h.2
  refine ⟨?_, step_liveInvariant hstep h.1 hp⟩
  apply RuntimePreservesLive.of_hosts_eq _ h.1
  intro slot
  rw [SmallStep.instances_preserved hstep]

theorem steps_preserve_liveInvariant {before after : SmallStep.Config α} {trace : List SmallStep.StepKind}
    (hsteps : SmallStep.Steps before trace after) (h : ConfigLiveInvariant P before) :
    ConfigLiveInvariant P after := by
  induction hsteps with
  | refl => exact h
  | cons head tail ih => exact ih (step_preserves_liveInvariant head h)

theorem singleton_runtime_liveInvariant (instance_ : SmallStep.ModuleInstance α)
    (hhosts : ∀ fn, (fn ∈ instance_.host.funcs ∨ fn ∈ instance_.host.foreignFuncs) →
      HostFn.PreservesLive P fn) :
    RuntimePreservesLive P { instances := #[instance_], entry := ⟨0⟩ } := by
  intro index fn hmember
  cases index with
  | zero => exact hhosts fn (by simpa using hmember)
  | succ index =>
    simp only [getElem!_def, Array.getElem?_singleton, Nat.succ_ne_zero, ite_false] at hmember
    change fn ∈ ([] : List (HostFn α)) ∨ fn ∈ [] at hmember
    simp at hmember

theorem initConfig_liveInvariant {instance_ : SmallStep.ModuleInstance α} {entry : Nat}
    {st : Store α} {args : List Value} {config : SmallStep.Config α}
    (hinit : SmallStep.initConfig instance_ entry st args = .ok config)
    (hhosts : ∀ fn, (fn ∈ instance_.host.funcs ∨ fn ∈ instance_.host.foreignFuncs) →
      HostFn.PreservesLive P fn) (hwf : P st.host) : ConfigLiveInvariant P config := by
  unfold SmallStep.initConfig at hinit
  split at hinit <;> split at hinit <;> simp only [Except.ok.injEq, reduceCtorEq] at hinit
  all_goals subst config; exact ⟨singleton_runtime_liveInvariant instance_ hhosts, hwf⟩

end Wasm
