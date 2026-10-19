import NearVM.ExecutionFrames
import Interpreter.Wasm.SmallStep

namespace Wasm

/-- A host result satisfies the predicate in every carried store. -/
def HostResult.Satisfies (P : α → Prop) : HostResult α → Prop
  | .Return _ st | .Trap st _ | .Throw st _ _ => P st.host

def HostFn.Preserves (P : α → Prop) (fn : HostFn α) : Prop :=
  ∀ st args, P st.host → HostResult.Satisfies P (fn.invoke st args)

/-- Every callable host in every instance satisfies the same invariant. -/
def RuntimePreservesInvariant (P : α → Prop) (runtime : SmallStep.RuntimeEnv α) : Prop :=
  ∀ (index : Nat) (fn : HostFn α), (fn ∈ (runtime.instances[index]!).host.funcs ∨
    fn ∈ (runtime.instances[index]!).host.foreignFuncs) → HostFn.Preserves P fn

variable {α : Type} {P : α → Prop}

theorem RuntimePreservesInvariant.of_hosts_eq {before after : SmallStep.RuntimeEnv α}
    (h : ∀ (slot : Nat), (after.instances[slot]!).host = (before.instances[slot]!).host)
    (hhosts : RuntimePreservesInvariant P before) : RuntimePreservesInvariant P after := by
  intro slot fn hmember
  apply hhosts slot fn
  simpa only [h slot] using hmember

theorem invariant_step_instances {before after : SmallStep.Config α} {kind : SmallStep.StepKind}
    (h : SmallStep.Step before kind after) :
    after.store.runtime.instances = before.store.runtime.instances := by
  exact SmallStep.instances_preserved h

theorem hostReturn_invariant {runtime : SmallStep.RuntimeEnv α}
    {fn : HostFn α} {st after : Store α} {args : List Value}
    (values : List Value)
    (hcall : fn.invoke st args = .Return values after)
    (hhosts : RuntimePreservesInvariant P runtime)
    (hwf : P st.host)
    (hmember : fn ∈ runtime.currentHost.funcs ∨ fn ∈ runtime.currentHost.foreignFuncs) :
    P after.host := by
  have hp := hhosts runtime.entry.id fn hmember st args hwf
  rw [hcall] at hp
  exact hp

theorem hostTrap_invariant {runtime : SmallStep.RuntimeEnv α}
    {fn : HostFn α} {st after : Store α} {args : List Value}
    (message : String)
    (hcall : fn.invoke st args = .Trap after message)
    (hhosts : RuntimePreservesInvariant P runtime)
    (hwf : P st.host)
    (hmember : fn ∈ runtime.currentHost.funcs ∨ fn ∈ runtime.currentHost.foreignFuncs) :
    P after.host := by
  have hp := hhosts runtime.entry.id fn hmember st args hwf
  rw [hcall] at hp
  exact hp

theorem hostThrow_invariant {runtime : SmallStep.RuntimeEnv α}
    {fn : HostFn α} {st after : Store α} {args : List Value}
    (tag : Nat) (values : List Value)
    (hcall : fn.invoke st args = .Throw after tag values)
    (hhosts : RuntimePreservesInvariant P runtime)
    (hwf : P st.host)
    (hmember : fn ∈ runtime.currentHost.funcs ∨ fn ∈ runtime.currentHost.foreignFuncs) :
    P after.host := by
  have hp := hhosts runtime.entry.id fn hmember st args hwf
  rw [hcall] at hp
  exact hp

set_option maxHeartbeats 2000000 in
theorem step_hostInvariant {before after : SmallStep.Config α} {kind : SmallStep.StepKind}
    (h : SmallStep.Step before kind after)
    (hhosts : RuntimePreservesInvariant P before.store.runtime)
    (hwf : P before.store.wasm.host) :
    P after.store.wasm.host := by
  revert hhosts hwf
  induction h <;> intro hhosts hwf <;> try exact hwf
  all_goals first
    | simpa only [SmallStep.prepareCatch_host, SmallStep.setMemoryAt_host] using hwf
    | (rename_i hcall
       first
       | apply hostReturn_invariant _ hcall hhosts hwf
       | apply hostTrap_invariant _ hcall hhosts hwf
       | apply hostThrow_invariant _ _ hcall hhosts hwf
       solve_by_elim [Or.inl, Or.inr, List.mem_of_getElem?])
    | (rename_i heval
       have hp := execGcOp_fallthrough_host heval
       simpa only [hp] using hwf)
    | (rename_i heval
       have hp := execGcOp_trap_host heval
       simpa only [hp] using hwf)
    | (rename_i heval htarget
       have hp := execGcOp_break_host heval
       simpa only [hp] using hwf)
    | skip
  case memOp =>
    rename_i henter hstep ih
    rw [SmallStep.resumeAfterIndexedMemory_host]
    apply ih
    · exact RuntimePreservesInvariant.of_hosts_eq (SmallStep.enterIndexedMemory_hosts henter) hhosts
    · simpa only [SmallStep.enterIndexedMemory_host henter] using hwf

/-- A state predicate and the host environments required to preserve it. -/
def ConfigHostInvariant (P : α → Prop) (config : SmallStep.Config α) : Prop :=
  RuntimePreservesInvariant P config.store.runtime ∧ P config.store.wasm.host

theorem step_preserves_hostInvariant {before after : SmallStep.Config α} {kind : SmallStep.StepKind}
    (hstep : SmallStep.Step before kind after) (h : ConfigHostInvariant P before) :
    ConfigHostInvariant P after := by
  refine ⟨?_, step_hostInvariant hstep h.1 h.2⟩
  apply RuntimePreservesInvariant.of_hosts_eq _ h.1
  intro slot
  rw [SmallStep.instances_preserved hstep]

theorem steps_preserve_hostInvariant {before after : SmallStep.Config α} {trace : List SmallStep.StepKind}
    (hsteps : SmallStep.Steps before trace after) (h : ConfigHostInvariant P before) :
    ConfigHostInvariant P after := by
  induction hsteps with
  | refl => exact h
  | cons head tail ih => exact ih (step_preserves_hostInvariant head h)

theorem singleton_runtime_invariant (instance_ : SmallStep.ModuleInstance α)
    (hhosts : ∀ fn, (fn ∈ instance_.host.funcs ∨ fn ∈ instance_.host.foreignFuncs) →
      HostFn.Preserves P fn) :
    RuntimePreservesInvariant P { instances := #[instance_], entry := ⟨0⟩ } := by
  intro index fn hmember
  cases index with
  | zero => exact hhosts fn (by simpa using hmember)
  | succ index =>
    simp only [getElem!_def, Array.getElem?_singleton, Nat.succ_ne_zero, ite_false] at hmember
    change fn ∈ ([] : List (HostFn α)) ∨ fn ∈ [] at hmember
    simp at hmember

theorem initConfig_hostInvariant {instance_ : SmallStep.ModuleInstance α} {entry : Nat}
    {st : Store α} {args : List Value} {config : SmallStep.Config α}
    (hinit : SmallStep.initConfig instance_ entry st args = .ok config)
    (hhosts : ∀ fn, (fn ∈ instance_.host.funcs ∨ fn ∈ instance_.host.foreignFuncs) →
      HostFn.Preserves P fn) (hwf : P st.host) : ConfigHostInvariant P config := by
  unfold SmallStep.initConfig at hinit
  split at hinit <;> split at hinit <;> simp only [Except.ok.injEq, reduceCtorEq] at hinit
  all_goals subst config; exact ⟨singleton_runtime_invariant instance_ hhosts, hwf⟩

end Wasm
