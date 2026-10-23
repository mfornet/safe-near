import Wasm.Exec

/-!
# Host-state invariants over execution

Only host functions touch the host state: every instruction of the machine
leaves `store.host` unchanged, and `enter` changes it exactly by one host
call. So any predicate on the host state that every host function in the
store preserves is preserved by every step. A "live" variant allows a
trapping host call to break the predicate, for hosts that roll back on traps.
-/

namespace Wasm.Exec

def _root_.Wasm.HostOutcome.host : HostOutcome H → H
  | .return _ h _ | .trap _ h _ => h

/-- The host functions that can be called: those in the store. -/
def StoreHosts (P : HostFn H → Prop) (store : Store H) : Prop :=
  ∀ fn, FuncInst.host fn ∈ store.funcs → P fn

/-- Every call preserves `P`, trapping or not. -/
def HostFn.Preserves (P : H → Prop) (fn : HostFn H) : Prop :=
  ∀ h mem args, P h → P (fn.call h mem args).host

/-- Every returning call preserves `P`. -/
def HostFn.PreservesLive (P : H → Prop) (fn : HostFn H) : Prop :=
  ∀ h mem args values h' mem', P h → fn.call h mem args = .return values h' mem' → P h'

theorem setMemOf_host (s : Store H) (inst : ModuleInst) (m : Memory) :
    (s.setMemOf inst m).host = s.host := by
  unfold Store.setMemOf; split <;> rfl

theorem setTable_host (s : Store H) (addr : Nat) (t : TableInst) :
    (setTable s addr t).host = s.host := rfl

theorem setMemOf_funcs (s : Store H) (inst : ModuleInst) (m : Memory) :
    (s.setMemOf inst m).funcs = s.funcs := by
  unfold Store.setMemOf; split <;> rfl

theorem setTable_funcs (s : Store H) (addr : Nat) (t : TableInst) :
    (setTable s addr t).funcs = s.funcs := rfl

theorem evalMemOp_store (store : Store H) (inst : ModuleInst) (stack : Array Value)
    (labels : List Label) (rest : List Instr) (locals : Array Value)
    (k : Memory → Option Memory) :
    (evalMemOp store inst stack labels rest locals k).store.host = store.host ∧
    (evalMemOp store inst stack labels rest locals k).store.funcs = store.funcs := by
  unfold evalMemOp
  split
  · exact ⟨rfl, rfl⟩
  · split
    · simp [setMemOf_host, setMemOf_funcs]
    · exact ⟨rfl, rfl⟩

theorem branch_store (store : Store H) (stack : Array Value) (labels : List Label)
    (locals : Array Value) (l : Nat) :
    (branch store stack labels locals l).store = store := by
  unfold branch
  dsimp only
  repeat' split
  all_goals rfl

theorem storeNat_store {store : Store H} {inst : ModuleInst} {arg : MemArg} {addr : UInt32}
    {len v : Nat} {s : Store H} (h : storeNat store inst arg addr len v = some s) :
    s.host = store.host ∧ s.funcs = store.funcs := by
  unfold storeNat at h
  cases hm : store.memOf inst with
  | none => simp [hm, Option.bind] at h
  | some mem =>
    cases hw : mem.writeNat (addr.toNat + arg.offset) len v with
    | none => simp [hm, hw, Option.bind] at h
    | some mem' =>
      simp [hm, hw] at h
      subst h
      exact ⟨setMemOf_host _ _ _, setMemOf_funcs _ _ _⟩

set_option maxHeartbeats 4000000 in
/-- Instructions never touch the host state nor the function instances. -/
theorem instr_store (store : Store H) (inst : ModuleInst) (locals stack : Array Value)
    (labels : List Label) (i : Instr) (rest : List Instr) :
    (instr store inst locals stack labels i rest).store.host = store.host ∧
    (instr store inst locals stack labels i rest).store.funcs = store.funcs := by
  unfold instr
  cases i <;> dsimp only <;> (repeat' split) <;>
    first
    | (simp_all [branch_store, evalMemOp_store, setTable_host, setMemOf_host, setTable_funcs,
        setMemOf_funcs]; done)
    | exact storeNat_store (by assumption)

/-! ## Invariants -/

/-- `P` holds on the host state and every host function preserves it. -/
def ConfigHostInvariant (P : H → Prop) (c : Config H) : Prop :=
  StoreHosts (HostFn.Preserves P) c.store ∧ P c.store.host

/-- `P` holds on the host state and every returning host call preserves it. -/
def ConfigLiveInvariant (P : H → Prop) (c : Config H) : Prop :=
  StoreHosts (HostFn.PreservesLive P) c.store ∧ P c.store.host

/-- `P` holds unless execution trapped. -/
def _root_.Wasm.StepResult.LiveHost (P : H → Prop) : StepResult H → Prop
  | .next c => P c.store.host
  | .done _ s => P s.host
  | .trap _ _ => True

theorem commitHost_host (store : Store H) (ci : Option ModuleInst) (host : H) (m : Option Memory) :
    (commitHost store ci host m).host = host := by
  unfold commitHost; split <;> simp [setMemOf_host]

theorem commitHost_funcs (store : Store H) (ci : Option ModuleInst) (host : H)
    (m : Option Memory) : (commitHost store ci host m).funcs = store.funcs := by
  unfold commitHost; split <;> simp [setMemOf_funcs]

theorem enter_funcs (c : Config H) (stack : Array Value) (frames : List CallFrame) (addr : Nat) :
    (enter c stack frames addr).store.funcs = c.store.funcs := by
  unfold enter
  split
  · rfl
  · rename_i fn hfn
    dsimp only
    generalize popN stack fn.type.params.length = pa
    obtain ⟨stack', args⟩ := pa
    dsimp only
    generalize (frames.head?.bind fun f => c.store.modules[f.inst]?) = ci
    split
    · split <;> simp [StepResult.store, commitHost_funcs]
    · simp [StepResult.store, commitHost_funcs]
  · split
    · rfl
    · rfl

theorem enter_hostInvariant {P : H → Prop} (c : Config H) (stack : Array Value)
    (frames : List CallFrame) (addr : Nat) (h : ConfigHostInvariant P c) :
    P (enter c stack frames addr).host := by
  unfold enter
  split
  · exact h.2
  · rename_i fn hfn
    have hp := h.1 fn (Array.mem_of_getElem? hfn)
    dsimp only
    generalize popN stack fn.type.params.length = pa
    obtain ⟨stack', args⟩ := pa
    dsimp only
    generalize (frames.head?.bind fun f => c.store.modules[f.inst]?) = ci
    have key := hp c.store.host (ci.bind c.store.memOf) args h.2
    split
    · rename_i values host mem' hcall
      rw [hcall] at key
      simp only [HostOutcome.host] at key
      split <;> simpa [StepResult.host, commitHost_host] using key
    · rename_i reason host mem' hcall
      rw [hcall] at key
      simp only [HostOutcome.host] at key
      simpa [StepResult.host, commitHost_host] using key
  · split
    · exact h.2
    · exact h.2

theorem enter_liveInvariant {P : H → Prop} (c : Config H) (stack : Array Value)
    (frames : List CallFrame) (addr : Nat) (h : ConfigLiveInvariant P c) :
    (enter c stack frames addr).LiveHost P := by
  unfold enter
  split
  · trivial
  · rename_i fn hfn
    have hp := h.1 fn (Array.mem_of_getElem? hfn)
    dsimp only
    generalize popN stack fn.type.params.length = pa
    obtain ⟨stack', args⟩ := pa
    dsimp only
    generalize (frames.head?.bind fun f => c.store.modules[f.inst]?) = ci
    split
    · rename_i values host mem' hcall
      have key := hp c.store.host (ci.bind c.store.memOf) args values host mem' h.2 hcall
      split <;> simpa [StepResult.LiveHost, commitHost_host] using key
    · trivial
  · split
    · trivial
    · exact h.2

/-- A running step keeps the execution limits. -/
theorem step_limits (c : Config H) {c' : Config H} (h : step c = .next c') : c'.limits = c.limits := by
  unfold step at h
  split at h
  · cases h
  · rename_i frame frames hframes
    split at h
    · unfold leave at h; dsimp only at h; (repeat' split at h) <;> cases h <;> rfl
    · cases h; rfl
    · dsimp only at h
      split at h
      · cases h; rfl
      · unfold enter at h
        split at h
        · cases h
        · dsimp only at h
          (repeat' split at h) <;> (try cases h) <;> rfl
        · split at h
          · cases h
          · cases h; rfl
      · unfold leave at h; dsimp only at h; (repeat' split at h) <;> cases h <;> rfl
      · cases h

theorem step_funcs (c : Config H) : (step c).store.funcs = c.store.funcs := by
  unfold step
  split
  · rfl
  · rename_i frame frames hframes
    split
    · unfold leave; dsimp only; repeat' split; all_goals rfl
    · rfl
    · rename_i i rest hcode
      have hstore := instr_store c.store (c.store.modules[frame.inst]!) frame.locals c.thread.stack
        frame.labels i rest
      dsimp only
      split
      · exact hstore.2
      · rw [enter_funcs]; exact hstore.2
      · unfold leave; dsimp only; repeat' split; all_goals exact hstore.2
      · exact hstore.2

theorem step_hostInvariant {P : H → Prop} (c : Config H) (h : ConfigHostInvariant P c) :
    P (step c).host := by
  unfold step
  split
  · exact h.2
  · rename_i frame frames hframes
    split
    · unfold leave; dsimp only; repeat' split; all_goals exact h.2
    · exact h.2
    · rename_i i rest hcode
      have hstore := instr_store c.store (c.store.modules[frame.inst]!) frame.locals c.thread.stack
        frame.labels i rest
      have h1 : P (instr c.store (c.store.modules[frame.inst]!) frame.locals c.thread.stack
        frame.labels i rest).store.host := hstore.1 ▸ h.2
      dsimp only
      split
      · exact h1
      · apply enter_hostInvariant
        exact ⟨fun fn hm => h.1 fn (hstore.2 ▸ hm), h1⟩
      · unfold leave; dsimp only; repeat' split; all_goals exact h1
      · exact h1

theorem step_liveInvariant {P : H → Prop} (c : Config H) (h : ConfigLiveInvariant P c) :
    (step c).LiveHost P := by
  unfold step
  split
  · exact h.2
  · rename_i frame frames hframes
    split
    · unfold leave; dsimp only; repeat' split; all_goals exact h.2
    · exact h.2
    · rename_i i rest hcode
      have hstore := instr_store c.store (c.store.modules[frame.inst]!) frame.locals c.thread.stack
        frame.labels i rest
      have h1 : P (instr c.store (c.store.modules[frame.inst]!) frame.locals c.thread.stack
        frame.labels i rest).store.host := hstore.1 ▸ h.2
      dsimp only
      split
      · exact h1
      · apply enter_liveInvariant
        exact ⟨fun fn hm => h.1 fn (hstore.2 ▸ hm), h1⟩
      · unfold leave; dsimp only; repeat' split; all_goals exact h1
      · trivial

theorem step_preserves_hostInvariant {P : H → Prop} {c c' : Config H}
    (h : ConfigHostInvariant P c) (hs : step c = .next c') : ConfigHostInvariant P c' := by
  refine ⟨fun fn hm => h.1 fn ?_, ?_⟩
  · have := step_funcs c
    rw [hs] at this
    exact this ▸ hm
  · have := step_hostInvariant c h
    rw [hs] at this
    exact this

theorem step_preserves_liveInvariant {P : H → Prop} {c c' : Config H}
    (h : ConfigLiveInvariant P c) (hs : step c = .next c') : ConfigLiveInvariant P c' := by
  refine ⟨fun fn hm => h.1 fn ?_, ?_⟩
  · have := step_funcs c
    rw [hs] at this
    exact this ▸ hm
  · have := step_liveInvariant c h
    rw [hs] at this
    exact this

end Wasm.Exec
