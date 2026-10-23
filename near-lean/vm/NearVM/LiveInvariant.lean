import NearVM.InterpreterInvariant

/-!
# Live invariants: broken only by traps

Terminal traps need not preserve a predicate, because the caller rolls back
their speculative state; returning host calls must.
-/

namespace Wasm

def HostResult.LiveSatisfies (P : α → Prop) : HostResult α → Prop
  | .Return _ st => P st.host
  | .Trap _ _ => True

def NearHostFn.PreservesLive (P : α → Prop) (fn : NearHostFn α) : Prop :=
  ∀ st args, P st.host → HostResult.LiveSatisfies P (fn.invoke st args)

theorem NearHostFn.PreservesLive.toHostFn {P : α → Prop} {fn : NearHostFn α}
    (h : fn.PreservesLive P) : Exec.HostFn.PreservesLive P fn.toHostFn := by
  intro host mem args values host' mem' hp hcall
  have := h { mem := mem.getD (Memory.new 0 none), host } args hp
  unfold NearHostFn.toHostFn at hcall
  dsimp only at hcall
  split at hcall
  · rename_i heq
    rw [heq] at this
    cases hcall
    exact this
  · cases hcall

/-- Every host function in the store preserves `P` on return, and `P` holds. -/
def StoreLiveInvariant (P : α → Prop) (store : Store α) : Prop :=
  Exec.StoreHosts (Exec.HostFn.PreservesLive P) store ∧ P store.host

abbrev ConfigLiveInvariant (P : α → Prop) (c : Config α) : Prop := Exec.ConfigLiveInvariant P c

/-- The live invariant on a machine state: after a trap only the host
functions are constrained. -/
def MachineLiveInvariant (P : α → Prop) : StepResult α → Prop
  | .next c => Exec.ConfigLiveInvariant P c
  | .done _ s => StoreLiveInvariant P s
  | .trap _ s => Exec.StoreHosts (Exec.HostFn.PreservesLive P) s

theorem MachineLiveInvariant.live {P : α → Prop} {m : StepResult α}
    (h : MachineLiveInvariant P m) : m.LiveHost P := by
  cases m with
  | next c => exact h.2
  | done _ s => exact h.2
  | trap _ _ => trivial

theorem MachineLiveInvariant.hosts {P : α → Prop} {m : StepResult α}
    (h : MachineLiveInvariant P m) : Exec.StoreHosts (Exec.HostFn.PreservesLive P) m.store := by
  cases m with
  | next c => exact h.1
  | done _ s => exact h.1
  | trap _ _ => exact h

theorem MachineLiveInvariant.of_parts {P : α → Prop} {m : StepResult α}
    (hhosts : Exec.StoreHosts (Exec.HostFn.PreservesLive P) m.store) (hp : m.LiveHost P) :
    MachineLiveInvariant P m := by
  cases m with
  | next c => exact ⟨hhosts, hp⟩
  | done _ s => exact ⟨hhosts, hp⟩
  | trap _ _ => exact hhosts

theorem step_liveInvariant {P : α → Prop} {c : Config α} (h : Exec.ConfigLiveInvariant P c) :
    MachineLiveInvariant P (Exec.step c) := by
  have hf := Exec.step_funcs c
  have hp := Exec.step_liveInvariant c h
  exact .of_parts (fun fn hm => h.1 fn (hf ▸ hm)) hp

theorem step_preserves_liveInvariant {P : α → Prop} {c c' : Config α}
    (h : Exec.ConfigLiveInvariant P c) (hs : Exec.step c = .next c') :
    Exec.ConfigLiveInvariant P c' :=
  Exec.step_preserves_liveInvariant h hs

theorem start_liveInvariant {P : α → Prop} {store : Store α} (h : StoreLiveInvariant P store)
    (limits : ExecLimits) (addr : Nat) (args : List Value) :
    MachineLiveInvariant P (Exec.start store limits addr args) := by
  unfold Exec.start
  have hf := Exec.enter_funcs ⟨store, ⟨#[], []⟩, limits⟩ args.toArray [] addr
  have hp := Exec.enter_liveInvariant (P := P) ⟨store, ⟨#[], []⟩, limits⟩ args.toArray [] addr h
  exact .of_parts (fun fn hm => h.1 fn (hf ▸ hm)) hp

theorem allocate_liveInvariant {P : α → Prop} {store : Store α} {env : HostEnv α}
    (hstore : Exec.StoreHosts (Exec.HostFn.PreservesLive P) store)
    (henv : ∀ fn ∈ env.funcs, fn.PreservesLive P) :
    Exec.StoreHosts (Exec.HostFn.PreservesLive P) (env.allocate store).1 := by
  intro fn hm
  rcases HostEnv.allocate_funcs store env fn hm with hin | ⟨nfn, hmem, rfl⟩
  · exact hstore fn hin
  · exact (henv nfn hmem).toHostFn

theorem empty_storeHostsLive' {P : α → Prop} (host : α) :
    Exec.StoreHosts (Exec.HostFn.PreservesLive P) (Store.empty host) := by
  intro fn hm
  simp [Store.empty] at hm

theorem instantiateModule_liveInvariant {P : α → Prop} {store store' : Store α} {vm : ValidModule}
    {imports : List ExternVal} {inst : ModuleInst} (h : StoreLiveInvariant P store)
    (hi : Link.instantiateModule store vm imports = .ok (store', inst)) :
    StoreLiveInvariant P store' :=
  let same := Link.instantiateModule_same store vm imports hi
  ⟨fun fn hm => h.1 fn (same.2 fn hm), same.1 ▸ h.2⟩

theorem resolvedStart_liveInvariant {P : α → Prop} {env : HostEnv α} {host : α}
    {store store' : Store α} {imports : List ExternVal} {vm : ValidModule} {inst : ModuleInst}
    {limits : ExecLimits} {addr : Nat} {args : List Value} {c : Config α}
    (henv : ∀ fn ∈ env.funcs, fn.PreservesLive P)
    (halloc : env.allocate (Store.empty host) = (store, imports))
    (hinst : Link.instantiateModule store vm imports = .ok (store', inst))
    (hstart : Exec.startWasm store' limits addr args = some c) (hp : P host) :
    ConfigLiveInvariant P c := by
  have h0 : StoreLiveInvariant P store := by
    have := allocate_liveInvariant (P := P) (empty_storeHostsLive' host) henv
    rw [halloc] at this
    refine ⟨this, ?_⟩
    have hh := HostEnv.allocate_host (Store.empty host) env
    rw [halloc] at hh
    exact hh ▸ hp
  have h1 := instantiateModule_liveInvariant h0 hinst
  show Exec.StoreHosts _ c.store ∧ P c.store.host
  rw [Exec.startWasm_store hstart]
  exact h1

theorem empty_storeHostsLive {P : α → Prop} (host : α) :
    Exec.StoreHosts (Exec.HostFn.PreservesLive P) (Store.empty host) := by
  intro fn hm
  simp [Store.empty] at hm

end Wasm
