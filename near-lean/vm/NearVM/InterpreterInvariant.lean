import NearVM.Interp

/-!
# Host-state invariants through execution

A predicate on the host state that every host function preserves is
preserved by every step of the machine: the runtime proves it once
(`Wasm.Exec.step_preserves_hostInvariant`), and this module states it for
NEAR host functions and for machine states, running or finished.
-/

namespace Wasm

/-- A host result satisfies the predicate in every carried store. -/
def HostResult.Satisfies (P : α → Prop) : HostResult α → Prop
  | .Return _ st | .Trap st _ => P st.host

def NearHostFn.Preserves (P : α → Prop) (fn : NearHostFn α) : Prop :=
  ∀ st args, P st.host → HostResult.Satisfies P (fn.invoke st args)

theorem NearHostFn.Preserves.toHostFn {P : α → Prop} {fn : NearHostFn α} (h : fn.Preserves P) :
    Exec.HostFn.Preserves P fn.toHostFn := by
  intro host mem args hp
  have := h { mem := mem.getD (Memory.new 0 none), host } args hp
  unfold NearHostFn.toHostFn
  dsimp only
  split <;> rename_i heq <;> rw [heq] at this <;> exact this

/-- Every host function in the store preserves `P`, and `P` holds. -/
def StoreHostInvariant (P : α → Prop) (store : Store α) : Prop :=
  Exec.StoreHosts (Exec.HostFn.Preserves P) store ∧ P store.host

abbrev ConfigHostInvariant (P : α → Prop) (c : Config α) : Prop := Exec.ConfigHostInvariant P c

/-- The invariant on a machine state, running or finished. -/
def MachineHostInvariant (P : α → Prop) : StepResult α → Prop
  | .next c => Exec.ConfigHostInvariant P c
  | .done _ s => StoreHostInvariant P s
  | .trap _ s => StoreHostInvariant P s

theorem MachineHostInvariant.host {P : α → Prop} {m : StepResult α}
    (h : MachineHostInvariant P m) : P m.host := by
  cases m <;> exact h.2

theorem MachineHostInvariant.hosts {P : α → Prop} {m : StepResult α}
    (h : MachineHostInvariant P m) : Exec.StoreHosts (Exec.HostFn.Preserves P) m.store := by
  cases m <;> exact h.1

theorem MachineHostInvariant.of_parts {P : α → Prop} {m : StepResult α}
    (hhosts : Exec.StoreHosts (Exec.HostFn.Preserves P) m.store) (hp : P m.host) :
    MachineHostInvariant P m := by
  cases m <;> exact ⟨hhosts, hp⟩

theorem step_hostInvariant {P : α → Prop} {c : Config α} (h : Exec.ConfigHostInvariant P c) :
    MachineHostInvariant P (Exec.step c) := by
  have hf := Exec.step_funcs c
  have hp := Exec.step_hostInvariant c h
  exact .of_parts (fun fn hm => h.1 fn (hf ▸ hm)) hp

theorem step_preserves_hostInvariant {P : α → Prop} {c c' : Config α}
    (h : Exec.ConfigHostInvariant P c) (hs : Exec.step c = .next c') :
    Exec.ConfigHostInvariant P c' :=
  Exec.step_preserves_hostInvariant h hs

/-- Starting a call keeps the invariant. -/
theorem start_hostInvariant {P : α → Prop} {store : Store α} (h : StoreHostInvariant P store)
    (limits : ExecLimits) (addr : Nat) (args : List Value) :
    MachineHostInvariant P (Exec.start store limits addr args) := by
  unfold Exec.start
  have hf := Exec.enter_funcs ⟨store, ⟨#[], []⟩, limits⟩ args.toArray [] addr
  have hp := Exec.enter_hostInvariant (P := P) ⟨store, ⟨#[], []⟩, limits⟩ args.toArray [] addr h
  exact .of_parts (fun fn hm => h.1 fn (hf ▸ hm)) hp

/-- Allocating a NEAR host environment whose functions preserve `P` keeps a
store's host functions preserving `P`. -/
theorem allocate_hostInvariant {P : α → Prop} {store : Store α} {env : HostEnv α}
    (hstore : Exec.StoreHosts (Exec.HostFn.Preserves P) store)
    (henv : ∀ fn ∈ env.funcs, fn.Preserves P) :
    Exec.StoreHosts (Exec.HostFn.Preserves P) (env.allocate store).1 := by
  intro fn hm
  rcases HostEnv.allocate_funcs store env fn hm with hin | ⟨nfn, hmem, rfl⟩
  · exact hstore fn hin
  · exact (henv nfn hmem).toHostFn

theorem empty_storeHosts' {P : α → Prop} (host : α) :
    Exec.StoreHosts (Exec.HostFn.Preserves P) (Store.empty host) := by
  intro fn hm
  simp [Store.empty] at hm

/-- Instantiation keeps the invariant: it adds no host function and keeps the host state. -/
theorem instantiateModule_hostInvariant {P : α → Prop} {store store' : Store α} {vm : ValidModule}
    {imports : List ExternVal} {inst : ModuleInst} (h : StoreHostInvariant P store)
    (hi : Link.instantiateModule store vm imports = .ok (store', inst)) :
    StoreHostInvariant P store' :=
  let same := Link.instantiateModule_same store vm imports hi
  ⟨fun fn hm => h.1 fn (same.2 fn hm), same.1 ▸ h.2⟩

/-- The first configuration of a call into a module instantiated over a NEAR
host environment whose functions preserve `P` satisfies the invariant. -/
theorem resolvedStart_hostInvariant {P : α → Prop} {env : HostEnv α} {host : α}
    {store store' : Store α} {imports : List ExternVal} {vm : ValidModule} {inst : ModuleInst}
    {limits : ExecLimits} {addr : Nat} {args : List Value} {c : Config α}
    (henv : ∀ fn ∈ env.funcs, fn.Preserves P)
    (halloc : env.allocate (Store.empty host) = (store, imports))
    (hinst : Link.instantiateModule store vm imports = .ok (store', inst))
    (hstart : Exec.startWasm store' limits addr args = some c) (hp : P host) :
    ConfigHostInvariant P c := by
  have h0 : StoreHostInvariant P store := by
    have := allocate_hostInvariant (P := P) (empty_storeHosts' host) henv
    rw [halloc] at this
    refine ⟨this, ?_⟩
    have hh := HostEnv.allocate_host (Store.empty host) env
    rw [halloc] at hh
    exact hh ▸ hp
  have h1 := instantiateModule_hostInvariant h0 hinst
  show Exec.StoreHosts _ c.store ∧ P c.store.host
  rw [Exec.startWasm_store hstart]
  exact h1

theorem empty_storeHosts {P : α → Prop} (host : α) :
    Exec.StoreHosts (Exec.HostFn.Preserves P) (Store.empty host) := by
  intro fn hm
  simp [Store.empty] at hm

end Wasm
