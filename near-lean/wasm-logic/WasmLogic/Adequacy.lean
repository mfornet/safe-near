import WasmLogic.Rules.Call
import Iris.ProgramLogic.Adequacy

/-!
# Adequacy: from the logic to `Wasm.Exec.run`

The one statement that makes proofs in the logic about the runtime:
`adequacy` says that if, from ownership of every cell of the initial store,
a function invocation satisfies `wpInvoke` with pure postconditions, then
every run of `Wasm.Exec.run` from `Exec.startWasm` that finishes returns
values satisfying the return postcondition, or traps only if the trap
postcondition holds. `Exec.run` is the function the spec testsuite runs.

A closed resource family `GF` provides the ghost state. Its first four slots
and their `GpreS` instances are taken from iris-lean's own
`Iris/Examples/ClosedProofs.lean` (Apache-2.0); the heap slot is ours.
-/

namespace WasmLogic

open Wasm Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProgramLogic.Language.Notation FromMathlib
  COFE HeapView Auth Std.LawfulSet

/-- The resource functors: iris-lean's four bookkeeping slots, then the heap. -/
noncomputable def GF (H : Type) : BundledGFunctors := fun n =>
  match n with
  | 0 => ⟨InvMapF, by infer_instance⟩
  | 1 => ⟨constOF CoPsetDisjL, by infer_instance⟩
  | 2 => ⟨constOF (DisjointLeibnizSet PosSet), by infer_instance⟩
  | 3 => ⟨AuthURF (constOF Credit), by infer_instance⟩
  | 4 => ⟨constOF (HeapView Loc (Agree (DiscreteO (Cell H))) HeapF), by infer_instance⟩
  | _ => ⟨constOF Unit, by infer_instance⟩

instance (H : Type) : WsatGpreS (GF H) where
  inv := { τ := 0, transp := by unfold GF; rfl }
  enabled := { τ := 1, transp := by unfold GF; rfl }
  disabled := { τ := 2, transp := by unfold GF; rfl }

instance (H : Type) : LcGpreS (GF H) where
  lc_elem := { τ := 3, transp := by unfold GF; rfl }

instance (H : Type) : InvGpreS (GF H) where
  toWsatGpreS := inferInstance
  toLcGpreS := inferInstance

instance (H : Type) : WasmGpreS H (GF H) where
  heap := ⟨{ τ := 4, transp := by unfold GF; rfl }⟩

/-- Adequacy of `WP` for the heap state interpretation: a `WP` proved from
ownership of every cell of the initial store holds of every finished run. -/
theorem wp_adequacy_heap {GF' : BundledGFunctors} [WasmGpreS H GF'] (e : Code H) (σ : Store H)
    (φ : Outcome → Prop)
    (hwp : ∀ [WasmGS H GF'], ownCells (GF := GF') (heapOf σ) ⊢
      WP e @ Stuckness.MaybeStuck; ⊤ {{ v, ⌜φ v⌝ }}) :
    adequate .MaybeStuck e σ (fun v _ => φ v) := by
  refine wp_adequacy (GF := GF') .MaybeStuck e σ φ ?_
  intro inst κs
  imod ghost_map_alloc (GF := GF') (heapOf σ) with ⟨%γ, Hauth, Hcells⟩
  letI wgs : WasmGS H GF' := { invGS := inst, heap := WasmGpreS.heap, name := γ }
  imodintro
  iexists (fun σ _ => ghost_map_auth γ (.own 1) (heapOf σ)), (fun _ => iprop(True))
  isplitl [Hauth]
  · iexact Hauth
  · iapply (@hwp wgs)
    iexact Hcells

/-- What a run of the machine can end in, as the language sees it. -/
theorem run_outcome (fuel : Nat) (σ : Store H) (limits : ExecLimits) (thread : Thread)
    (φ : Outcome → Prop)
    (had : adequate (Expr := Code H) .MaybeStuck (.running limits thread) σ (fun o _ => φ o)) :
    match Exec.run fuel (Code.config σ limits thread) with
    | .done vs _ => φ (.values vs)
    | .trap r _ => φ (.trap r)
    | .outOfFuel _ => True := by
  have steps := run_steps fuel σ limits thread
  cases h : Exec.run fuel (Code.config σ limits thread) with
  | done vs s =>
    rw [h] at steps
    exact had.adequate_result [] s (.values vs) steps
  | trap r s =>
    rw [h] at steps
    exact had.adequate_result [] s (.trap r) steps
  | outOfFuel _ => trivial

/-- Make an owned cell persistent: functions, instances and limits never
change, so the initial store's cells for them can be shared. -/
theorem pointsTo_persist {GF' : BundledGFunctors} [ι : WasmGS H GF'] (l : Loc) (c : Cell H) :
    pointsTo (GF := GF') l (.own 1) c ==∗ pointsTo (GF := GF') l .discard c := by
  iintro H
  iapply ghost_map_elem_persist $$ H

theorem mem_of_lookup {xs : List (Loc × Cell H)} {k : Loc} {c : Cell H} (h : xs.lookup k = some c) :
    (k, c) ∈ xs := by
  induction xs with
  | nil => simp at h
  | cons p xs ih =>
    obtain ⟨k', c'⟩ := p
    simp only [List.lookup_cons] at h
    split at h
    · rename_i hk
      cases h
      simp only [beq_iff_eq] at hk
      subst hk
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih h)

/-- Take a list of cells out of the ownership of a heap, dropping the rest:
how a proof picks the cells of the initial store it needs. -/
theorem ownCells_take {GF' : BundledGFunctors} [WasmGS H GF'] (m : HeapF (Cell H))
    (xs : List (Loc × Cell H)) (hnd : (xs.map (·.1)).Nodup)
    (h : ∀ p ∈ xs, get? m p.1 = some p.2) :
    ownCells (GF := GF') m ⊢ [∗list] p ∈ xs, p.1 ↦ₛ p.2 := by
  refine (BigSepM.bigSepM_subseteq (Φ := fun l c => iprop(l ↦ₛ c)) ?_).trans
    (ownCells_cellsOf xs hnd).1
  intro k c hk
  rw [get?_cellsOf] at hk
  exact h _ (mem_of_lookup hk)

theorem startWasm_eq {σ : Store H} {lim : ExecLimits} {a : Nat} {args : List Value} {c : Config H}
    (hc : Exec.startWasm σ lim a args = some c) :
    ∃ type inst code, σ.funcs[a]? = some (.wasm type inst code) ∧
      c = Code.config σ lim (calleeThread [] [] type inst code args) := by
  unfold Exec.startWasm at hc
  split at hc
  · rename_i type inst code hfn
    cases hc
    exact ⟨type, inst, code, hfn, rfl⟩
  · cases hc

/-- **Adequacy.** If, from ownership of every cell of the store, the
invocation of the Wasm function at `a` with `args` satisfies `wpInvoke` with
pure postconditions, then every run of `Exec.run` from `Exec.startWasm`
that finishes returns values satisfying `φ`, and traps only if `φtrap`. -/
theorem adequacy (σ : Store H) (lim : ExecLimits) (a : Nat) (args : List Value)
    (type : FuncType) (inst : Nat) (mi : ModuleInst) (code : Func)
    (hfn : σ.funcs[a]? = some (.wasm type inst code))
    (φ : List Value → Prop) (φtrap : Prop)
    (hwp : ∀ [WasmGS H (GF H)], ownCells (GF := GF H) (heapOf σ) ⊢ |==>
      (instPt inst mi ∗ wpInvoke lim 0 type inst mi code args
        { ret := fun rs => iprop(⌜φ rs⌝), trap := iprop(⌜φtrap⌝) }))
    (c : Config H) (hc : Exec.startWasm σ lim a args = some c) (fuel : Nat) :
    match Exec.run fuel c with
    | .done vs _ => φ vs
    | .trap _ _ => φtrap
    | .outOfFuel _ => True := by
  obtain ⟨type', inst', code', hfn', rfl⟩ := startWasm_eq hc
  rw [hfn] at hfn'
  cases hfn'
  have had := wp_adequacy_heap (GF' := GF H) (Code.running lim (calleeThread [] [] type inst code args))
    σ (fun o => match o with | .values vs => φ vs | .trap _ => φtrap) (by
      intro _
      iintro Hcells
      imod hwp $$ Hcells with ⟨#Hi, Hwp⟩
      unfold wpInvoke
      iapply Hwp $$ %(fun o => iprop(⌜match o with | .values vs => φ vs | .trap _ => φtrap⌝))
        %([] : List Value) %([] : List CallFrame) %rfl Hi
      isplit
      · iintro %rs %hrs
        simp only [retCode]
        iapply wp_finished
        ipureintro
        exact hrs
      · iintro %ht %r
        ipureintro
        exact ht)
  have := run_outcome fuel σ lim _ _ had
  revert this
  cases Exec.run fuel (Code.config σ lim (calleeThread [] [] type inst code args)) <;> simp

end WasmLogic
