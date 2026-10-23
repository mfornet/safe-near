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

/-- Ownership of cells `cs`, distinct locations, with `R cs`: how a
postcondition says what the final store holds. -/
abbrev cellsSat {GF' : BundledGFunctors} [WasmGS H GF'] (R : List (Loc × Cell H) → Prop) : IProp GF' :=
  iprop(∃ cs, ⌜R cs ∧ (cs.map (·.1)).Nodup⌝ ∗ [∗list] p ∈ cs, p.1 ↦ₛ p.2)

/-- Adequacy with cells: if from ownership of every cell of the initial
store the program satisfies `WP` with a postcondition `⌜φ o⌝` and cells with
`R o`, then every finished run ends in an outcome `o` with `φ o` and a store
holding cells `cs` with `R o cs`. This is the root statement;
`wp_adequacy_heap`, `adequacy_cells` and `adequacy` are corollaries. -/
theorem wp_adequacy_cells {GF' : BundledGFunctors} [WasmGpreS H GF'] (e : Code H) (σ : Store H)
    (φ : Outcome → Prop) (R : Outcome → List (Loc × Cell H) → Prop)
    (hwp : ∀ [WasmGS H GF'], ownCells (GF := GF') (heapOf σ) ⊢
      WP e @ Stuckness.MaybeStuck; ⊤ {{ o, ⌜φ o⌝ ∗ cellsSat (R o) }}) :
    adequate .MaybeStuck e σ
      (fun o σ' => φ o ∧ ∃ cs, R o cs ∧ ∀ p ∈ cs, lookup σ' p.1 = some p.2) := by
  refine (adequate_alt _ _ _ _).mpr ?_
  intro t2 σ2 hreach
  refine ⟨fun v2 t2' heq => ?_, fun _ h => by cases h⟩
  subst heq
  obtain ⟨n, κs, hsteps⟩ := (Language.erasedStep_nSteps _ _).mp hreach
  apply wp_strong_adequacy_gen (GF := GF') (hlc := .hasLC) .MaybeStuck (Hsteps := hsteps)
    (numLaters := fun _ => 0)
  iintro %Hinv
  imod ghost_map_alloc (GF := GF') (heapOf σ) with ⟨%γ, Hauth, Hcells⟩
  letI wgs : WasmGS H GF' := { invGS := Hinv, heap := WasmGpreS.heap, name := γ }
  ihave Hwp := (@hwp wgs) $$ Hcells
  iexists (fun σ _ _ _ => ghost_map_auth γ (.own 1) (heapOf σ)),
    [fun o => iprop(⌜φ o⌝ ∗ cellsSat (R o))], (fun _ => iprop(True)),
    (fun _ _ _ _ => fupd_intro)
  dsimp only
  imodintro
  iframe
  isplitl
  · iapply BigSepL2.bigSepL2_nil; itrivial
  iintro %es' %_ %Heq %hlen %_ Hst Hpost _
  icases BigSepL2.bigSepL2_cons_inv_right $$ Hpost with ⟨%e', %es'', %Heq', Hpost, H⟩
  subst Heq'
  icases BigSepL2.bigSepL2_nil_inv_right $$ H with %Heq''
  subst Heq''
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at Heq
  obtain ⟨rfl, -⟩ := Heq
  simp only [ToVal.toVal_coe, Option.elim_some]
  icases Hpost with ⟨%hφ, %cs, %⟨hR, hnd⟩, Hc⟩
  ihave Hc := (ownCells_cellsOf (GF := GF') cs hnd).2 $$ Hc
  ihave %hsub := ghost_map_lookup_big (cellsOf cs) $$ Hst Hc
  iapply fupd_mask_intro_discard empty_subset
  ipureintro
  refine ⟨hφ, cs, hR, fun p hp => ?_⟩
  have := hsub p.1 p.2 (by rw [get?_cellsOf]; exact lookup_of_mem hnd hp)
  simpa [get?_heapOf] using this

/-- Adequacy of `WP` for the heap state interpretation with a pure
postcondition: a `WP` proved from ownership of every cell of the initial
store holds of every finished run. -/
theorem wp_adequacy_heap {GF' : BundledGFunctors} [WasmGpreS H GF'] (e : Code H) (σ : Store H)
    (φ : Outcome → Prop)
    (hwp : ∀ [WasmGS H GF'], ownCells (GF := GF') (heapOf σ) ⊢
      WP e @ Stuckness.MaybeStuck; ⊤ {{ v, ⌜φ v⌝ }}) :
    adequate .MaybeStuck e σ (fun v _ => φ v) := by
  have h := wp_adequacy_cells (GF' := GF') e σ φ (fun _ _ => True) (by
    intro _
    refine hwp.trans (wp_mono fun _ => ?_)
    iintro H
    isplitl [H]
    · iexact H
    · iexists []
      isplitr
      · ipureintro; exact ⟨trivial, List.nodup_nil⟩
      · iapply BigSepL.bigSepL_nil.2; iempintro)
  exact ⟨fun t2 σ2 v2 hr => (h.adequate_result t2 σ2 v2 hr).1,
    fun t2 σ2 e2 hs hr hm => h.adequate_not_stuck t2 σ2 e2 hs hr hm⟩

/-- What a run of the machine can end in, as the language sees it. -/
theorem run_outcome (fuel : Nat) (σ : Store H) (limits : ExecLimits) (thread : Thread)
    (φ : Outcome → Store H → Prop)
    (had : adequate (Expr := Code H) .MaybeStuck (.running limits thread) σ φ) :
    match Exec.run fuel (Code.config σ limits thread) with
    | .done vs σ' => φ (.values vs) σ'
    | .trap r σ' => φ (.trap r) σ'
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

/-- Weaken a function's postcondition. -/
theorem wpInvoke_mono {GF' : BundledGFunctors} [WasmGS H GF'] {lim : ExecLimits} {d : Nat}
    {type : FuncType} {inst : Nat} {mi : ModuleInst} {code : Func} {args : List Value}
    {Φf Φf' : FunPost GF'} (hret : ∀ rs, Φf.ret rs ⊢ Φf'.ret rs) (htrap : Φf.trap ⊢ Φf'.trap) :
    wpInvoke (H := H) lim d type inst mi code args Φf ⊢ wpInvoke lim d type inst mi code args Φf' := by
  unfold wpInvoke
  iintro Hwp %Ψ %bs %fs %hfs #Hi HK
  iapply Hwp $$ %Ψ %bs %fs %hfs Hi
  isplit
  · iintro %rs Hr
    icases HK with ⟨HK, -⟩
    iapply HK
    iapply hret $$ Hr
  · iintro Ht
    icases HK with ⟨-, HK⟩
    iapply HK
    iapply htrap $$ Ht

/-- **Adequacy.** If, from ownership of every cell of the store, the
invocation of the Wasm function at `a` with `args` satisfies `wpInvoke`,
returning `rs` with `φ rs` and cells with `R rs`, and trapping only with
`φtrap`, then every run of `Exec.run` from `Exec.startWasm` that finishes
returns values `vs` with `φ vs` in a store holding cells `cs` with `R vs cs`,
and traps only if `φtrap`. -/
theorem adequacy_cells (σ : Store H) (lim : ExecLimits) (a : Nat) (args : List Value)
    (type : FuncType) (inst : Nat) (mi : ModuleInst) (code : Func)
    (hfn : σ.funcs[a]? = some (.wasm type inst code))
    (φ : List Value → Prop) (φtrap : Prop) (R : List Value → List (Loc × Cell H) → Prop)
    (hwp : ∀ [WasmGS H (GF H)], ownCells (GF := GF H) (heapOf σ) ⊢ |==>
      (instPt inst mi ∗ wpInvoke lim 0 type inst mi code args
        { ret := fun rs => iprop(⌜φ rs⌝ ∗ cellsSat (R rs)), trap := iprop(⌜φtrap⌝) }))
    (c : Config H) (hc : Exec.startWasm σ lim a args = some c) (fuel : Nat) :
    match Exec.run fuel c with
    | .done vs σ' => φ vs ∧ ∃ cs, R vs cs ∧ ∀ p ∈ cs, lookup σ' p.1 = some p.2
    | .trap _ _ => φtrap
    | .outOfFuel _ => True := by
  obtain ⟨type', inst', code', hfn', rfl⟩ := startWasm_eq hc
  rw [hfn] at hfn'
  cases hfn'
  let φ' : Outcome → Prop := fun o => match o with | .values vs => φ vs | .trap _ => φtrap
  let R' : Outcome → List (Loc × Cell H) → Prop := fun o cs =>
    match o with | .values vs => R vs cs | .trap _ => True
  have had := wp_adequacy_cells (GF' := GF H) (Code.running lim (calleeThread [] [] type inst code args))
    σ φ' R' (by
      intro _
      let Ψ : Outcome → IProp (GF H) := fun o => iprop(⌜φ' o⌝ ∗ cellsSat (R' o))
      show _ ⊢ WP _ @ _; _ {{ Ψ }}
      iintro Hcells
      imod hwp $$ Hcells with ⟨#Hi, Hwp⟩
      unfold wpInvoke
      iapply Hwp $$ %Ψ %([] : List Value) %([] : List CallFrame) %rfl Hi
      isplit
      · iintro %rs ⟨%hrs, Hc⟩
        simp only [retCode]
        iapply wp_finished
        isplitr
        · ipureintro; exact hrs
        · iexact Hc
      · iintro %ht %r
        isplitr
        · ipureintro; exact ht
        · iexists []
          isplitr
          · ipureintro; exact ⟨trivial, List.nodup_nil⟩
          · iapply BigSepL.bigSepL_nil.2; iempintro)
  have := run_outcome fuel σ lim _ _ had
  revert this
  cases Exec.run fuel (Code.config σ lim (calleeThread [] [] type inst code args)) <;>
    exact fun h => by first | exact h | exact h.1 | trivial

/-- Adequacy with pure postconditions: every run of `Exec.run` from
`Exec.startWasm` that finishes returns values satisfying `φ`, and traps
only if `φtrap`. -/
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
  have h := adequacy_cells σ lim a args type inst mi code hfn φ φtrap (fun _ _ => True) (by
      intro _
      iintro Hcells
      imod hwp $$ Hcells with ⟨Hi, Hwp⟩
      imodintro
      isplitl [Hi]
      · iexact Hi
      have hm : ∀ rs, (iprop(⌜φ rs⌝) : IProp (GF H)) ⊢
          iprop(⌜φ rs⌝ ∗ cellsSat (H := H) (fun _ => True)) := fun _ => by
        iintro H
        isplitl [H]
        · iexact H
        · iexists []
          isplitr
          · ipureintro; exact ⟨trivial, List.nodup_nil⟩
          · iapply BigSepL.bigSepL_nil.2; iempintro
      iapply (wpInvoke_mono (Φf := { ret := fun rs => iprop(⌜φ rs⌝), trap := iprop(⌜φtrap⌝) })
        (Φf' := { ret := fun rs => iprop(⌜φ rs⌝ ∗ cellsSat (H := H) (fun _ => True)),
                  trap := iprop(⌜φtrap⌝) }) hm .rfl) $$ Hwp) c hc fuel
  revert h
  cases Exec.run fuel c <;> exact fun h => by first | exact h.1 | exact h | trivial

end WasmLogic
