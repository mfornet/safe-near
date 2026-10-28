import NearLogic.Language

/-!
# The metered heap, gas credits and the lifting lemma

The heap is WasmLogic's (`WasmLogic.lookup`), with the host state split in
two: `Loc.host` holds the host state with its gas counter and gas profile
erased, and `gasLoc` holds the counter and the profile. Every metered step
changes the gas cell and nothing else of the host, so an instruction that
does not touch the host needs the gas cell only.

Gas credits `credits C n` own the gas cell and say that `n` more gas can be
used without the counter's `used` passing the ceiling `C`, which is below
both of the counter's limits: the next `n` gas worth of charges succeed.
Credits are threaded through code, not split: a contract takes
`credits C (cost + R)` and gives back `credits C R`.

`mwp_lift_heap` is the one lifting lemma, as in WasmLogic, over `mnext`.
-/

namespace NearLogic

open Wasm Wasm.Near WasmLogic Iris Iris.BI Iris.Std Iris.Std.PartialMap Iris.ProgramLogic
  Iris.ProgramLogic.Language.Notation FromMathlib Std.LawfulSet

/-- The location of the gas counter and profile. -/
abbrev gasLoc : Loc := (10, 0, 0)

/-- The host state without its gas counter, its profile, and the copy of
`used` that metered host functions keep in the context. -/
def erase (h : NearState) : NearState :=
  { h with gas := {}, gasProfile := {}, actionProfile := [], context := { h.context with usedGas := 0 } }

/-- The host up to gas and the recorded proof: what a run with the gas limits
raised (`relax`, which records no proof) keeps of the original. -/
def eraseP (h : NearState) : NearState := { erase h with storageProofSize := none }

theorem eraseP_of_erase {h h' : NearState} (he : erase h = erase h') : eraseP h = eraseP h' := by
  unfold eraseP
  rw [he]

theorem eraseP_field {α : Type} {h h' : NearState} (he : eraseP h = eraseP h') (f : NearState → α)
    (hf : ∀ x, f (eraseP x) = f x) : f h = f h' := by
  rw [← hf h, ← hf h', he]

/-- The gas cell: a host state holding only a counter and the two profiles. -/
def gasCellOf (g : Near.GasCounter) (p : Near.GasProfile) (a : List (String × Nat)) : Cell NearState :=
  .host { (default : NearState) with gas := g, gasProfile := p, actionProfile := a }

/-- What a location holds in the metered view of a store. -/
def mlookup (σ : MStore) (l : Loc) : Option (Cell NearState) :=
  if l = gasLoc then some (gasCellOf σ.store.host.gas σ.store.host.gasProfile σ.store.host.actionProfile)
  else if l = Loc.host then some (.host (erase σ.store.host))
  else lookup σ.store l

/-- The metered view as a finite map. -/
def mheapOf (σ : MStore) : HeapF (Cell NearState) := ofFun (gasLoc :: storeKeys σ.store) (mlookup σ)

@[simp] theorem get?_mheapOf (σ : MStore) (l : Loc) : get? (mheapOf σ) l = mlookup σ l := by
  unfold mheapOf
  rw [get?_ofFun]
  split
  · rfl
  · rename_i hl
    unfold mlookup
    split
    · rename_i h; exact absurd (h ▸ List.mem_cons_self) hl
    · split
      · rename_i h
        subst h
        exact absurd (List.mem_cons_of_mem _ (mem_keys_of_lookup (lookup_host σ.store))) hl
      · cases h : lookup σ.store l with
        | none => rfl
        | some c => exact absurd (List.mem_cons_of_mem _ (mem_keys_of_lookup h)) hl

/-- Locations of the store proper: memories, globals, tables, functions,
instances and segments, not the host. -/
def isPlain (l : Loc) : Prop := l.1 < 9

theorem mlookup_plain (σ : MStore) {l : Loc} (h : isPlain l) : mlookup σ l = lookup σ.store l := by
  obtain ⟨k, a, i⟩ := l
  unfold isPlain at h
  simp only at h
  unfold mlookup
  rw [if_neg (by intro he; cases he; omega), if_neg (by intro he; cases he; omega)]

/-- A change of the host leaves the plain locations alone. -/
theorem lookup_plain_host (σ : Store NearState) (h : NearState) {l : Loc} (hl : isPlain l) :
    lookup { σ with host := h } l = lookup σ l :=
  lookup_with_host σ h l (by unfold isPlain at hl; omega)

/-- The ghost state for the metered language: WasmLogic's ghost names, with
the metered view as the state interpretation. -/
instance nearIrisGS [ι : WasmGS NearState GF] : IrisGS_gen .hasLC MCode GF where
  toStateInterp := ⟨fun σ _ _ _ => ghost_map_auth ι.name (.own 1) (mheapOf σ)⟩
  invGS := ι.invGS
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := let _ := ι.invGS; fupd_intro

section Assertions

variable {GF : BundledGFunctors} [ι : WasmGS NearState GF]

/-- The gas counter and profiles. -/
def gasPt (g : Near.GasCounter) (p : Near.GasProfile) (a : List (String × Nat)) : IProp GF :=
  gasLoc ↦ₛ gasCellOf g p a

/-- `n` gas can be used, and `used` stays within `C`, itself within both
limits. -/
def credits (C n : Nat) : IProp GF :=
  iprop(∃ (g : Near.GasCounter) (p : Near.GasProfile) (a : List (String × Nat)),
    gasPt g p a ∗ ⌜g.burnt ≤ g.used ∧ g.used + n ≤ C ∧ C ≤ g.maxBurnt ∧ C ≤ g.prepaid⌝)

/-- The host state, gas erased. -/
def mhostPt (h : NearState) : IProp GF := Loc.host ↦ₛ (.host (erase h) : Cell NearState)

theorem credits_mono {C n m : Nat} (h : m ≤ n) : credits (GF := GF) C n ⊢ credits C m := by
  unfold credits
  iintro ⟨%g, %p, %a, Hg, %hg⟩
  iexists g, p, a
  isplitl [Hg]
  · iexact Hg
  · ipureintro; omega

end Assertions

section Lifting

variable {GF : BundledGFunctors} [ι : WasmGS NearState GF]
variable {s : Stuckness} {E : CoPset} {Φ : Ending → IProp GF}

/-- What the state interpretation says about persistently seen cells. -/
theorem mseeList_lookup (σ : MStore) (Rd : List (Loc × Cell NearState)) :
    ⊢ ghost_map_auth (GF := GF) ι.name (.own 1) (mheapOf σ) -∗ seeList Rd -∗
      ⌜∀ p ∈ Rd, mlookup σ p.1 = some p.2⌝ := by
  induction Rd with
  | nil =>
    iintro _ _
    ipureintro
    simp
  | cons p Rd ih =>
    iintro Hσ ⟨Hp, HRd⟩
    ihave %h1 := ghost_map_lookup $$ Hσ Hp
    ihave %h2 := ih $$ Hσ HRd
    ipureintro
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · simpa using h1
    · exact h2 q hq

/-- The one lifting lemma, as WasmLogic's `wp_lift_heap`, for the metered step. -/
theorem mwp_lift_heap (cfg : WasmConfig) (lim : ExecLimits) (t : Thread)
    (Rd : List (Loc × Cell NearState))
    (P : HeapF (Cell NearState)) (Q : MStore → HeapF (Cell NearState)) (e' : MStore → MCode)
    (hstep : ∀ σ : MStore, (∀ p ∈ Rd, mlookup σ p.1 = some p.2) → P ⊆ mheapOf σ →
      (mnext σ cfg lim t).1 = e' σ ∧
        mheapOf (mnext σ cfg lim t).2 = PartialMap.union (Q σ) (PartialMap.difference (mheapOf σ) P))
    (hdisj : ∀ σ : MStore, (∀ p ∈ Rd, mlookup σ p.1 = some p.2) → P ⊆ mheapOf σ →
      Q σ ##ₘ PartialMap.difference (mheapOf σ) P) :
    seeList Rd ∗ ownCells P ∗
      ▷ (∀ σ : MStore, ⌜(∀ p ∈ Rd, mlookup σ p.1 = some p.2) ∧ P ⊆ mheapOf σ⌝ -∗
        ownCells (Q σ) -∗ WP (e' σ) @ s; E {{ Φ }})
      ⊢ WP (MCode.running cfg lim t) @ s; E {{ Φ }} := by
  iintro ⟨HRd, HP, Hwp⟩
  iapply wp_lift_step rfl
  iintro %σ %ns %obs %obs' %nt Hσ
  ihave %hRd := mseeList_lookup σ Rd $$ Hσ HRd
  ihave %hP := ghost_map_lookup_big (dq' := .own 1) P $$ Hσ HP
  obtain ⟨he, hheap⟩ := hstep σ hRd hP
  have hQ := hdisj σ hRd hP
  iapply fupd_mask_intro empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact running_reducible cfg lim t σ
    · trivial
  iintro !> %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨-, rfl, rfl, rfl⟩ := step_det Hstep
  imod ghost_map_delete_big (γ := ι.name) P $$ Hσ HP with Hσ
  ihave Hins := ghost_map_insert_big (γ := ι.name) (m := PartialMap.difference (mheapOf σ) P) (Q σ) hQ
  imod Hins $$ Hσ with ⟨Hσ, HQ⟩
  imod Hclose
  imodintro
  rw [he]
  have key : (ghost_map_auth ι.name (.own 1) (PartialMap.union (Q σ) (PartialMap.difference
      (mheapOf σ) P)) : IProp GF) ⊢ stateInterp (mnext σ cfg lim t).2 (ns + 1) obs' (nt + 0) := by
    rw [← hheap]; exact .rfl
  isplitl [Hσ]
  · iapply key $$ Hσ
  isplitl [Hwp HQ]
  · iapply Hwp $$ %σ %⟨hRd, hP⟩ HQ
  · iapply BigSepL.bigSepL_nil.2
    itrivial

/-- The lifting lemma over lists of cells, as WasmLogic's `wp_lift_dep`. -/
theorem mwp_lift_dep (cfg : WasmConfig) (lim : ExecLimits) (t : Thread)
    (Rd P : List (Loc × Cell NearState))
    (Q : MStore → List (Loc × Cell NearState)) (e' : MStore → MCode)
    (hP : (P.map (·.1)).Nodup) (hQ : ∀ σ, ((Q σ).map (·.1)).Nodup)
    (hstep : ∀ σ : MStore, (∀ p ∈ Rd, mlookup σ p.1 = some p.2) →
      (∀ p ∈ P, mlookup σ p.1 = some p.2) →
      (mnext σ cfg lim t).1 = e' σ ∧ ∀ l, mlookup (mnext σ cfg lim t).2 l =
        ((Q σ).lookup l).or (if (P.lookup l).isSome then none else mlookup σ l))
    (hfresh : ∀ σ : MStore, (∀ p ∈ Rd, mlookup σ p.1 = some p.2) →
      (∀ p ∈ P, mlookup σ p.1 = some p.2) →
      ∀ l, ((Q σ).lookup l).isSome → P.lookup l = none → mlookup σ l = none) :
    seeList Rd ∗ ([∗list] p ∈ P, p.1 ↦ₛ p.2) ∗
      ▷ (∀ σ : MStore, ⌜(∀ p ∈ Rd, mlookup σ p.1 = some p.2) ∧
          (∀ p ∈ P, mlookup σ p.1 = some p.2)⌝ -∗
        ([∗list] p ∈ Q σ, p.1 ↦ₛ p.2) -∗ WP (e' σ) @ s; E {{ Φ }})
      ⊢ WP (MCode.running cfg lim t) @ s; E {{ Φ }} := by
  have hsub : ∀ σ : MStore, cellsOf P ⊆ mheapOf σ → ∀ p ∈ P, mlookup σ p.1 = some p.2 := by
    intro σ h p hp
    have := h p.1 p.2 (by rw [get?_cellsOf]; exact lookup_of_mem hP hp)
    simpa using this
  iintro ⟨HRd, HP, Hwp⟩
  iapply mwp_lift_heap cfg lim t Rd (cellsOf P) (fun σ => cellsOf (Q σ)) e'
  · intro σ hRd hPs
    obtain ⟨he, hl⟩ := hstep σ hRd (hsub σ hPs)
    refine ⟨he, LawfulPartialMap.equiv_iff_eq.mp fun l => ?_⟩
    simp only [get?_mheapOf, PartialMap.union, LawfulPartialMap.get?_merge, PartialMap.difference,
      LawfulPartialMap.get?_differenceWith, get?_cellsOf, hl]
    cases (Q σ).lookup l <;> cases hp : P.lookup l <;> cases mlookup σ l <;> simp [Option.merge]
  · intro σ hRd hPs
    refine (PartialMap.disjoint_iff _ _).mpr fun l => ?_
    simp only [get?_mheapOf, PartialMap.difference, LawfulPartialMap.get?_differenceWith,
      get?_cellsOf]
    cases hq : (Q σ).lookup l with
    | none => exact .inl rfl
    | some c =>
      right
      cases hp : P.lookup l with
      | some c' => simp
      | none => simp [hfresh σ hRd (hsub σ hPs) l (by simp [hq]) hp]
  isplitl [HRd]
  · iexact HRd
  isplitl [HP]
  · iapply (ownCells_cellsOf P hP).2 $$ HP
  · inext
    iintro %σ %⟨hRd, hPs⟩ HQ
    iapply Hwp $$ %σ %⟨hRd, hsub σ hPs⟩
    iapply (ownCells_cellsOf (Q σ) (hQ σ)).1 $$ HQ

/-- A finished thread has its postcondition. -/
theorem mwp_finished (e : Ending) : Φ e ⊢ WP (MCode.finished e) @ s; E {{ Φ }} :=
  wp_value' (Expr := MCode) (v := e)

end Lifting

end NearLogic
