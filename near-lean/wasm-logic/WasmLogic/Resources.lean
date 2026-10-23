import WasmLogic.Heap
import WasmLogic.Language
import Iris.Instances.Lib.GhostMap
import Iris.ProgramLogic.WeakestPre
import Iris.ProgramLogic.Lifting

/-!
# Resources: owning pieces of the store

The state interpretation owns the heap of the store (`heapOf σ`) as the
authoritative part of a ghost map; a points-to assertion owns one cell of it.
`wp_lift_heap` is the one lifting lemma every instruction rule is derived
from: if the cells a thread step reads and writes are owned, the step can be
taken, and the owned cells are replaced by the ones the step leaves.

Notation follows Iris-Wasm (`iris_wp_def.v`): `↦[wm]` a byte, `↦[wms]` a byte
list, `↦[i32]` a little-endian word, `↦[wmlength]` a memory's length in bytes,
`↪[wmlimit]` its maximum, `↦[wg]` a global, `↦[wt]` a table entry,
`↪[wf]` a function, `↪[inst]` a module instance. Functions, instances and
limits never change while code runs, so their assertions are persistent.
-/

namespace WasmLogic

open Wasm Iris Iris.BI Iris.Std Iris.Std.PartialMap Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
  FromMathlib Std.LawfulSet

/-- What adequacy needs before the ghost state exists. -/
class WasmGpreS (H : Type) (GF : BundledGFunctors) extends InvGpreS GF where
  heap : GhostMapG GF Loc (Cell H) HeapF

attribute [reducible, instance] WasmGpreS.heap

/-- The ghost state of the logic: invariants, and the store's heap. -/
class WasmGS (H : outParam Type) (GF : BundledGFunctors) where
  [invGS : InvGS GF]
  [heap : GhostMapG GF Loc (Cell H) HeapF]
  name : GName

attribute [reducible, instance] WasmGS.heap

instance wasmIrisGS [ι : WasmGS H GF] : IrisGS_gen .hasLC (Code H) GF where
  toStateInterp := ⟨fun σ _ _ _ => ghost_map_auth ι.name (.own 1) (heapOf σ)⟩
  invGS := ι.invGS
  numLatersPerStep _ := 0
  forkPost _ := iprop(True)
  stateInterp_mono _ _ _ _ := let _ := ι.invGS; fupd_intro

section Assertions

variable {H : Type} {GF : BundledGFunctors} [ι : WasmGS H GF]

/-- Ownership of one cell of the store. -/
abbrev pointsTo (l : Loc) (dq : DFrac) (c : Cell H) : IProp GF := ghost_map_elem ι.name dq l c

notation:50 l:50 " ↦ₛ{" dq "} " c:50 => pointsTo l dq c
notation:50 l:50 " ↦ₛ " c:50 => pointsTo l (DFrac.own 1) c
notation:50 l:50 " ↦ₛ□ " c:50 => pointsTo l DFrac.discard c

instance pointsTo_persistent (l : Loc) (c : Cell H) :
    Persistent (pointsTo (GF := GF) l .discard c) := by
  unfold pointsTo ghost_map_elem; infer_instance

instance pointsTo_timeless (l : Loc) (dq : DFrac) (c : Cell H) :
    Timeless (pointsTo (GF := GF) l dq c) := by
  unfold pointsTo ghost_map_elem; infer_instance

/-- Byte `i` of memory `n`. -/
def memByte (n i : Nat) (b : UInt8) : IProp GF := Loc.byte n i ↦ₛ (.byte b : Cell H)

/-- Bytes `bs` from offset `i` of memory `n`, as cells. -/
def byteCells (n i : Nat) : List UInt8 → List (Loc × Cell H)
  | [] => []
  | b :: bs => (Loc.byte n i, .byte b) :: byteCells n (i + 1) bs

/-- Bytes `bs` from offset `i` of memory `n`. -/
def memBytes (n i : Nat) (bs : List UInt8) : IProp GF :=
  [∗list] p ∈ byteCells (H := H) n i bs, p.1 ↦ₛ p.2

/-- The little-endian bytes of a 32-bit word. -/
def bytes32 (v : UInt32) : List UInt8 :=
  (List.range 4).map fun k => UInt8.ofNat (v.toNat >>> (8 * k))

/-- The little-endian bytes of a 64-bit word. -/
def bytes64 (v : UInt64) : List UInt8 :=
  (List.range 8).map fun k => UInt8.ofNat (v.toNat >>> (8 * k))

def memLength (n len : Nat) : IProp GF := Loc.memLength n ↦ₛ (.memLength len : Cell H)
def memLimit (n : Nat) (mx : Option Nat) : IProp GF := Loc.memLimit n ↦ₛ□ (.memLimit mx : Cell H)
def globalPt (g : Nat) (gi : GlobalInst) : IProp GF := Loc.global g ↦ₛ (.global gi : Cell H)
def tablePt (t i : Nat) (r : Ref) : IProp GF := Loc.tableElem t i ↦ₛ (.ref r : Cell H)
def funcPt (a : Nat) (f : FuncInst H) : IProp GF := Loc.func a ↦ₛ□ (.func f : Cell H)
def instPt (i : Nat) (m : ModuleInst) : IProp GF := Loc.inst i ↦ₛ□ (.inst m : Cell H)
def hostPt (h : H) : IProp GF := Loc.host ↦ₛ (.host h : Cell H)

instance (n : Nat) (mx : Option Nat) : Persistent (memLimit (H := H) (GF := GF) n mx) := by
  unfold memLimit; infer_instance
instance (a : Nat) (f : FuncInst H) : Persistent (funcPt (GF := GF) a f) := by
  unfold funcPt; infer_instance
instance (i : Nat) (m : ModuleInst) : Persistent (instPt (H := H) (GF := GF) i m) := by
  unfold instPt; infer_instance

end Assertions

notation:50 n:50 " ↦[wm][ " i " ] " b:50 => memByte n i b
notation:50 n:50 " ↦[wms][ " i " ] " bs:50 => memBytes n i bs
notation:50 n:50 " ↦[i32][ " i " ] " v:50 => memBytes n i (bytes32 v)
notation:50 n:50 " ↦[wmlength] " len:50 => memLength n len
notation:50 n:50 " ↪[wmlimit] " mx:50 => memLimit n mx
notation:50 g:50 " ↦[wg] " gi:50 => globalPt g gi
notation:50 t:50 " ↦[wt][ " i " ] " r:50 => tablePt t i r
notation:50 a:50 " ↪[wf] " f:50 => funcPt a f
notation:50 i:50 " ↪[inst] " m:50 => instPt i m
notation:50 "↦[host] " h:50 => hostPt h

section Lifting

variable {H : Type} {GF : BundledGFunctors} [ι : WasmGS H GF]
variable {s : Stuckness} {E : CoPset} {Φ : Outcome → IProp GF}

/-- The cells of a map, owned. -/
abbrev ownCells (P : HeapF (Cell H)) : IProp GF := [∗map] l ↦ c ∈ P, l ↦ₛ c

/-- Read-only cells, as a list: duplicates are harmless. -/
abbrev seeList (Rd : List (Loc × Cell H)) : IProp GF := [∗list] p ∈ Rd, p.1 ↦ₛ□ p.2

theorem seeList_cons (p : Loc × Cell H) (Rd : List (Loc × Cell H)) :
    seeList (GF := GF) (p :: Rd) ⊣⊢ p.1 ↦ₛ□ p.2 ∗ seeList Rd := .rfl

/-- What the state interpretation says about persistently seen cells. -/
theorem seeList_lookup (σ : Store H) (Rd : List (Loc × Cell H)) :
    ⊢ ghost_map_auth (GF := GF) ι.name (.own 1) (heapOf σ) -∗ seeList Rd -∗
      ⌜∀ p ∈ Rd, lookup σ p.1 = some p.2⌝ := by
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

/-- The one lifting lemma. A running thread whose next step, from any store
`σ` containing the read-only cells `Rd` and the owned cells `P`, reaches
`e' σ` and replaces `P` by `Q σ` in the heap. What the step does may depend
on the store beyond the owned cells (as `memory.grow` depends on the
memory's limit); the continuation is given the store's facts. -/
theorem wp_lift_heap (lim : ExecLimits) (t : Thread) (Rd : List (Loc × Cell H))
    (P : HeapF (Cell H)) (Q : Store H → HeapF (Cell H)) (e' : Store H → Code H)
    (hstep : ∀ σ : Store H, (∀ p ∈ Rd, lookup σ p.1 = some p.2) → P ⊆ heapOf σ →
      (next σ lim t).1 = e' σ ∧
        heapOf (next σ lim t).2 = PartialMap.union (Q σ) (PartialMap.difference (heapOf σ) P))
    (hdisj : ∀ σ : Store H, (∀ p ∈ Rd, lookup σ p.1 = some p.2) → P ⊆ heapOf σ →
      Q σ ##ₘ PartialMap.difference (heapOf σ) P) :
    seeList Rd ∗ ownCells P ∗
      ▷ (∀ σ : Store H, ⌜(∀ p ∈ Rd, lookup σ p.1 = some p.2) ∧ P ⊆ heapOf σ⌝ -∗
        ownCells (Q σ) -∗ WP (e' σ) @ s; E {{ Φ }})
      ⊢ WP (Code.running (H := H) lim t) @ s; E {{ Φ }} := by
  iintro ⟨HRd, HP, Hwp⟩
  iapply wp_lift_step rfl
  iintro %σ %ns %obs %obs' %nt Hσ
  ihave %hRd := seeList_lookup σ Rd $$ Hσ HRd
  ihave %hP := ghost_map_lookup_big (dq' := .own 1) P $$ Hσ HP
  obtain ⟨he, hheap⟩ := hstep σ hRd hP
  have hQ := hdisj σ hRd hP
  iapply fupd_mask_intro empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s
    · exact running_reducible lim t σ
    · trivial
  iintro !> %e₂ %σ₂ %eₜ %Hstep _
  obtain ⟨-, rfl, rfl, rfl⟩ := step_det Hstep
  imod ghost_map_delete_big (γ := ι.name) P $$ Hσ HP with Hσ
  ihave Hins := ghost_map_insert_big (γ := ι.name) (m := PartialMap.difference (heapOf σ) P) (Q σ) hQ
  imod Hins $$ Hσ with ⟨Hσ, HQ⟩
  imod Hclose
  imodintro
  rw [he]
  have key : (ghost_map_auth ι.name (.own 1) (PartialMap.union (Q σ) (PartialMap.difference
      (heapOf σ) P)) : IProp GF) ⊢ stateInterp (next σ lim t).2 (ns + 1) obs' (nt + 0) := by
    rw [← hheap]; exact .rfl
  isplitl [Hσ]
  · iapply key $$ Hσ
  isplitl [Hwp HQ]
  · iapply Hwp $$ %σ %⟨hRd, hP⟩ HQ
  · iapply BigSepL.bigSepL_nil.2
    itrivial

/-! ## Owned cells as lists -/

/-- A finite map from a list of cells; the first binding of a location wins. -/
def cellsOf (xs : List (Loc × Cell H)) : HeapF (Cell H) :=
  xs.foldr (fun p m => PartialMap.insert m p.1 p.2) ∅

theorem get?_cellsOf (xs : List (Loc × Cell H)) (l : Loc) : get? (cellsOf xs) l = xs.lookup l := by
  induction xs with
  | nil => exact LawfulPartialMap.get?_empty l
  | cons p xs ih =>
    obtain ⟨k, c⟩ := p
    simp only [cellsOf, List.foldr_cons, List.lookup_cons] at ih ⊢
    by_cases h : k = l
    · subst h; simp [LawfulPartialMap.get?_insert_eq rfl]
    · rw [LawfulPartialMap.get?_insert_ne h, ih]
      have : (l == k) = false := by simpa using Ne.symm h
      simp [this]

theorem lookup_cons_pair (k l : Loc) (c : Cell H) (xs : List (Loc × Cell H)) :
    ((k, c) :: xs).lookup l = if l = k then some c else xs.lookup l := by
  by_cases h : l = k
  · subst h; simp [List.lookup]
  · have : (l == k) = false := by simpa using h
    simp [List.lookup, this, h]

theorem lookup_of_mem {xs : List (Loc × Cell H)} (hnd : (xs.map (·.1)).Nodup) {p : Loc × Cell H}
    (hp : p ∈ xs) : xs.lookup p.1 = some p.2 := by
  induction xs with
  | nil => cases hp
  | cons q xs ih =>
    obtain ⟨k, c⟩ := q
    obtain ⟨hq, hnd⟩ := List.nodup_cons.mp hnd
    rw [lookup_cons_pair]
    rcases List.mem_cons.mp hp with rfl | hp
    · simp
    · have hne : p.1 ≠ k := fun h => hq (h ▸ List.mem_map_of_mem (f := (·.1)) hp)
      simp [hne, ih hnd hp]

theorem lookup_eq_none_of_not_mem {xs : List (Loc × Cell H)} {l : Loc}
    (h : l ∉ xs.map (·.1)) : xs.lookup l = none := by
  induction xs with
  | nil => rfl
  | cons q xs ih =>
    obtain ⟨k, c⟩ := q
    rw [lookup_cons_pair]
    have hne : l ≠ k := fun he => h (by simp [he])
    simp only [hne, ite_false]
    exact ih (fun h' => h (List.mem_cons_of_mem _ h'))

theorem ownCells_cellsOf (xs : List (Loc × Cell H)) (hnd : (xs.map (·.1)).Nodup) :
    ownCells (GF := GF) (cellsOf xs) ⊣⊢ [∗list] p ∈ xs, p.1 ↦ₛ p.2 := by
  induction xs with
  | nil =>
    simp only [cellsOf, List.foldr_nil]
    exact BigSepM.bigSepM_empty.trans BigSepL.bigSepL_nil.symm
  | cons p xs ih =>
    obtain ⟨hp, hnd⟩ := List.nodup_cons.mp hnd
    have hnone : get? (cellsOf xs) p.1 = none := by
      rw [get?_cellsOf]; exact lookup_eq_none_of_not_mem hp
    simp only [ownCells, cellsOf, List.foldr_cons] at ih ⊢
    have hins := BigSepM.bigSepM_insert (PROP := IProp GF) (M := HeapF)
      (Φ := fun l c => iprop(l ↦ₛ c)) (x := p.2) hnone
    refine ⟨hins.1.trans (sep_mono .rfl (ih hnd).1), (sep_mono .rfl (ih hnd).2).trans hins.2⟩

/-- The lifting lemma over lists of cells: `Rd` read persistently, `P` owned
before the step and replaced by `Q σ` after it, the step reaching `e' σ`. -/
theorem wp_lift_dep (lim : ExecLimits) (t : Thread) (Rd P : List (Loc × Cell H))
    (Q : Store H → List (Loc × Cell H)) (e' : Store H → Code H)
    (hP : (P.map (·.1)).Nodup) (hQ : ∀ σ, ((Q σ).map (·.1)).Nodup)
    (hstep : ∀ σ : Store H, (∀ p ∈ Rd, lookup σ p.1 = some p.2) →
      (∀ p ∈ P, lookup σ p.1 = some p.2) →
      (next σ lim t).1 = e' σ ∧ ∀ l, lookup (next σ lim t).2 l =
        ((Q σ).lookup l).or (if (P.lookup l).isSome then none else lookup σ l))
    (hfresh : ∀ σ : Store H, (∀ p ∈ Rd, lookup σ p.1 = some p.2) →
      (∀ p ∈ P, lookup σ p.1 = some p.2) →
      ∀ l, ((Q σ).lookup l).isSome → P.lookup l = none → lookup σ l = none) :
    seeList Rd ∗ ([∗list] p ∈ P, p.1 ↦ₛ p.2) ∗
      ▷ (∀ σ : Store H, ⌜(∀ p ∈ Rd, lookup σ p.1 = some p.2) ∧ (∀ p ∈ P, lookup σ p.1 = some p.2)⌝ -∗
        ([∗list] p ∈ Q σ, p.1 ↦ₛ p.2) -∗ WP (e' σ) @ s; E {{ Φ }})
      ⊢ WP (Code.running (H := H) lim t) @ s; E {{ Φ }} := by
  have hsub : ∀ σ : Store H, cellsOf P ⊆ heapOf σ → ∀ p ∈ P, lookup σ p.1 = some p.2 := by
    intro σ h p hp
    have := h p.1 p.2 (by rw [get?_cellsOf]; exact lookup_of_mem hP hp)
    simpa using this
  iintro ⟨HRd, HP, Hwp⟩
  iapply wp_lift_heap lim t Rd (cellsOf P) (fun σ => cellsOf (Q σ)) e'
  · intro σ hRd hPs
    obtain ⟨he, hl⟩ := hstep σ hRd (hsub σ hPs)
    refine ⟨he, LawfulPartialMap.equiv_iff_eq.mp fun l => ?_⟩
    simp only [get?_heapOf, PartialMap.union, LawfulPartialMap.get?_merge, PartialMap.difference,
      LawfulPartialMap.get?_differenceWith, get?_cellsOf, hl]
    cases (Q σ).lookup l <;> cases hp : P.lookup l <;> cases lookup σ l <;> simp [Option.merge]
  · intro σ hRd hPs
    refine (PartialMap.disjoint_iff _ _).mpr fun l => ?_
    simp only [get?_heapOf, PartialMap.difference, LawfulPartialMap.get?_differenceWith,
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

/-- The lifting lemma over lists of cells, when the step's outcome does not
depend on the store beyond the cells. -/
theorem wp_lift (lim : ExecLimits) (t : Thread) (Rd P Q : List (Loc × Cell H)) (e' : Code H)
    (hP : (P.map (·.1)).Nodup) (hQ : (Q.map (·.1)).Nodup)
    (hstep : ∀ σ : Store H, (∀ p ∈ Rd, lookup σ p.1 = some p.2) →
      (∀ p ∈ P, lookup σ p.1 = some p.2) →
      (next σ lim t).1 = e' ∧ ∀ l, lookup (next σ lim t).2 l =
        (Q.lookup l).or (if (P.lookup l).isSome then none else lookup σ l))
    (hfresh : ∀ σ : Store H, (∀ p ∈ Rd, lookup σ p.1 = some p.2) →
      (∀ p ∈ P, lookup σ p.1 = some p.2) →
      ∀ l, (Q.lookup l).isSome → P.lookup l = none → lookup σ l = none) :
    seeList Rd ∗ ([∗list] p ∈ P, p.1 ↦ₛ p.2) ∗ ▷ (([∗list] p ∈ Q, p.1 ↦ₛ p.2) -∗ WP e' @ s; E {{ Φ }})
      ⊢ WP (Code.running (H := H) lim t) @ s; E {{ Φ }} := by
  iintro ⟨HRd, HP, Hwp⟩
  iapply wp_lift_dep lim t Rd P (fun _ => Q) (fun _ => e') hP (fun _ => hQ) hstep hfresh
  isplitl [HRd]
  · iexact HRd
  isplitl [HP]
  · iexact HP
  · inext
    iintro %σ %_ HQ
    iapply Hwp $$ HQ

/-- A finished thread has its postcondition. -/
theorem wp_finished (o : Outcome) : Φ o ⊢ WP (Code.finished (H := H) o) @ s; E {{ Φ }} :=
  wp_value' (Expr := Code H) (v := o)

/-- Two running threads that step to the same place from every store have
the same weakest precondition. -/
theorem wp_running_congr {lim₁ lim₂ : ExecLimits} {t₁ t₂ : Thread}
    (h : ∀ σ : Store H, next σ lim₁ t₁ = next σ lim₂ t₂) :
    WP (Code.running (H := H) lim₂ t₂) @ s; E {{ Φ }}
      ⊢ WP (Code.running (H := H) lim₁ t₁) @ s; E {{ Φ }} := by
  rw [(wp_unfold (e := Code.running (H := H) lim₁ t₁)).to_eq,
    (wp_unfold (e := Code.running (H := H) lim₂ t₂)).to_eq]
  simp only [wp.pre, ToVal.toVal]
  iintro H %σ %ns %obs %obs' %nt Hσ
  imod H $$ %σ %ns %obs %obs' %nt Hσ with ⟨_, H⟩
  imodintro
  isplitr
  · ipureintro
    cases s
    · exact running_reducible lim₁ t₁ σ
    · trivial
  iintro %e₂ %σ₂ %eₜ %Hstep
  iapply H
  ipureintro
  obtain ⟨h1, h2, h3⟩ := step_iff.mp Hstep
  exact step_iff.mpr ⟨h1, h2, h3.trans (h σ)⟩

/-- Congruence under persistently seen cells: the two threads step to the
same place from every store with those cells. -/
theorem wp_running_congr_see {lim₁ lim₂ : ExecLimits} {t₁ t₂ : Thread} (Rd : List (Loc × Cell H))
    (h : ∀ σ : Store H, (∀ p ∈ Rd, lookup σ p.1 = some p.2) → next σ lim₁ t₁ = next σ lim₂ t₂) :
    seeList Rd ∗ WP (Code.running (H := H) lim₂ t₂) @ s; E {{ Φ }}
      ⊢ WP (Code.running (H := H) lim₁ t₁) @ s; E {{ Φ }} := by
  rw [(wp_unfold (e := Code.running (H := H) lim₁ t₁)).to_eq,
    (wp_unfold (e := Code.running (H := H) lim₂ t₂)).to_eq]
  simp only [wp.pre, ToVal.toVal]
  iintro ⟨HRd, H⟩ %σ %ns %obs %obs' %nt Hσ
  ihave %hRd := seeList_lookup σ Rd $$ Hσ HRd
  imod H $$ %σ %ns %obs %obs' %nt Hσ with ⟨_, H⟩
  imodintro
  isplitr
  · ipureintro
    cases s
    · exact running_reducible lim₁ t₁ σ
    · trivial
  iintro %e₂ %σ₂ %eₜ %Hstep
  iapply H
  ipureintro
  obtain ⟨h1, h2, h3⟩ := step_iff.mp Hstep
  exact step_iff.mpr ⟨h1, h2, h3.trans (h σ hRd)⟩

end Lifting

end WasmLogic
