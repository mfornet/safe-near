import NearLogic.Resources

/-!
# Lifting a step that does not touch the host

Every Wasm instruction but a host call leaves the host state alone; its
metered step charges the gas counter twice (the instruction, then a new
frame's activation) and otherwise does what `Exec.step` does to the store.
`mwp_lift_plain` takes such a step from facts about `Exec.step` alone,
paying with credits: the rules of WasmLogic carry over with their side
conditions unchanged, plus their cost.
-/

namespace NearLogic

open Wasm Wasm.Near WasmLogic Iris Iris.BI Iris.Std Iris.ProgramLogic
  Iris.ProgramLogic.Language.Notation FromMathlib

/-! ## Charges that succeed -/

theorem burn_ok {g : Near.GasCounter} {n C : Nat} (h1 : g.used + n ≤ C) (h2 : C ≤ g.maxBurnt)
    (h3 : C ≤ g.prepaid) : g.burn n = ({ g with burnt := g.burnt + n }, none) := by
  unfold Near.GasCounter.burn Near.GasCounter.deduct
  unfold Near.GasCounter.used at h1
  rw [if_pos (by omega)]
  simp

/-- The host after a successful charge of `n`. -/
def charged (h : NearState) (n : Nat) : NearState :=
  { h with gas := { h.gas with burnt := h.gas.burnt + n },
           gasProfile := { h.gasProfile with wasm := h.gasProfile.wasm + n } }

theorem chargeHost_ok {h : NearState} {n C : Nat} (h1 : h.gas.used + n ≤ C) (h2 : C ≤ h.gas.maxBurnt)
    (h3 : C ≤ h.gas.prepaid) : chargeHost h n = (charged h n, none) := by
  unfold chargeHost charged
  rw [burn_ok h1 h2 h3]
  simp

theorem charged_charged (h : NearState) (a b : Nat) : charged (charged h a) b = charged h (a + b) := by
  simp [charged, Nat.add_assoc]

theorem erase_charged (h : NearState) (n : Nat) : erase (charged h n) = erase h := rfl

@[simp] theorem charged_gas_used (h : NearState) (n : Nat) :
    (charged h n).gas.used = h.gas.used + n := by
  simp [charged, Near.GasCounter.used]; omega

/-- The instruction cost does not look at the store. -/
theorem nextInstructionGas_store (cfg : WasmConfig) (s s' : Store NearState) (t : Thread)
    (lim : ExecLimits) :
    nextInstructionGas cfg { store := s, thread := t, limits := lim } =
      nextInstructionGas cfg { store := s', thread := t, limits := lim } := rfl

theorem gasCellOf_inj {g g' : Near.GasCounter} {p p' : Near.GasProfile}
    (h : gasCellOf g p = gasCellOf g' p') : g = g' ∧ p = p' := by
  unfold gasCellOf at h
  cases h
  exact ⟨rfl, rfl⟩

/-- The locations that are neither plain, the host nor the gas cell hold nothing. -/
theorem lookup_other (σ : Store NearState) {l : Loc} (hp : ¬ isPlain l) (hh : l ≠ Loc.host) :
    lookup σ l = none := by
  obtain ⟨k, a, i⟩ := l
  unfold isPlain at hp
  simp only at hp
  match k, a, i, hh with
  | 9, 0, 0, hh => exact absurd rfl hh
  | 9, _ + 1, _, _ | 9, 0, _ + 1, _ | _ + 10, _, _, _ => simp [lookup]
  | 0, _, _, _ | 1, _, _, _ | 2, _, _, _ | 3, _, _, _ | 4, _, _, _ | 5, _, _, _ | 6, _, _, _
  | 7, _, _, _ | 8, _, _, _ => omega

/-! ## The lifting lemma -/

/-- The store after a successful charge of `n`. -/
def chargedStore (s : Store NearState) (n : Nat) : Store NearState := { s with host := charged s.host n }

theorem lookup_chargedStore_plain (s : Store NearState) (n : Nat) {l : Loc} (hl : isPlain l) :
    lookup (chargedStore s n) l = lookup s l :=
  lookup_plain_host s _ hl

/-- The store the instruction runs on: the instruction's charge paid. -/
def preStore (cfg : WasmConfig) (lim : ExecLimits) (t : Thread) (s : Store NearState) : Store NearState :=
  chargedStore s (nextInstructionGas cfg { store := s, thread := t, limits := lim })

/-- A machine state with its host replaced. -/
def withHost : StepResult NearState → NearState → StepResult NearState
  | .next c, h => .next { c with store := { c.store with host := h } }
  | .done vs st, h => .done vs { st with host := h }
  | .trap r st, h => .trap r { st with host := h }

@[simp] theorem ofMachine_withHost (cfg : WasmConfig) (lim : ExecLimits) (m : StepResult NearState)
    (h : NearState) : ofMachine cfg lim (withHost m h) = ofMachine cfg lim m := by
  cases m <;> rfl

@[simp] theorem withHost_store (m : StepResult NearState) (h : NearState) :
    (withHost m h).store = { m.store with host := h } := by
  cases m <;> rfl

theorem chargeWasm_ok {m : StepResult NearState} {n C : Nat} (h1 : m.store.host.gas.used + n ≤ C)
    (h2 : C ≤ m.store.host.gas.maxBurnt) (h3 : C ≤ m.store.host.gas.prepaid) :
    chargeWasm m n = (withHost m (charged m.store.host n), none) := by
  cases m with
  | next c =>
    simp only [StepResult.store] at h1 h2 h3
    simp only [chargeWasm, chargeConfig]
    rw [chargeHost_ok h1 h2 h3]
    rfl
  | done vs st =>
    simp only [StepResult.store] at h1 h2 h3
    simp only [chargeWasm]
    rw [chargeHost_ok h1 h2 h3]
    rfl
  | trap r st =>
    simp only [StepResult.store] at h1 h2 h3
    simp only [chargeWasm]
    rw [chargeHost_ok h1 h2 h3]
    rfl

/-- The metered step of a thread whose step leaves the host alone, when the
charges fit. -/
theorem mnext_ok (cfg : WasmConfig) (lim : ExecLimits) (t : Thread) (ms : MStore) {C : Nat}
    (hhost : (Exec.step { store := preStore cfg lim t ms.store, thread := t, limits := lim }).store.host =
      (preStore cfg lim t ms.store).host)
    (hC : ms.store.host.gas.used + (nextInstructionGas cfg { store := ms.store, thread := t, limits := lim } +
      frameTransitionGas cfg { store := preStore cfg lim t ms.store, thread := t, limits := lim }
        (Exec.step { store := preStore cfg lim t ms.store, thread := t, limits := lim })) ≤ C)
    (h2 : C ≤ ms.store.host.gas.maxBurnt) (h3 : C ≤ ms.store.host.gas.prepaid) :
    mnext ms cfg lim t =
      (ofMachine cfg lim (Exec.step { store := preStore cfg lim t ms.store, thread := t, limits := lim }),
        ⟨{ (Exec.step { store := preStore cfg lim t ms.store, thread := t, limits := lim }).store with
            host := charged (preStore cfg lim t ms.store).host
              (frameTransitionGas cfg { store := preStore cfg lim t ms.store, thread := t, limits := lim }
                (Exec.step { store := preStore cfg lim t ms.store, thread := t, limits := lim })) }⟩) := by
  have hc1 : chargeConfig { store := ms.store, thread := t, limits := lim }
      (nextInstructionGas cfg { store := ms.store, thread := t, limits := lim }) =
      ({ store := preStore cfg lim t ms.store, thread := t, limits := lim }, none) := by
    unfold chargeConfig
    rw [chargeHost_ok (C := C) (by omega) h2 h3]
    rfl
  unfold mnext
  simp only
  rw [hc1]
  simp only
  rw [chargeWasm_ok (C := C)]
  · simp only [ofMachine_withHost, withHost_store, hhost]
  · rw [hhost]
    show (charged ms.store.host _).gas.used + _ ≤ C
    rw [charged_gas_used]
    omega
  · rw [hhost]; exact h2
  · rw [hhost]; exact h3

section Lifting

variable {GF : BundledGFunctors} [ι : WasmGS NearState GF]
variable {s : Stuckness} {E : CoPset} {Φ : Ending → IProp GF}

/-- A step that touches only plain locations, read in `Rd`, owned in `P` and
left as `Q`, and leaves the host alone, costs `k` credits: the instruction's
charge and the activation of any frame it enters. Its facts are about
`Exec.step` from any store holding the cells. -/
theorem mwp_lift_plain (cfg : WasmConfig) (lim : ExecLimits) (t : Thread)
    (Rd P : List (Loc × Cell NearState)) (Q : Store NearState → List (Loc × Cell NearState))
    (e' : Store NearState → MCode) (k C R : Nat)
    (hRd : ∀ p ∈ Rd, isPlain p.1) (hPp : ∀ p ∈ P, isPlain p.1) (hQp : ∀ σ, ∀ p ∈ Q σ, isPlain p.1)
    (hP : (P.map (·.1)).Nodup) (hQ : ∀ σ, ((Q σ).map (·.1)).Nodup)
    (hstep : ∀ σ : Store NearState, (∀ p ∈ Rd, lookup σ p.1 = some p.2) →
      (∀ p ∈ P, lookup σ p.1 = some p.2) →
      nextInstructionGas cfg { store := σ, thread := t, limits := lim } +
          frameTransitionGas cfg { store := σ, thread := t, limits := lim }
            (Exec.step { store := σ, thread := t, limits := lim }) = k ∧
        ofMachine cfg lim (Exec.step { store := σ, thread := t, limits := lim }) = e' σ ∧
        (Exec.step { store := σ, thread := t, limits := lim }).store.host = σ.host ∧
        ∀ l, isPlain l → lookup (Exec.step { store := σ, thread := t, limits := lim }).store l =
          ((Q σ).lookup l).or (if (P.lookup l).isSome then none else lookup σ l))
    (hfresh : ∀ σ : Store NearState, (∀ p ∈ Rd, lookup σ p.1 = some p.2) →
      (∀ p ∈ P, lookup σ p.1 = some p.2) →
      ∀ l, ((Q σ).lookup l).isSome → P.lookup l = none → lookup σ l = none) :
    credits C (k + R) ∗ seeList Rd ∗ ([∗list] p ∈ P, p.1 ↦ₛ p.2) ∗
      ▷ (∀ σ : Store NearState, ⌜(∀ p ∈ Rd, lookup σ p.1 = some p.2) ∧
          (∀ p ∈ P, lookup σ p.1 = some p.2)⌝ -∗
        ([∗list] p ∈ Q σ, p.1 ↦ₛ p.2) -∗ credits C R -∗ WP (e' σ) @ s; E {{ Φ }})
      ⊢ WP (MCode.running cfg lim t) @ s; E {{ Φ }} := by
  iintro ⟨Hc, HRd, HP, Hwp⟩
  iunfold credits at Hc
  icases Hc with ⟨%g, %p, Hg, %hg⟩
  obtain ⟨-, hk, hC1, hC2⟩ := hg
  -- The store the step runs on, and the cells around it.
  let pre (ms : MStore) := preStore cfg lim t ms.store
  let P' := (gasLoc, gasCellOf g p) :: P
  let Q' (ms : MStore) := (gasLoc, gasCellOf { g with burnt := g.burnt + k }
    { p with wasm := p.wasm + k }) :: Q (pre ms)
  have hnotP : gasLoc ∉ P.map (·.1) := by
    intro h
    obtain ⟨q, hq, he⟩ := List.mem_map.mp h
    have := hPp q hq
    rw [he] at this
    unfold isPlain at this
    simp at this
  have hnotQ : ∀ σ, gasLoc ∉ (Q σ).map (·.1) := by
    intro σ h
    obtain ⟨q, hq, he⟩ := List.mem_map.mp h
    have := hQp σ q hq
    rw [he] at this
    unfold isPlain at this
    simp at this
  -- Facts of a store holding the cells.
  have hfacts : ∀ ms : MStore, (∀ q ∈ Rd, mlookup ms q.1 = some q.2) → (∀ q ∈ P', mlookup ms q.1 = some q.2) →
      ms.store.host.gas = g ∧ ms.store.host.gasProfile = p ∧
      (∀ q ∈ Rd, lookup (pre ms) q.1 = some q.2) ∧ (∀ q ∈ P, lookup (pre ms) q.1 = some q.2) := by
    intro ms hR hPs
    have hgas := hPs _ List.mem_cons_self
    rw [mlookup, if_pos rfl, Option.some.injEq] at hgas
    obtain ⟨h1, h2⟩ := gasCellOf_inj hgas
    refine ⟨h1, h2, fun q hq => ?_, fun q hq => ?_⟩
    · rw [show pre ms = chargedStore ms.store _ from rfl, lookup_chargedStore_plain _ _ (hRd q hq),
        ← mlookup_plain ms (hRd q hq)]
      exact hR q hq
    · rw [show pre ms = chargedStore ms.store _ from rfl, lookup_chargedStore_plain _ _ (hPp q hq),
        ← mlookup_plain ms (hPp q hq)]
      exact hPs q (List.mem_cons_of_mem _ hq)
  iapply mwp_lift_dep cfg lim t Rd P' Q' (fun ms => e' (pre ms))
    (List.nodup_cons.mpr ⟨hnotP, hP⟩) (fun ms => List.nodup_cons.mpr ⟨hnotQ _, hQ _⟩)
  · intro ms hR hPs
    obtain ⟨hgas, hprof, hR', hP''⟩ := hfacts ms hR hPs
    obtain ⟨hcost, he, hhost, hplain⟩ := hstep (pre ms) hR' hP''
    have hpre : nextInstructionGas cfg { store := pre ms, thread := t, limits := lim } =
        nextInstructionGas cfg { store := ms.store, thread := t, limits := lim } := rfl
    rw [mnext_ok cfg lim t ms (C := C) hhost (by rw [← hpre, hcost, hgas]; omega)
      (by rw [hgas]; exact hC1) (by rw [hgas]; exact hC2)]
    refine ⟨he, fun l => ?_⟩
    have hk2 : nextInstructionGas cfg { store := ms.store, thread := t, limits := lim } +
        frameTransitionGas cfg { store := pre ms, thread := t, limits := lim }
          (Exec.step { store := pre ms, thread := t, limits := lim }) = k := by rw [← hpre]; exact hcost
    have hfin : charged (preStore cfg lim t ms.store).host
        (frameTransitionGas cfg { store := preStore cfg lim t ms.store, thread := t, limits := lim }
          (Exec.step { store := preStore cfg lim t ms.store, thread := t, limits := lim })) =
          charged ms.store.host k := by
      show charged (charged ms.store.host _) _ = _
      rw [charged_charged, hk2]
    rw [hfin]
    -- The cells of `Q` and `P` are plain.
    have hQnone : ∀ l, ¬ isPlain l → (Q (pre ms)).lookup l = none := by
      intro l hl
      cases hq : (Q (pre ms)).lookup l with
      | none => rfl
      | some c => exact absurd (hQp _ (l, c) (mem_of_lookup hq)) hl
    have hPnone : ∀ l, ¬ isPlain l → P.lookup l = none := by
      intro l hl
      cases hq : P.lookup l with
      | none => rfl
      | some c => exact absurd (hPp (l, c) (mem_of_lookup hq)) hl
    by_cases hg : l = gasLoc
    · subst hg
      simp only [mlookup, ↓reduceIte, Q', lookup_cons_pair, Option.some_or]
      rw [← hgas, ← hprof]
      rfl
    by_cases hh : l = Loc.host
    · subst hh
      have hnp : ¬ isPlain Loc.host := by unfold isPlain; simp
      simp only [mlookup, Q', P', lookup_cons_pair, if_neg hg, ↓reduceIte, hQnone _ hnp,
        hPnone _ hnp, Option.none_or, Option.isSome_none, Bool.false_eq_true, ite_false]
      rw [erase_charged]
    by_cases hp : isPlain l
    · simp only [mlookup, Q', P', lookup_cons_pair, if_neg hg, if_neg hh]
      rw [lookup_plain_host _ _ hp, hplain l hp, show pre ms = chargedStore ms.store _ from rfl,
        lookup_chargedStore_plain _ _ hp]
    · simp only [mlookup, Q', P', lookup_cons_pair, if_neg hg, if_neg hh, hQnone _ hp, hPnone _ hp,
        Option.none_or, Option.isSome_none, Bool.false_eq_true, ite_false]
      rw [lookup_other _ hp hh, lookup_other _ hp hh]
  · intro ms hR hPs l hl hnone
    obtain ⟨-, -, hR', hP''⟩ := hfacts ms hR hPs
    have hgl : l ≠ gasLoc := by
      intro he; subst he; simp [P', lookup_cons_pair] at hnone
    simp only [Q', lookup_cons_pair, if_neg hgl] at hl
    simp only [P', lookup_cons_pair, if_neg hgl] at hnone
    have hpl : isPlain l := by
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hl
      exact hQp _ (l, c) (mem_of_lookup hc)
    rw [mlookup_plain ms hpl, ← lookup_chargedStore_plain ms.store
      (nextInstructionGas cfg { store := ms.store, thread := t, limits := lim }) hpl]
    exact hfresh (pre ms) hR' hP'' l hl hnone
  isplitl [HRd]
  · iexact HRd
  isplitl [Hg HP]
  · iapply BigSepL.bigSepL_cons.2
    isplitl [Hg]
    · iunfold gasPt at Hg
      iexact Hg
    · iexact HP
  inext
  iintro %ms %⟨hR, hPs⟩ HQ
  obtain ⟨hgas, hprof, hR', hP''⟩ := hfacts ms hR hPs
  icases (BigSepL.bigSepL_cons.1 : _ ⊢ _ ∗ _) $$ HQ with ⟨Hg, HQ⟩
  iapply Hwp $$ %(pre ms) %⟨hR', hP''⟩ HQ
  iunfold credits
  iexists { g with burnt := g.burnt + k }, { p with wasm := p.wasm + k }
  isplitl [Hg]
  · iunfold gasPt
    iexact Hg
  · ipureintro
    simp only [Near.GasCounter.used] at hk ⊢
    omega

end Lifting

end NearLogic
