import NearLogic.Frag
import WasmLogic.Adequacy

/-!
# Adequacy: from the metered logic to `runMetered`

`runMetered_steps` says a run of `Wasm.Near.runMetered` is a sequence of
steps of the metered language, and `madequacy` that a `WP` proved from
ownership of the initial store's cells, with a pure postcondition, holds of
how every run ends: its values, its trap or its failed charge. A proof that
holds credits for every step has `False` as the postcondition of a failed
charge, so such a run never fails for gas.

The resource family is WasmLogic's (`WasmLogic.GF NearState`).
-/

namespace NearLogic

open Wasm Wasm.Near WasmLogic Iris Iris.BI Iris.Std Iris.ProgramLogic
  Iris.ProgramLogic.Language.Notation FromMathlib Std.LawfulSet

/-! ## `runMetered` as language steps -/

/-- What a run of `runMetered` stopped at, as an expression and a state.
Fuel exhaustion leaves a running thread; a failed charge is the `gas`
ending. -/
def resultCode (cfg : WasmConfig) : Machine × Option FunctionCallError → MCode × MStore
  | (m, some (.hostError e)) => (.finished (.gas e), ⟨m.store⟩)
  | (.next c, _) => (.running cfg c.limits c.thread, ⟨c.store⟩)
  | (.done vs s, _) => (.finished (.values vs), ⟨s⟩)
  | (.trap r s, _) => (.finished (.trap r), ⟨s⟩)

theorem chargeConfig_limits (c : Config NearState) (n : Nat) : (chargeConfig c n).1.limits = c.limits :=
  rfl

theorem chargeWasm_next_limits {c : Config NearState} {n : Nat} {c' : Config NearState}
    (h : (chargeWasm (.next c) n).1 = .next c') : c'.limits = c.limits := by
  simp only [chargeWasm, chargeConfig, StepResult.next.injEq] at h
  rw [← h]

/-- A run of `runMetered` from a running configuration is a sequence of
steps of the language. -/
theorem runMetered_steps (cfg : WasmConfig) (fuel : Nat) (c : Config NearState) :
    ([MCode.running cfg c.limits c.thread], (⟨c.store⟩ : MStore)) -·->ₜₚ*
      ([(resultCode cfg (runMetered cfg fuel (.next c))).1],
        (resultCode cfg (runMetered cfg fuel (.next c))).2) := by
  induction fuel generalizing c with
  | zero => exact .refl
  | succ fuel ih =>
    have hstep : ∀ e σ, (e, σ) = mnext ⟨c.store⟩ cfg c.limits c.thread →
        ([MCode.running cfg c.limits c.thread], (⟨c.store⟩ : MStore)) -·->ₜₚ* ([e], σ) := by
      intro e σ he
      exact .single ⟨[], .atomic (step_iff.mpr ⟨rfl, rfl, he⟩) [] []⟩
    unfold runMetered
    simp only
    cases h1 : (chargeConfig c (nextInstructionGas cfg c)).2 with
    | some e =>
      apply hstep
      simp [mnext, h1, resultCode] <;> rfl
    | none =>
      simp only
      cases h2 : (chargeWasm (Exec.step (chargeConfig c (nextInstructionGas cfg c)).1)
          (frameTransitionGas cfg (chargeConfig c (nextInstructionGas cfg c)).1
            (Exec.step (chargeConfig c (nextInstructionGas cfg c)).1))).2 with
      | some e =>
        apply hstep
        simp [mnext, h1, h2, resultCode] <;> rfl
      | none =>
        simp only
        generalize hm : (chargeWasm (Exec.step (chargeConfig c (nextInstructionGas cfg c)).1)
          (frameTransitionGas cfg (chargeConfig c (nextInstructionGas cfg c)).1
            (Exec.step (chargeConfig c (nextInstructionGas cfg c)).1))).1 = m at h2
        have hmn : mnext ⟨c.store⟩ cfg c.limits c.thread = (ofMachine cfg c.limits m, ⟨m.store⟩) := by
          simp [mnext, h1, h2, hm]
        cases m with
        | next c' =>
          have hlim : c'.limits = c.limits := by
            cases hs : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 with
            | next c'' =>
              rw [hs] at hm
              rw [chargeWasm_next_limits hm, Exec.step_limits _ hs, chargeConfig_limits]
            | done vs s => rw [hs] at hm; simp [chargeWasm] at hm
            | trap r s => rw [hs] at hm; simp [chargeWasm] at hm
          have h1' := hstep _ _ hmn.symm
          have h2' := ih c'
          rw [hlim] at h2'
          simp only [ofMachine, StepResult.store] at h1'
          exact h1'.trans h2'
        | done vs s =>
          rw [runMetered_done]
          exact hstep _ _ (by rw [hmn]; rfl)
        | trap r s =>
          rw [runMetered_trapped]
          exact hstep _ _ (by rw [hmn]; rfl)

/-! ## Adequacy -/

/-- Adequacy with a pure postcondition: if from ownership of every cell of
the initial store's metered view the program satisfies `WP` with
postcondition `⌜φ e⌝`, then every reachable finished thread ends in an `e`
with `φ e`. -/
theorem mwp_adequacy {GF' : BundledGFunctors} [WasmGpreS NearState GF'] (e : MCode) (σ : MStore)
    (φ : Ending → Prop)
    (hwp : ∀ [WasmGS NearState GF'], ownCells (GF := GF') (mheapOf σ) ⊢
      WP e @ Stuckness.MaybeStuck; ⊤ {{ v, ⌜φ v⌝ }}) :
    adequate .MaybeStuck e σ (fun v _ => φ v) := by
  refine (adequate_alt _ _ _ _).mpr ?_
  intro t2 σ2 hreach
  refine ⟨fun v2 t2' heq => ?_, fun _ h => by cases h⟩
  subst heq
  obtain ⟨n, κs, hsteps⟩ := (Language.erasedStep_nSteps _ _).mp hreach
  apply wp_strong_adequacy_gen (GF := GF') (hlc := .hasLC) .MaybeStuck (Hsteps := hsteps)
    (numLaters := fun _ => 0)
  iintro %Hinv
  imod ghost_map_alloc (GF := GF') (mheapOf σ) with ⟨%γ, Hauth, Hcells⟩
  let wgs : WasmGS NearState GF' := { invGS := Hinv, heap := WasmGpreS.heap, name := γ }
  ihave Hwp := (@hwp wgs) $$ Hcells
  iexists (fun σ _ _ _ => ghost_map_auth γ (.own 1) (mheapOf σ)),
    [fun v => iprop(⌜φ v⌝)], (fun _ => iprop(True)),
    (fun _ _ _ _ => fupd_intro)
  dsimp only
  imodintro
  iframe
  isplitl
  · iapply BigSepL2.bigSepL2_nil; itrivial
  iintro %es' %_ %Heq %hlen %_ _ Hpost _
  icases BigSepL2.bigSepL2_cons_inv_right $$ Hpost with ⟨%e', %es'', %Heq', Hpost, H⟩
  subst Heq'
  icases BigSepL2.bigSepL2_nil_inv_right $$ H with %Heq''
  subst Heq''
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at Heq
  obtain ⟨rfl, -⟩ := Heq
  simp only [ToVal.toVal_coe, Option.elim_some]
  icases Hpost with %hφ
  iapply fupd_mask_intro_discard empty_subset
  ipureintro
  exact hφ

/-- Ownership of cells `cs`, at distinct locations, with `R cs`: how a
postcondition says what the final store holds. -/
abbrev mcellsSat {GF' : BundledGFunctors} [WasmGS NearState GF'] (R : List (Loc × Cell NearState) → Prop) :
    IProp GF' :=
  iprop(∃ cs, ⌜R cs ∧ (cs.map (·.1)).Nodup⌝ ∗ [∗list] p ∈ cs, p.1 ↦ₛ p.2)

/-- Adequacy with cells: every reachable finished thread ends in an `e` with
`φ e` and a state whose metered view holds cells `cs` with `R e cs`. -/
theorem mwp_adequacy_cells {GF' : BundledGFunctors} [WasmGpreS NearState GF'] (e : MCode) (σ : MStore)
    (φ : Ending → Prop) (R : Ending → List (Loc × Cell NearState) → Prop)
    (hwp : ∀ [WasmGS NearState GF'], ownCells (GF := GF') (mheapOf σ) ⊢
      WP e @ Stuckness.MaybeStuck; ⊤ {{ v, ⌜φ v⌝ ∗ mcellsSat (R v) }}) :
    adequate .MaybeStuck e σ
      (fun v σ' => φ v ∧ ∃ cs, R v cs ∧ ∀ p ∈ cs, mlookup σ' p.1 = some p.2) := by
  refine (adequate_alt _ _ _ _).mpr ?_
  intro t2 σ2 hreach
  refine ⟨fun v2 t2' heq => ?_, fun _ h => by cases h⟩
  subst heq
  obtain ⟨n, κs, hsteps⟩ := (Language.erasedStep_nSteps _ _).mp hreach
  apply wp_strong_adequacy_gen (GF := GF') (hlc := .hasLC) .MaybeStuck (Hsteps := hsteps)
    (numLaters := fun _ => 0)
  iintro %Hinv
  imod ghost_map_alloc (GF := GF') (mheapOf σ) with ⟨%γ, Hauth, Hcells⟩
  let wgs : WasmGS NearState GF' := { invGS := Hinv, heap := WasmGpreS.heap, name := γ }
  ihave Hwp := (@hwp wgs) $$ Hcells
  iexists (fun σ _ _ _ => ghost_map_auth γ (.own 1) (mheapOf σ)),
    [fun v => iprop(⌜φ v⌝ ∗ mcellsSat (R v))], (fun _ => iprop(True)),
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
  simpa [get?_mheapOf] using this

/-- How a run of `runMetered` ends, from adequacy: values, a trap or a
failed charge all satisfy the postcondition; fuel exhaustion is not
covered (`NearVM.Fuel` rules it out). -/
theorem runMetered_ending (cfg : WasmConfig) (fuel : Nat) (c : Config NearState) (φ : Ending → Prop)
    (had : adequate (Expr := MCode) .MaybeStuck (.running cfg c.limits c.thread) ⟨c.store⟩
      (fun v _ => φ v)) :
    match resultCode cfg (runMetered cfg fuel (.next c)) with
    | (.finished e, _) => φ e
    | (.running .., _) => True := by
  have steps := runMetered_steps cfg fuel c
  generalize resultCode cfg (runMetered cfg fuel (.next c)) = r at steps
  obtain ⟨e, σ⟩ := r
  cases e with
  | running => trivial
  | finished e => exact had.adequate_result [] σ e steps

/-- `runMetered_ending` with what the final state holds. -/
theorem runMetered_ending_state (cfg : WasmConfig) (fuel : Nat) (c : Config NearState)
    (φ : Ending → MStore → Prop)
    (had : adequate (Expr := MCode) .MaybeStuck (.running cfg c.limits c.thread) ⟨c.store⟩ φ) :
    match resultCode cfg (runMetered cfg fuel (.next c)) with
    | (.finished e, σ) => φ e σ
    | (.running .., _) => True := by
  have steps := runMetered_steps cfg fuel c
  generalize resultCode cfg (runMetered cfg fuel (.next c)) = r at steps
  obtain ⟨e, σ⟩ := r
  cases e with
  | running => trivial
  | finished e => exact had.adequate_result [] σ e steps

end NearLogic
