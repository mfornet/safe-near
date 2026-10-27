import NearLogic.Lift
import WasmLogic.Frag

/-!
# Weakest preconditions for code fragments, metered

WasmLogic's `wpi` (`WasmLogic/Frag.lean`) over the metered language: a
fragment `es` run in frame `f` on operands `vs`, ending as `Φ : Post` says.
Frames, contexts and postconditions are WasmLogic's. A charge that fails is
no way of ending: proofs hold credits for every step, so it never happens.

Gas credits are ordinary resources: an instruction rule takes
`credits C (cost + R)` and gives the continuation `credits C R`.
-/

namespace NearLogic

open Wasm Wasm.Near WasmLogic Iris Iris.BI Iris.Std Iris.ProgramLogic
  Iris.ProgramLogic.Language.Notation FromMathlib

section Defs

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- `WP` of a running metered thread. -/
abbrev mwpT (cfg : WasmConfig) (lim : ExecLimits) (t : Thread) (Ψ : Ending → IProp GF) : IProp GF :=
  WP (MCode.running cfg lim t) @ Stuckness.MaybeStuck; ⊤ {{ Ψ }}

/-- How the context carries on from each way the fragment can end. -/
def mKont (cfg : WasmConfig) (lim : ExecLimits) (C : Ctx) (f : Frame) (Φ : Post NearState GF)
    (Ψ : Ending → IProp GF) : IProp GF :=
  iprop((∀ vs l, Φ.normal vs (f.withLocals l) -∗
      mwpT cfg lim (C.thread (f.withLocals l) vs C.labels C.rest) Ψ) ∧
    (∀ n vs l, Φ.br n vs (f.withLocals l) -∗
      mwpT cfg lim (C.thread (f.withLocals l) vs C.labels [.br n]) Ψ) ∧
    (∀ vs l, Φ.ret vs (f.withLocals l) -∗
      mwpT cfg lim (C.thread (f.withLocals l) vs C.labels [.return]) Ψ) ∧
    (Φ.trap -∗ ∀ r, Ψ (.trap r)))

/-- The metered weakest precondition of fragment `es` in frame `f` on
operands `vs`, at call depth `d`. -/
def mwpi (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (f : Frame) (vs : List Value)
    (es : List Instr) (Φ : Post NearState GF) : IProp GF :=
  iprop(∀ (Ψ : Ending → IProp GF) (C : Ctx), ⌜C.below.length = d⌝ -∗
    instPt (H := NearState) f.inst f.mi -∗
    mKont cfg lim C f Φ Ψ -∗ mwpT cfg lim (C.thread f vs C.labels (es ++ C.rest)) Ψ)

/-- Sequencing: after `es₁` falls through, run `es₂`. -/
def Post.mseq (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (es₂ : List Instr)
    (Φ : Post NearState GF) : Post NearState GF :=
  { Φ with normal := fun vs f => mwpi cfg lim d f vs es₂ Φ }

end Defs

section Structural

variable {GF : BundledGFunctors} [ι : WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {vs : List Value}
  {es : List Instr}

theorem mwpi_wand {Φ Φ' : Post NearState GF} :
    mwpi cfg lim d f vs es Φ ∗ Post.wand Φ Φ' ⊢ mwpi cfg lim d f vs es Φ' := by
  unfold mwpi Post.wand mKont
  iintro ⟨Hwp, Hw⟩ %Ψ %C %hC #Hi HK
  iapply Hwp $$ %Ψ %C %hC Hi
  isplit
  · iintro %vs' %f' HΦ
    icases Hw with ⟨Hw, -⟩
    icases HK with ⟨HK, -⟩
    iapply HK
    iapply Hw $$ HΦ
  isplit
  · iintro %n %vs' %f' HΦ
    icases Hw with ⟨-, ⟨Hw, -⟩⟩
    icases HK with ⟨-, ⟨HK, -⟩⟩
    iapply HK
    iapply Hw $$ HΦ
  isplit
  · iintro %vs' %f' HΦ
    icases Hw with ⟨-, -, ⟨Hw, -⟩⟩
    icases HK with ⟨-, -, ⟨HK, -⟩⟩
    iapply HK
    iapply Hw $$ HΦ
  · iintro HΦ
    icases Hw with ⟨-, -, -, Hw⟩
    icases HK with ⟨-, -, -, HK⟩
    iapply HK
    iapply Hw $$ HΦ

/-- The frame rule. -/
theorem mwpi_frame {R : IProp GF} {Φ : Post NearState GF} :
    R ∗ mwpi cfg lim d f vs es Φ ⊢ mwpi cfg lim d f vs es (Post.frame R Φ) := by
  iintro ⟨HR, Hwp⟩
  iapply mwpi_wand
  isplitl [Hwp]
  · iexact Hwp
  unfold Post.wand Post.frame
  isplit
  · iintro %vs' %f' HΦ
    isplitl [HR]
    · iexact HR
    · iexact HΦ
  isplit
  · iintro %n %vs' %f' HΦ
    isplitl [HR]
    · iexact HR
    · iexact HΦ
  isplit
  · iintro %vs' %f' HΦ
    isplitl [HR]
    · iexact HR
    · iexact HΦ
  · iintro HΦ
    isplitl [HR]
    · iexact HR
    · iexact HΦ

/-- The empty fragment falls through at once. -/
theorem mwpi_nil {Φ : Post NearState GF} : Φ.normal vs f ⊢ mwpi cfg lim d f vs [] Φ := by
  unfold mwpi mKont
  iintro HΦ %Ψ %C %_ #_ HK
  icases HK with ⟨HK, -⟩
  simp only [List.nil_append]
  ispecialize HK $$ %vs %f.locals
  simp only [Frame.withLocals_self]
  iapply HK $$ HΦ

theorem mwpi_seq {es₁ es₂ : List Instr} {Φ : Post NearState GF} :
    mwpi cfg lim d f vs es₁ (Post.mseq cfg lim d es₂ Φ) ⊢ mwpi cfg lim d f vs (es₁ ++ es₂) Φ := by
  unfold mwpi Post.mseq mKont
  iintro Hwp %Ψ %C %hC #Hi HK
  rw [List.append_assoc]
  ispecialize Hwp $$ %Ψ %{ C with rest := es₂ ++ C.rest } %hC Hi
  simp only [Ctx.thread_withRest]
  iapply Hwp
  isplit
  · iintro %vs' %f' H2
    iunfold mwpi, mKont at H2
    simp only [Frame.withLocals_inst, Frame.withLocals_mi, Frame.withLocals_withLocals]
    iapply H2 $$ %Ψ %C %hC Hi
    iexact HK
  · icases HK with ⟨-, HK⟩
    iexact HK

theorem mwpi_cons {i : Instr} {es : List Instr} {Φ : Post NearState GF} :
    mwpi cfg lim d f vs [i] (Post.mseq cfg lim d es Φ) ⊢ mwpi cfg lim d f vs (i :: es) Φ :=
  mwpi_seq (es₁ := [i]) (es₂ := es)

@[simp] theorem Post.mseq_normal (es : List Instr) (Φ : Post NearState GF) (vs : List Value) (g : Frame) :
    (Post.mseq cfg lim d es Φ).normal vs g = mwpi cfg lim d g vs es Φ := rfl
@[simp] theorem Post.mseq_br (es : List Instr) (Φ : Post NearState GF) (n : Nat) (vs : List Value)
    (g : Frame) : (Post.mseq cfg lim d es Φ).br n vs g = Φ.br n vs g := rfl
@[simp] theorem Post.mseq_ret (es : List Instr) (Φ : Post NearState GF) (vs : List Value) (g : Frame) :
    (Post.mseq cfg lim d es Φ).ret vs g = Φ.ret vs g := rfl
@[simp] theorem Post.mseq_trap (es : List Instr) (Φ : Post NearState GF) :
    (Post.mseq cfg lim d es Φ).trap = Φ.trap := rfl

end Structural

/-! ## One instruction -/

/-- Instructions whose charge is one `regular_op_cost`: no `block`, no
branch (a branch back to a loop costs one more), no bulk operation. -/
def isFlat : Instr → Bool
  | .block .. | .br _ | .br_if _ | .br_table .. => false
  | i => !linearInstruction i

theorem nextInstructionGas_flat (cfg : WasmConfig) (σ : Store NearState) (lim : ExecLimits) (C : Ctx)
    (f : Frame) (vs : List Value) (L : List Label) (i : Instr) (R : List Instr) (hi : isFlat i = true) :
    nextInstructionGas cfg { store := σ, thread := C.thread f vs L (i :: R), limits := lim } =
      cfg.regularOpCost := by
  have hl : linearInstruction i = false := by
    cases i <;> simp_all [isFlat]
  cases i <;> simp_all [nextInstructionGas, Config.nextInstr?, Ctx.thread, Ctx.threadA, loopBackedge,
    isFlat]

theorem frameTransitionGas_same (cfg : WasmConfig) (c c' : Config NearState)
    (h : c'.callDepth = c.callDepth) : frameTransitionGas cfg c (.next c') = 0 := by
  simp [frameTransitionGas, h]

/-- A step of an instruction that continues in the same frame, as
`Exec.step` takes it. -/
theorem step_instr_continue (σ : Store NearState) (lim : ExecLimits) (C : Ctx) (f : Frame)
    (vs : List Value) (L : List Label) (i : Instr) (R : List Instr)
    (hmi : σ.modules[f.inst]? = some f.mi) {σ' : Store NearState} {stack' : Array Value}
    {L' : List Label} {code' : List Instr} {loc' : Array Value}
    (h : Exec.instr σ f.mi f.locals (C.base ++ vs).toArray L i R =
      ⟨σ', .continue stack' L' code' loc'⟩) :
    Exec.step { store := σ, thread := C.thread f vs L (i :: R), limits := lim } =
      .next { store := σ', thread := C.threadA (f.withLocals loc') stack' L' code', limits := lim } := by
  simp [Exec.step, Ctx.thread, Ctx.threadA, Frame.withLocals, modules_get! hmi, h]

section Instr

variable {GF : BundledGFunctors} [ι : WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {vs : List Value}

/-- The generic metered rule for a flat instruction that falls through, on
plain cells: WasmLogic's `wpi_instr`, for `regular_op_cost` credits. -/
theorem mwpi_instr (i : Instr) (hi : isFlat i = true) (vs' : List Value) (loc' : Array Value)
    (Rd P Q : List (Loc × Cell NearState))
    (hRd : ∀ p ∈ Rd, isPlain p.1) (hPp : ∀ p ∈ P, isPlain p.1) (hQp : ∀ p ∈ Q, isPlain p.1)
    (hP : (P.map (·.1)).Nodup) (hQ : (Q.map (·.1)).Nodup) {Φ : Post NearState GF} {Cg R : Nat}
    (h : ∀ σ : Store NearState, σ.modules[f.inst]? = some f.mi → (∀ p ∈ Rd, lookup σ p.1 = some p.2) →
      (∀ p ∈ P, lookup σ p.1 = some p.2) → ∀ base L R, ∃ σ',
        Exec.instr σ f.mi f.locals (base ++ vs).toArray L i R =
          ⟨σ', .continue (base ++ vs').toArray L R loc'⟩ ∧ Replaces σ σ' P Q ∧ σ'.host = σ.host)
    (hfresh : ∀ σ : Store NearState, σ.modules[f.inst]? = some f.mi →
      (∀ p ∈ Rd, lookup σ p.1 = some p.2) → (∀ p ∈ P, lookup σ p.1 = some p.2) →
      ∀ l, (Q.lookup l).isSome → P.lookup l = none → lookup σ l = none) :
    credits Cg (cfg.regularOpCost + R) ∗ seeList Rd ∗ ([∗list] p ∈ P, p.1 ↦ₛ p.2) ∗
      ▷ (([∗list] p ∈ Q, p.1 ↦ₛ p.2) -∗ credits Cg R -∗ Φ.normal vs' (f.withLocals loc'))
      ⊢ mwpi cfg lim d f vs [i] Φ := by
  unfold mwpi mKont
  iintro ⟨Hc, HRd, HP, HΦ⟩ %Ψ %C %hC #Hi HK
  have hmi : ∀ σ : Store NearState, (∀ p ∈ (Loc.inst f.inst, Cell.inst f.mi) :: Rd,
      lookup σ p.1 = some p.2) → σ.modules[f.inst]? = some f.mi := by
    intro σ hσ
    have := hσ _ List.mem_cons_self
    simp only [lookup_inst, Option.map_eq_some_iff] at this
    obtain ⟨m, hm, he⟩ := this
    cases he; exact hm
  have hRd' : ∀ p ∈ (Loc.inst f.inst, Cell.inst f.mi) :: Rd, isPlain p.1 := by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · unfold isPlain; simp
    · exact hRd p hp
  iapply mwp_lift_plain cfg lim (C.thread f vs C.labels ([i] ++ C.rest))
    ((Loc.inst f.inst, .inst f.mi) :: Rd) P (fun _ => Q)
    (fun _ => .running cfg lim (C.thread (f.withLocals loc') vs' C.labels C.rest))
    cfg.regularOpCost Cg R hRd' hPp (fun _ => hQp) hP (fun _ => hQ)
  · intro σ hR hPs
    obtain ⟨σ', hinstr, hrep, hhost⟩ := h σ (hmi σ hR) (fun p hp => hR p (List.mem_cons_of_mem _ hp)) hPs
      C.base C.labels C.rest
    rw [List.singleton_append, step_instr_continue σ lim C f vs C.labels i C.rest (hmi σ hR) hinstr,
      nextInstructionGas_flat cfg σ lim C f vs C.labels i C.rest hi,
      frameTransitionGas_same cfg _ _ (by simp [Config.callDepth, Ctx.thread, Ctx.threadA])]
    exact ⟨rfl, rfl, hhost, fun l _ => hrep l⟩
  · intro σ hR hPs l hl hnone
    exact hfresh σ (hmi σ hR) (fun p hp => hR p (List.mem_cons_of_mem _ hp)) hPs l hl hnone
  isplitl [Hc]
  · iexact Hc
  isplitl [HRd]
  · iapply (seeList_cons _ _).2
    iunfold instPt at Hi
    isplitr
    · iexact Hi
    · iexact HRd
  isplitl [HP]
  · iexact HP
  inext
  iintro %σ %_ HQ Hc
  icases HK with ⟨HK, -⟩
  iapply HK
  iapply HΦ $$ HQ Hc

end Instr

end NearLogic
