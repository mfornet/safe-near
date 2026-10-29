import NearLogic.Entry

/-!
# The entry function, ending in `return`

`NearLogic.mwp_entry` takes a body that falls through (`entryPost`, whose `ret` is `False`). A
body that ends in `return` (as `new`'s, function 290, from inside its blocks) needs the `ret`
continuation too: `return` at the entry leaves the frame, as falling through does, but pays its
instruction (`regularOpCost`). `entryPostR` is `entryPost` with that `ret`, and `mwp_entryR` is
`mwp_entry` for it.
-/

namespace NearLogic

open Wasm Wasm.Near WasmLogic Iris Iris.BI Iris.Std Iris.ProgramLogic
  Iris.ProgramLogic.Language.Notation FromMathlib

/-- `entryPost`, and `return` with the entry's results, paying its instruction. -/
def entryPostR {GF : BundledGFunctors} [WasmGS NearState GF] (cfg : WasmConfig) (Cg arity : Nat)
    (Ψ : Ending → IProp GF) : Post NearState GF where
  normal vs _ := iprop(⌜vs.length = arity⌝ ∗ ∃ R, credits Cg R ∗ (credits Cg R -∗ Ψ (.values vs)))
  ret vs _ := iprop(⌜vs.length = arity⌝ ∗ ∃ R, credits Cg (cfg.regularOpCost + R) ∗ (credits Cg R -∗ Ψ (.values vs)))
  trap := iprop(∀ r, Ψ (.trap r))

section Entry

variable {GF : BundledGFunctors} [ι : WasmGS NearState GF]

theorem step_return_entry (σ : Store NearState) (lim : ExecLimits) (f : Frame) (arity : Nat) (vs : List Value)
    (hv : vs.length = arity) :
    Exec.step { store := σ, thread := (entryCtx arity).thread f vs (entryCtx arity).labels [.return], limits := lim } = .done vs σ := by
  simp only [Exec.step, Exec.instr, entryCtx, Ctx.thread, Ctx.threadA, List.nil_append, Exec.leave, Exec.Effect.return]
  have := popN_args [] vs
  simp only [List.nil_append] at this
  rw [← hv, this]

/-- `return` at the entry: the frame is left, the machine is done with the values. -/
theorem mwp_return_entry (cfg : WasmConfig) (lim : ExecLimits) (f : Frame) (arity : Nat) (vs : List Value)
    (Cg : Nat) (Ψ : Ending → IProp GF) (hv : vs.length = arity) :
    (∃ R, credits Cg (cfg.regularOpCost + R) ∗ ▷ (credits Cg R -∗ Ψ (.values vs))) ⊢
      mwpT cfg lim ((entryCtx arity).thread f vs (entryCtx arity).labels [.return]) Ψ := by
  iintro ⟨%R, Hc, HΨ⟩
  iapply mwp_lift_plain cfg lim ((entryCtx arity).thread f vs (entryCtx arity).labels [.return]) [] [] (fun _ => [])
    (fun _ => .finished (.values vs)) cfg.regularOpCost Cg R (by simp) (by simp) (by simp) (by simp) (by simp)
  · intro σ _ _
    rw [step_return_entry σ lim f arity vs hv]
    refine ⟨?_, rfl, rfl, fun l _ => by simp [StepResult.store]⟩
    simp [nextInstructionGas, Config.nextInstr?, entryCtx, Ctx.thread, Ctx.threadA, frameTransitionGas,
      linearInstruction, loopBackedge]
  · intro σ _ _ l hl _
    simp at hl
  isplitl [Hc]
  · iexact Hc
  isplitl []
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl []
  · iapply BigSepL.bigSepL_nil.2; iempintro
  inext
  iintro %_ %_ _ Hc
  iapply mwp_finished
  iapply HΨ $$ Hc

/-- **`mwp_entry` for a body that may `return`.** -/
theorem mwp_entryR (cfg : WasmConfig) (lim : ExecLimits) (f : Frame) (arity : Nat) (body : List Instr)
    (Cg : Nat) (Ψ : Ending → IProp GF) :
    instPt (H := NearState) f.inst f.mi ∗ mwpi cfg lim 0 f [] body (entryPostR cfg Cg arity Ψ)
      ⊢ mwpT cfg lim (entryThread f arity body) Ψ := by
  iintro ⟨#Hi, Hwp⟩
  iunfold mwpi at Hwp
  have ht : entryThread f arity body =
      (entryCtx arity).thread f [] (entryCtx arity).labels (body ++ (entryCtx arity).rest) := by
    simp [entryThread, entryCtx, Ctx.thread, Ctx.threadA]
  rw [ht]
  iapply Hwp $$ %Ψ %(entryCtx arity) %rfl Hi
  iunfold mKont
  simp only [entryPostR]
  isplit
  · iintro %vs %l ⟨%hv, %R, Hc, HΨ⟩
    iapply mwp_leave_entry cfg lim (f.withLocals l) arity vs Cg Ψ hv
    iexists R
    isplitl [Hc]
    · iexact Hc
    · inext
      iexact HΨ
  isplit
  · iintro %n %vs %l HF
    iexfalso
    iexact HF
  isplit
  · iintro %vs %l ⟨%hv, %R, Hc, HΨ⟩
    iapply mwp_return_entry cfg lim (f.withLocals l) arity vs Cg Ψ hv
    iexists R
    isplitl [Hc]
    · iexact Hc
    · inext
      iexact HΨ
  · iintro HΨ
    iexact HΨ

end Entry

end NearLogic
