import NearLogic.Frag
import WasmLogic.Rules.Call

/-!
# The entry function

A method runs as the only frame of the machine (`Exec.startWasm`). When its
body falls through, the machine leaves the frame and is done with its
`arity` values; that last step costs nothing. `mwp_entry` turns a proof of
the body, as a fragment at call depth 0, into a `WP` of the whole thread.
-/

namespace NearLogic

open Wasm Wasm.Near WasmLogic Iris Iris.BI Iris.Std Iris.ProgramLogic
  Iris.ProgramLogic.Language.Notation FromMathlib

/-- The thread `Exec.startWasm` builds for a function with these locals,
instance, arity and body. -/
def entryThread (f : Frame) (arity : Nat) (body : List Instr) : Thread :=
  { stack := #[], frames := [CallFrame.mk f.locals f.inst arity 0 [] body] }

/-- The context of an entry function's body. -/
def entryCtx (arity : Nat) : Ctx :=
  { base := [], labels := [], rest := [], arity, height := 0, below := [] }

/-- How the entry function may end: falling through with its results and
whatever credits are left, or trapping. -/
def entryPost {GF : BundledGFunctors} [WasmGS NearState GF] (Cg arity : Nat) (Ψ : Ending → IProp GF) :
    Post NearState GF where
  normal vs _ := iprop(⌜vs.length = arity⌝ ∗ (∃ R, credits Cg R) ∗ Ψ (.values vs))
  trap := iprop(∀ r, Ψ (.trap r))

section Entry

variable {GF : BundledGFunctors} [ι : WasmGS NearState GF]

theorem step_leave (σ : Store NearState) (lim : ExecLimits) (f : Frame) (arity : Nat) (vs : List Value)
    (hv : vs.length = arity) :
    Exec.step { store := σ, thread := (entryCtx arity).thread f vs (entryCtx arity).labels (entryCtx arity).rest, limits := lim } = .done vs σ := by
  simp only [Exec.step, entryCtx, Ctx.thread, Ctx.threadA, List.nil_append, Exec.leave]
  have := popN_args [] vs
  simp only [List.nil_append] at this
  rw [← hv, this]

/-- The last step of the entry function: its frame is left, and the machine
is done with the values on its stack. -/
theorem mwp_leave_entry (cfg : WasmConfig) (lim : ExecLimits) (f : Frame) (arity : Nat) (vs : List Value)
    (Cg : Nat) (Ψ : Ending → IProp GF) (hv : vs.length = arity) :
    (∃ R, credits Cg R) ∗ ▷ Ψ (.values vs) ⊢ mwpT cfg lim ((entryCtx arity).thread f vs (entryCtx arity).labels (entryCtx arity).rest) Ψ := by
  iintro ⟨⟨%R, Hc⟩, HΨ⟩
  iapply mwp_lift_plain cfg lim ((entryCtx arity).thread f vs (entryCtx arity).labels (entryCtx arity).rest) [] [] (fun _ => [])
    (fun _ => .finished (.values vs)) 0 Cg R (by simp) (by simp) (by simp) (by simp) (by simp)
  · intro σ _ _
    rw [step_leave σ lim f arity vs hv]
    refine ⟨?_, rfl, rfl, fun l _ => by simp [StepResult.store]⟩
    simp [nextInstructionGas, Config.nextInstr?, entryCtx, Ctx.thread, Ctx.threadA, frameTransitionGas]
  · intro σ _ _ l hl _
    simp at hl
  isplitl [Hc]
  · rw [Nat.zero_add]; iexact Hc
  isplitl []
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl []
  · iapply BigSepL.bigSepL_nil.2; iempintro
  inext
  iintro %_ %_ _ _
  iapply mwp_finished
  iexact HΨ

/-- A method's body, proved as a fragment at depth 0, is a `WP` of the
thread that runs it. -/
theorem mwp_entry (cfg : WasmConfig) (lim : ExecLimits) (f : Frame) (arity : Nat) (body : List Instr)
    (Cg : Nat) (Ψ : Ending → IProp GF) :
    instPt (H := NearState) f.inst f.mi ∗ mwpi cfg lim 0 f [] body (entryPost Cg arity Ψ)
      ⊢ mwpT cfg lim (entryThread f arity body) Ψ := by
  iintro ⟨#Hi, Hwp⟩
  iunfold mwpi at Hwp
  have ht : entryThread f arity body =
      (entryCtx arity).thread f [] (entryCtx arity).labels (body ++ (entryCtx arity).rest) := by
    simp [entryThread, entryCtx, Ctx.thread, Ctx.threadA]
  rw [ht]
  iapply Hwp $$ %Ψ %(entryCtx arity) %rfl Hi
  iunfold mKont
  simp only [entryPost]
  isplit
  · iintro %vs %l ⟨%hv, Hc, HΨ⟩
    iapply mwp_leave_entry cfg lim (f.withLocals l) arity vs Cg Ψ hv
    isplitl [Hc]
    · iexact Hc
    · inext
      iexact HΨ
  isplit
  · iintro %n %vs %l HF
    iexfalso
    iexact HF
  isplit
  · iintro %vs %l HF
    iexfalso
    iexact HF
  · iintro HΨ
    iexact HΨ

end Entry

end NearLogic
