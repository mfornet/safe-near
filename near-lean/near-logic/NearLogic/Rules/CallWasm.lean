import NearLogic.Frag
import WasmLogic.Rules.Call

/-!
# Calling a Wasm function, metered

WasmLogic's call rules (`WasmLogic/Rules/Call.lean`) for the metered
language.

- `mwpInvoke` is the metered weakest precondition of a Wasm function from the
  moment its frame is pushed, as WasmLogic's `wpInvoke`; credits are not an
  index of it: they travel inside the function's postcondition `Φf`.
- `Post.mfunc Cg r Φf` translates a body ending into the function returning.
  Every way of leaving the frame is a metered step, which needs the gas cell:
  falling off the end costs nothing, `br` past every label and `return` cost
  one `regular_op_cost`. So each way of ending hands over credits for that
  step, `∃ R, credits Cg (k + R) ∗ (credits Cg R -∗ Φf.ret rs)`.
- `mwpInvoke_intro` (Iris-Wasm's `wp_invoke_native`): a proof of the body as a
  fragment gives the function.
- `mwpi_call`: `call i` to a Wasm function costs `regular_op_cost` plus the
  activation of the new frame, `activationGas cfg.regularOpCost (entryLocals
  code args)`; the caller holds those credits plus `R` and the callee starts
  with `credits Cg R`.
- `MFunSpec` / `mwpi_call_spec`: the modular form. A function proved once,
  persistently, against a precondition `P args`, a cost `K args` and a
  postcondition `Q args rs`, all at depth `d + 1`, is used at a call site at
  depth `d` with credits `regular_op_cost + activation + K args + R`, getting
  back `credits Cg R` and `Q args rs`.
-/

namespace NearLogic

open Wasm Wasm.Near WasmLogic Iris Iris.BI Iris.Std Iris.ProgramLogic
  Iris.ProgramLogic.Language.Notation FromMathlib

/-- What the metered machine does once a function returns `rs`. -/
def mretCode (cfg : WasmConfig) (lim : ExecLimits) (bs rs : List Value) : List CallFrame → MCode
  | [] => .finished (.values rs)
  | f :: fs => .running cfg lim { stack := (bs ++ rs).toArray, frames := f :: fs }

section Defs

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The metered weakest precondition of a Wasm function with `args`, called
at depth `d`, from the moment its frame is pushed. -/
def mwpInvoke (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType) (inst : Nat)
    (mi : ModuleInst) (code : Func) (args : List Value) (Φf : FunPost GF) : IProp GF :=
  iprop(∀ (Ψ : Ending → IProp GF) (bs : List Value) (fs : List CallFrame), ⌜fs.length = d⌝ -∗
    instPt (H := NearState) inst mi -∗
    ((∀ rs, Φf.ret rs -∗ WP (mretCode cfg lim bs rs fs) @ Stuckness.MaybeStuck; ⊤ {{ Ψ }}) ∧
      (Φf.trap -∗ ∀ r, Ψ (.trap r))) -∗
    mwpT cfg lim (calleeThread bs fs type inst code args) Ψ)

/-- How a function body ending translates to the function returning: the
top `r` operands are its results, and the step leaving the frame is paid
from the credits handed over (nothing for falling off the end, one
`regular_op_cost` for `br` or `return`). -/
def Post.mfunc (cfg : WasmConfig) (Cg r : Nat) (Φf : FunPost GF) : Post NearState GF where
  normal vs _ := iprop(⌜r ≤ vs.length⌝ ∗
    ∃ R, credits Cg R ∗ (credits Cg R -∗ Φf.ret (vs.drop (vs.length - r))))
  br _ vs _ := iprop(⌜r ≤ vs.length⌝ ∗
    ∃ R, credits Cg (cfg.regularOpCost + R) ∗ (credits Cg R -∗ Φf.ret (vs.drop (vs.length - r))))
  ret vs _ := iprop(⌜r ≤ vs.length⌝ ∗
    ∃ R, credits Cg (cfg.regularOpCost + R) ∗ (credits Cg R -∗ Φf.ret (vs.drop (vs.length - r))))
  trap := Φf.trap

end Defs

section Step

/-- Leaving a function body: its top `r` operands are its results, at a cost
of `k`. -/
theorem step_leave_body (cfg : WasmConfig) (σ : Store NearState) (lim : ExecLimits)
    (bs : List Value) (fs : List CallFrame) (r : Nat) (g : Frame) (vs : List Value)
    (hr : r ≤ vs.length) (code : List Instr) (k : Nat)
    (hcode : (code = [] ∧ k = 0) ∨ (∃ n, code = [.br n] ∧ k = cfg.regularOpCost) ∨
      (code = [.return] ∧ k = cfg.regularOpCost)) :
    let c : Config NearState := Config.mk σ ((bodyCtx bs fs r).thread g vs [] code) lim
    nextInstructionGas cfg c + frameTransitionGas cfg c (Exec.step c) = k ∧
      ofMachine cfg lim (Exec.step c) = mretCode cfg lim bs (vs.drop (vs.length - r)) fs ∧
      (Exec.step c).store = σ := by
  intro c
  have hs := branch_stack bs vs r hr
  have hv := popN_snd bs vs r hr
  have hs1 : List.take bs.length (Exec.popN (bs ++ vs).toArray r).fst.toList = bs := by
    have := congrArg Array.toList hs
    simpa [hv] using this
  rcases hcode with ⟨rfl, rfl⟩ | ⟨n, rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  · cases fs <;>
      simp [c, Exec.step, Exec.instr, Exec.branch, Exec.leave, bodyCtx, Ctx.thread,
        Ctx.threadA, mretCode, ofMachine, hv, hs1, nextInstructionGas, Config.nextInstr?,
        frameTransitionGas, Config.callDepth, linearInstruction, loopBackedge,
        Config.labelIsLoop, StepResult.store]
    all_goals omega

/-- A call to a Wasm function pushes its frame, as `Exec.step` takes it. -/
theorem step_call_wasm (σ : Store NearState) (lim : ExecLimits) (C : Ctx) (f : Frame)
    (vs₀ args : List Value) (i a : Nat) (type : FuncType) (inst : Nat) (code : Func)
    (hmi : σ.modules[f.inst]? = some f.mi) (ha : f.mi.funcAddrs[i]? = some a)
    (hfn : σ.funcs[a]? = some (.wasm type inst code)) (hlen : args.length = type.params.length)
    (hd : C.below.length + 1 < lim.maxCallDepth) :
    Exec.step (Config.mk σ (C.thread f (vs₀ ++ args) C.labels (.call i :: C.rest)) lim) =
      .next (Config.mk σ
        (calleeThread (C.base ++ vs₀) (callerFrame C f :: C.below) type inst code args) lim) := by
  have he := next_call_wasm σ lim C f vs₀ args
    (C.thread f (vs₀ ++ args) C.labels (.call i :: C.rest)) a type inst code hfn hlen hd
  simp only [Exec.step, Ctx.thread, Ctx.threadA]
  simp only [Exec.instr, modules_get! hmi, ha, Exec.Effect.call]
  simp only [Ctx.thread, Ctx.threadA, callerFrame] at he ⊢
  exact he

/-- The charge of a call to a Wasm function (`call` or `call_indirect`): the
instruction, and the activation of the callee's frame. -/
theorem gas_call_wasm (cfg : WasmConfig) (σ : Store NearState) (lim : ExecLimits) (C : Ctx)
    (f : Frame) (vs vs₀ args : List Value) (ins : Instr) (hi : isFlat ins = true) (type : FuncType)
    (inst : Nat) (code : Func) :
    nextInstructionGas cfg (Config.mk σ (C.thread f vs C.labels (ins :: C.rest)) lim) +
      frameTransitionGas cfg (Config.mk σ (C.thread f vs C.labels (ins :: C.rest)) lim)
        (.next (Config.mk σ
          (calleeThread (C.base ++ vs₀) (callerFrame C f :: C.below) type inst code args) lim)) =
      cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals code args) := by
  rw [nextInstructionGas_flat cfg σ lim C f vs C.labels ins C.rest hi]
  simp [frameTransitionGas, Config.callDepth, Config.locals, calleeThread, Ctx.thread, Ctx.threadA]

theorem mretCode_caller (cfg : WasmConfig) (lim : ExecLimits) (C : Ctx) (f : Frame)
    (vs₀ rs : List Value) :
    mretCode cfg lim (C.base ++ vs₀) rs (callerFrame C f :: C.below) =
      .running cfg lim (C.thread f (vs₀ ++ rs) C.labels C.rest) := by
  simp [mretCode, Ctx.thread, Ctx.threadA, callerFrame]

end Step

section Rules

variable {GF : BundledGFunctors} [ι : WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {Φ : Post NearState GF}

/-- The step leaving a function body, for `k` credits. -/
theorem mwp_leave_body (bs : List Value) (fs : List CallFrame) (r : Nat) (g : Frame)
    (vs : List Value) (hr : r ≤ vs.length) (code : List Instr) (k : Nat)
    (hcode : (code = [] ∧ k = 0) ∨ (∃ n, code = [.br n] ∧ k = cfg.regularOpCost) ∨
      (code = [.return] ∧ k = cfg.regularOpCost)) (Cg R : Nat) (Ψ : Ending → IProp GF) :
    credits Cg (k + R) ∗
      ▷ (credits Cg R -∗ WP (mretCode cfg lim bs (vs.drop (vs.length - r)) fs)
          @ Stuckness.MaybeStuck; ⊤ {{ Ψ }})
      ⊢ mwpT cfg lim ((bodyCtx bs fs r).thread g vs [] code) Ψ := by
  iintro ⟨Hc, HΨ⟩
  iapply mwp_lift_plain cfg lim ((bodyCtx bs fs r).thread g vs [] code) [] [] (fun _ => [])
    (fun _ => mretCode cfg lim bs (vs.drop (vs.length - r)) fs) k Cg R (by simp) (by simp)
    (by simp) (by simp) (by simp)
  · intro σ _ _
    obtain ⟨h1, h2, h3⟩ := step_leave_body cfg σ lim bs fs r g vs hr code k hcode
    exact ⟨h1, h2, by rw [h3], fun l _ => by simp [h3]⟩
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
  iapply HΨ $$ Hc

/-- Iris-Wasm's `wp_invoke_native`, metered: a function is its body run in
its entry frame, ending by falling off, returning, or branching past every
label, each paying for the step that leaves the frame. -/
theorem mwpInvoke_intro (type : FuncType) (inst : Nat) (mi : ModuleInst) (code : Func)
    (args : List Value) (Φf : FunPost GF) (Cg : Nat) :
    mwpi cfg lim d ⟨entryLocals code args, inst, mi⟩ [] code.body
        (Post.mfunc cfg Cg type.results.length Φf)
      ⊢ mwpInvoke cfg lim d type inst mi code args Φf := by
  unfold mwpInvoke
  iintro Hwp %Ψ %bs %fs %hfs #Hi HK
  rw [calleeThread_eq bs fs type inst mi]
  unfold mwpi
  iapply Hwp $$ %Ψ %(bodyCtx bs fs type.results.length) %hfs Hi
  unfold mKont Post.mfunc
  simp only [bodyCtx_labels, bodyCtx_rest]
  isplit
  · iintro %vs %l ⟨%hr, %R, Hc, HΦ⟩
    iapply mwp_leave_body bs fs _ _ vs hr [] 0 (.inl ⟨rfl, rfl⟩) Cg R Ψ
    isplitl [Hc]
    · rw [Nat.zero_add]; iexact Hc
    inext
    iintro Hc
    icases HK with ⟨HK, -⟩
    iapply HK
    iapply HΦ $$ Hc
  isplit
  · iintro %n %vs %l ⟨%hr, %R, Hc, HΦ⟩
    iapply mwp_leave_body bs fs _ _ vs hr [.br n] cfg.regularOpCost (.inr (.inl ⟨n, rfl, rfl⟩))
      Cg R Ψ
    isplitl [Hc]
    · iexact Hc
    inext
    iintro Hc
    icases HK with ⟨HK, -⟩
    iapply HK
    iapply HΦ $$ Hc
  isplit
  · iintro %vs %l ⟨%hr, %R, Hc, HΦ⟩
    iapply mwp_leave_body bs fs _ _ vs hr [.return] cfg.regularOpCost (.inr (.inr ⟨rfl, rfl⟩))
      Cg R Ψ
    isplitl [Hc]
    · iexact Hc
    inext
    iintro Hc
    icases HK with ⟨HK, -⟩
    iapply HK
    iapply HΦ $$ Hc
  · icases HK with ⟨-, HK⟩
    iexact HK

/-- A function's postcondition can be weakened. -/
theorem mwpInvoke_wand (type : FuncType) (inst : Nat) (mi : ModuleInst) (code : Func)
    (args : List Value) {Φf Φf' : FunPost GF} :
    mwpInvoke cfg lim d type inst mi code args Φf ∗
      ((∀ rs, Φf.ret rs -∗ Φf'.ret rs) ∧ (Φf.trap -∗ Φf'.trap))
      ⊢ mwpInvoke cfg lim d type inst mi code args Φf' := by
  unfold mwpInvoke
  iintro ⟨Hwp, Hw⟩ %Ψ %bs %fs %hfs #Hi HK
  iapply Hwp $$ %Ψ %bs %fs %hfs Hi
  isplit
  · iintro %rs H
    icases Hw with ⟨Hw, -⟩
    icases HK with ⟨HK, -⟩
    iapply HK
    iapply Hw $$ H
  · iintro H
    icases Hw with ⟨-, Hw⟩
    icases HK with ⟨-, HK⟩
    iapply HK
    iapply Hw $$ H

/-- Iris-Wasm's `wp_call`, metered: call the module's function `i`, a Wasm
function, for `regular_op_cost` and the activation of its frame. The callee
starts with the credits left over. -/
theorem mwpi_call (i a : Nat) (type : FuncType) (inst : Nat) (mi : ModuleInst) (code : Func)
    (vs₀ args : List Value) {Cg R : Nat} (ha : f.mi.funcAddrs[i]? = some a)
    (hlen : args.length = type.params.length) (hd : d + 1 < lim.maxCallDepth) :
    credits Cg (cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals code args) + R) ∗
      a ↪[wf] FuncInst.wasm type inst code ∗ inst ↪[inst] mi ∗
      ▷ (credits Cg R -∗ mwpInvoke cfg lim (d + 1) type inst mi code args
          { ret := fun rs => Φ.normal (vs₀ ++ rs) f, trap := Φ.trap })
      ⊢ mwpi cfg lim d f (vs₀ ++ args) [.call i] Φ := by
  unfold mwpi mKont
  iintro ⟨Hc, #Hf, #Hi', Hwp⟩ %Ψ %C %hC #Hi HK
  rw [List.singleton_append]
  have hRd : ∀ p ∈ [(Loc.inst f.inst, Cell.inst f.mi),
      (Loc.func a, (Cell.func (.wasm type inst code) : Cell NearState))], isPlain p.1 := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> (unfold isPlain; simp)
  iapply mwp_lift_plain cfg lim (C.thread f (vs₀ ++ args) C.labels (.call i :: C.rest))
    [(Loc.inst f.inst, .inst f.mi), (Loc.func a, .func (.wasm type inst code))] [] (fun _ => [])
    (fun _ => .running cfg lim
      (calleeThread (C.base ++ vs₀) (callerFrame C f :: C.below) type inst code args))
    (cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals code args)) Cg R hRd
    (by simp) (by simp) List.nodup_nil (fun _ => List.nodup_nil)
  · intro σ hR _
    have hmi := hmi_of_see hR
    have hfn : σ.funcs[a]? = some (.wasm type inst code) := by
      have := hR _ (List.mem_cons_of_mem _ List.mem_cons_self)
      simp only [lookup_func, Option.map_eq_some_iff] at this
      obtain ⟨g, hg, he⟩ := this
      cases he; exact hg
    have hstep := step_call_wasm σ lim C f vs₀ args i a type inst code hmi ha hfn hlen (by omega)
    rw [hstep]
    exact ⟨gas_call_wasm cfg σ lim C f _ vs₀ args (.call i) rfl type inst code, rfl, rfl,
      fun l _ => by simp [StepResult.store]⟩
  · intro σ _ _ l hl _
    simp at hl
  isplitl [Hc]
  · iexact Hc
  isplitl []
  · iapply (seeList_cons _ _).2
    iunfold instPt at Hi
    iunfold funcPt at Hf
    isplitr
    · iexact Hi
    · iapply (seeList_cons _ _).2
      isplitr
      · iexact Hf
      · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl []
  · iapply BigSepL.bigSepL_nil.2; iempintro
  inext
  iintro %_ %_ _ Hc
  ispecialize Hwp $$ Hc
  unfold mwpInvoke
  iapply Hwp $$ %Ψ %(C.base ++ vs₀) %(callerFrame C f :: C.below) %(by simp; omega) Hi'
  isplit
  · iintro %rs HΦ
    rw [mretCode_caller]
    icases HK with ⟨HK, -⟩
    ispecialize HK $$ %(vs₀ ++ rs) %f.locals
    simp only [Frame.withLocals_self]
    iapply HK $$ HΦ
  · icases HK with ⟨-, -, -, HK⟩
    iexact HK

/-- Iris-Wasm's `wp_call_indirect_success`, metered: the table entry names a
Wasm function of the expected type. -/
theorem mwpi_call_indirect (ty t ta : Nat) (idx : UInt32) (a : Nat) (type : FuncType) (inst : Nat)
    (mi : ModuleInst) (code : Func) (vs₀ args : List Value) {Cg R : Nat}
    (hta : f.mi.tableAddrs[t]? = some ta) (hty : type = f.mi.types[ty]!)
    (hlen : args.length = type.params.length) (hd : d + 1 < lim.maxCallDepth) :
    credits Cg (cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals code args) + R) ∗
      ta ↦[wt][ idx.toNat ] Ref.func a ∗ a ↪[wf] FuncInst.wasm type inst code ∗ inst ↪[inst] mi ∗
      ▷ (ta ↦[wt][ idx.toNat ] Ref.func a -∗ credits Cg R -∗
          mwpInvoke cfg lim (d + 1) type inst mi code args
            { ret := fun rs => Φ.normal (vs₀ ++ rs) f, trap := Φ.trap })
      ⊢ mwpi cfg lim d f (vs₀ ++ args ++ [.i32 idx]) [.call_indirect ty t] Φ := by
  unfold mwpi mKont
  iintro ⟨Hc, Ht, #Hf, #Hi', Hwp⟩ %Ψ %C %hC #Hi HK
  rw [List.singleton_append]
  have hRd : ∀ p ∈ [(Loc.inst f.inst, Cell.inst f.mi),
      (Loc.func a, (Cell.func (.wasm type inst code) : Cell NearState))], isPlain p.1 := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl <;> (unfold isPlain; simp)
  have hPp : ∀ p ∈ [(Loc.tableElem ta idx.toNat, (Cell.ref (.func a) : Cell NearState))],
      isPlain p.1 := by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp; unfold isPlain; simp
  iapply mwp_lift_plain cfg lim
    (C.thread f (vs₀ ++ args ++ [.i32 idx]) C.labels (.call_indirect ty t :: C.rest))
    [(Loc.inst f.inst, .inst f.mi), (Loc.func a, .func (.wasm type inst code))]
    [(Loc.tableElem ta idx.toNat, .ref (.func a))]
    (fun _ => [(Loc.tableElem ta idx.toNat, .ref (.func a))])
    (fun _ => .running cfg lim
      (calleeThread (C.base ++ vs₀) (callerFrame C f :: C.below) type inst code args))
    (cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals code args)) Cg R hRd
    hPp (fun _ => hPp) (by simp) (fun _ => by simp)
  · intro σ hR hP
    have hmi := hmi_of_see hR
    have hfn : σ.funcs[a]? = some (.wasm type inst code) := by
      have := hR _ (List.mem_cons_of_mem _ List.mem_cons_self)
      simp only [lookup_func, Option.map_eq_some_iff] at this
      obtain ⟨g, hg, he⟩ := this
      cases he; exact hg
    have htab := hP _ List.mem_cons_self
    simp only [lookup_tableElem, Option.bind_eq_some_iff, Option.map_eq_some_iff] at htab
    obtain ⟨table, htable, r, hr, hre⟩ := htab
    cases hre
    have hinstr : Exec.instr σ f.mi f.locals (C.base ++ (vs₀ ++ args ++ [Value.i32 idx])).toArray
        C.labels (.call_indirect ty t) C.rest = ⟨σ, .call (C.base ++ (vs₀ ++ args)).toArray a C.rest⟩ := by
      simp [Exec.instr, Exec.tableOf, hta, htable, Exec.i32, hr, hfn, ← hty, FuncInst.type]
    have he := next_call_wasm σ lim C f vs₀ args
      (C.thread f (vs₀ ++ args ++ [.i32 idx]) C.labels (.call_indirect ty t :: C.rest)) a type inst
      code hfn hlen (by omega)
    have hstep : Exec.step (Config.mk σ
        (C.thread f (vs₀ ++ args ++ [.i32 idx]) C.labels (.call_indirect ty t :: C.rest)) lim) =
        .next (Config.mk σ
          (calleeThread (C.base ++ vs₀) (callerFrame C f :: C.below) type inst code args) lim) := by
      simp only [Exec.step, Ctx.thread, Ctx.threadA, modules_get! hmi]
      rw [hinstr]
      simp only [Ctx.thread, Ctx.threadA, callerFrame] at he ⊢
      exact he
    rw [hstep]
    refine ⟨gas_call_wasm cfg σ lim C f _ vs₀ args (.call_indirect ty t) rfl type inst code, rfl, rfl,
      fun l _ => ?_⟩
    simp only [StepResult.store]
    cases hq : ([(Loc.tableElem ta idx.toNat, (Cell.ref (.func a) : Cell NearState))]).lookup l with
    | none => simp_all
    | some c =>
      have := hP _ (mem_of_lookup hq)
      simp only at this
      simp [this]
  · intro σ _ _ l hq hp
    simp_all
  isplitl [Hc]
  · iexact Hc
  isplitl []
  · iapply (seeList_cons _ _).2
    iunfold instPt at Hi
    iunfold funcPt at Hf
    isplitr
    · iexact Hi
    · iapply (seeList_cons _ _).2
      isplitr
      · iexact Hf
      · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Ht]
  · iunfold tablePt at Ht
    iapply BigSepL.bigSepL_cons.2
    isplitl [Ht]
    · iexact Ht
    · iapply BigSepL.bigSepL_nil.2; iempintro
  inext
  iintro %_ %_ HQ Hc
  icases BigSepL.bigSepL_cons.1 $$ HQ with ⟨HQ, -⟩
  iunfold tablePt at Hwp
  ispecialize Hwp $$ HQ Hc
  unfold mwpInvoke
  iapply Hwp $$ %Ψ %(C.base ++ vs₀) %(callerFrame C f :: C.below) %(by simp; omega) Hi'
  isplit
  · iintro %rs HΦ
    rw [mretCode_caller]
    icases HK with ⟨HK, -⟩
    ispecialize HK $$ %(vs₀ ++ rs) %f.locals
    simp only [Frame.withLocals_self]
    iapply HK $$ HΦ
  · icases HK with ⟨-, -, -, HK⟩
    iexact HK

/-! ## Function specifications -/

/-- A Wasm function's metered specification at call depth `d`: for any
arguments satisfying `P` and any credits `K args + R`, the function returns
`rs` with `Q args rs`, giving back `credits Cg R`. Persistent: proved once,
used at every call site. -/
def MFunSpec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType) (inst : Nat)
    (mi : ModuleInst) (code : Func) (Cg : Nat) (P : List Value → IProp GF) (K : List Value → Nat)
    (Q : List Value → List Value → IProp GF) : IProp GF :=
  iprop(□ ∀ args R, P args -∗ credits Cg (K args + R) -∗
    mwpInvoke cfg lim d type inst mi code args { ret := fun rs => iprop(credits Cg R ∗ Q args rs) })

/-- Proving a specification from the body: falling off the end with the
results on top, or returning, with `Q` and the credits left over. -/
theorem MFunSpec_intro (type : FuncType) (inst : Nat) (mi : ModuleInst) (code : Func) (Cg : Nat)
    (P : List Value → IProp GF) (K : List Value → Nat) (Q : List Value → List Value → IProp GF) :
    (□ ∀ args R, P args -∗ credits Cg (K args + R) -∗
      mwpi cfg lim d ⟨entryLocals code args, inst, mi⟩ [] code.body
        (Post.mfunc cfg Cg type.results.length { ret := fun rs => iprop(credits Cg R ∗ Q args rs) }))
      ⊢ MFunSpec cfg lim d type inst mi code Cg P K Q := by
  unfold MFunSpec
  iintro #H
  imodintro
  iintro %args %R HP Hc
  iapply mwpInvoke_intro
  iapply H $$ %args %R HP Hc

/-- A call to a function with a specification: the caller pays the call, the
activation and the function's cost `K args`, and keeps `R`. -/
theorem mwpi_call_spec (i a : Nat) (type : FuncType) (inst : Nat) (mi : ModuleInst) (code : Func)
    (vs₀ args : List Value) {Cg R : Nat} (P : List Value → IProp GF) (K : List Value → Nat)
    (Q : List Value → List Value → IProp GF) (ha : f.mi.funcAddrs[i]? = some a)
    (hlen : args.length = type.params.length) (hd : d + 1 < lim.maxCallDepth) :
    credits Cg (cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals code args) +
        (K args + R)) ∗
      a ↪[wf] FuncInst.wasm type inst code ∗ inst ↪[inst] mi ∗
      MFunSpec cfg lim (d + 1) type inst mi code Cg P K Q ∗ P args ∗
      ▷ (∀ rs, credits Cg R -∗ Q args rs -∗ Φ.normal (vs₀ ++ rs) f)
      ⊢ mwpi cfg lim d f (vs₀ ++ args) [.call i] Φ := by
  iintro ⟨Hc, #Hf, #Hi, Hs, HP, HΦ⟩
  iapply mwpi_call i a type inst mi code vs₀ args ha hlen hd
  isplitl [Hc]
  · iexact Hc
  isplitr
  · iexact Hf
  isplitr
  · iexact Hi
  inext
  iintro Hc
  iapply mwpInvoke_wand
  isplitl [HP Hc Hs]
  · iunfold MFunSpec at Hs
    icases Hs with #Hs
    iapply Hs $$ %args %R HP Hc
  isplit
  · iintro %rs ⟨Hc, HQ⟩
    iapply HΦ $$ %rs Hc HQ
  · iintro HF
    iexfalso
    iexact HF

end Rules

end NearLogic
