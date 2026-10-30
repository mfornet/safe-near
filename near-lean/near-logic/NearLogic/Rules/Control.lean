import NearLogic.Frag
import WasmLogic.Rules.Control

/-!
# Rules for structured control, metered

WasmLogic's control rules (`WasmLogic/Rules/Control.lean`) over the metered
language, with their charges (`nextInstructionGas`): `block` is free, `if`,
`loop`, `br_if` not taken cost one `regular_op_cost`, popping a finished
label is free, a branch costs one `regular_op_cost`, two for a back-edge to a
loop label.

Where branches are paid. `br n`, `return`, a taken `br_if` and `br_table`
hand control to the context's continuation (`mKont`), which runs the thread
`[.br n]` (or `[.return]`); that thread's step is the one charged, and it is
charged the same as the original instruction. So these rules need no
credits (`mwpi_br`: `Φ.br n vs f ⊢ mwpi … [.br n] Φ`, as in WasmLogic); the
step is proved by congruence (`mwp_running_congr`: same charge, same depth,
same `next`). The charge falls where the label is consumed, and the
postcondition of a body carries the credits for it, as `pay Cg k P`
(`k` more gas, the rest passed on to `P`):

* `Post.mblock`: falling through needs `pay Cg 0` (the free step that pops
  the label still needs the gas cell); `br 0` needs `pay Cg regularOpCost`;
  outer branches and returns pass through unchanged.
* `Post.mloop`: `br 0` is a back-edge, `pay Cg (2 * regularOpCost)` of the
  loop's invariant `I`. The back-edge step goes straight into the body, so
  a loop is not "the `loop` instruction again" as in WasmLogic: `mwpi_loop`
  takes the invariant `I` (operands, frame) and the body proved once,
  persistently, from `I`, and runs it any number of times by Löb induction.

Instruction rules otherwise take `credits Cg (cost + R)` and give the
continuation `credits Cg R` (`mwpi_block`, cost 0, takes `credits Cg R`).
-/

namespace NearLogic

open Wasm Wasm.Near WasmLogic Iris Iris.BI Iris.Std Iris.ProgramLogic
  Iris.ProgramLogic.Language.Notation FromMathlib

section Thread

variable {GF : BundledGFunctors} [ι : WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits}

/-- Two threads whose charge, depth and step agree take the same metered
step, from a store with the plain cells `Rd`. -/
theorem mnext_congr (σ : MStore) {t₁ t₂ : Thread} (Rd : List (Loc × Cell NearState))
    (hRd : ∀ p ∈ Rd, isPlain p.1) (hσ : ∀ p ∈ Rd, lookup σ.store p.1 = some p.2)
    (hg : nextInstructionGas cfg { store := σ.store, thread := t₁, limits := lim } =
      nextInstructionGas cfg { store := σ.store, thread := t₂, limits := lim })
    (hd : t₁.frames.length = t₂.frames.length)
    (hn : ∀ s : Store NearState, (∀ p ∈ Rd, lookup s p.1 = some p.2) →
      next s lim t₁ = next s lim t₂) :
    mnext σ cfg lim t₁ = mnext σ cfg lim t₂ := by
  unfold mnext
  simp only [chargeConfig]
  rw [hg]
  generalize chargeHost σ.store.host _ = r
  obtain ⟨h', e⟩ := r
  cases e with
  | some e => rfl
  | none =>
    have := hn { σ.store with host := h' } (fun p hp => by
      rw [lookup_plain_host _ _ (hRd p hp)]; exact hσ p hp)
    simp only [next, Code.config] at this
    simp only
    generalize Exec.step { store := { σ.store with host := h' }, thread := t₁, limits := lim } = m₁
      at this ⊢
    generalize Exec.step { store := { σ.store with host := h' }, thread := t₂, limits := lim } = m₂
      at this ⊢
    cases m₁ <;> cases m₂ <;> simp at this
    · obtain ⟨h1, h2⟩ := this
      simp [chargeWasm, chargeConfig, frameTransitionGas, Config.callDepth, Config.locals, ofMachine,
        StepResult.store, hd, h1, h2]
    · obtain ⟨h1, h2⟩ := this
      subst h1 h2; rfl
    · obtain ⟨h1, h2⟩ := this
      subst h1 h2; rfl

/-- Congruence under persistently seen plain cells. -/
theorem mwp_running_congr_see {t₁ t₂ : Thread} {Ψ : Ending → IProp GF}
    (Rd : List (Loc × Cell NearState)) (hRd : ∀ p ∈ Rd, isPlain p.1)
    (hg : ∀ s, nextInstructionGas cfg { store := s, thread := t₁, limits := lim } =
      nextInstructionGas cfg { store := s, thread := t₂, limits := lim })
    (hd : t₁.frames.length = t₂.frames.length)
    (hn : ∀ s : Store NearState, (∀ p ∈ Rd, lookup s p.1 = some p.2) →
      next s lim t₁ = next s lim t₂) :
    seeList Rd ∗ mwpT cfg lim t₂ Ψ ⊢ mwpT cfg lim t₁ Ψ := by
  unfold mwpT
  rw [(wp_unfold (e := MCode.running cfg lim t₁)).to_eq,
    (wp_unfold (e := MCode.running cfg lim t₂)).to_eq]
  simp only [wp.pre, ToVal.toVal]
  iintro ⟨HRd, H⟩ %σ %ns %obs %obs' %nt Hσ
  ihave %hR := mseeList_lookup σ Rd $$ Hσ HRd
  imod H $$ %σ %ns %obs %obs' %nt Hσ with ⟨_, H⟩
  imodintro
  isplitr
  · ipureintro
    trivial
  iintro %e₂ %σ₂ %eₜ %Hstep
  iapply H
  ipureintro
  obtain ⟨h1, h2, h3⟩ := step_iff.mp Hstep
  refine step_iff.mpr ⟨h1, h2, h3.trans (mnext_congr σ Rd hRd (fun p hp => ?_) (hg _) hd hn)⟩
  rw [← mlookup_plain σ (hRd p hp)]; exact hR p hp

theorem mwp_running_congr {t₁ t₂ : Thread} {Ψ : Ending → IProp GF}
    (hg : ∀ s, nextInstructionGas cfg { store := s, thread := t₁, limits := lim } =
      nextInstructionGas cfg { store := s, thread := t₂, limits := lim })
    (hd : t₁.frames.length = t₂.frames.length)
    (hn : ∀ s : Store NearState, next s lim t₁ = next s lim t₂) :
    mwpT cfg lim t₂ Ψ ⊢ mwpT cfg lim t₁ Ψ := by
  iintro H
  iapply mwp_running_congr_see [] (by simp) hg hd (fun s _ => hn s)
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  · iexact H

/-- A step that only moves the thread, at a known charge `k`, from every
store with the plain cells `Rd`. -/
theorem mwpT_step {t t' : Thread} {Ψ : Ending → IProp GF} (Rd : List (Loc × Cell NearState))
    (hRd : ∀ p ∈ Rd, isPlain p.1) (k Cg R : Nat)
    (hk : ∀ s, nextInstructionGas cfg { store := s, thread := t, limits := lim } = k)
    (hd : t'.frames.length = t.frames.length)
    (h : ∀ s : Store NearState, (∀ p ∈ Rd, lookup s p.1 = some p.2) →
      next s lim t = (.running lim t', s)) :
    credits Cg (k + R) ∗ seeList Rd ∗ ▷ (credits Cg R -∗ mwpT cfg lim t' Ψ) ⊢ mwpT cfg lim t Ψ := by
  iintro ⟨Hc, HRd, Hwp⟩
  iapply mwp_lift_plain cfg lim t Rd [] (fun _ => []) (fun _ => .running cfg lim t') k Cg R hRd
    (by simp) (by simp) List.nodup_nil (fun _ => List.nodup_nil)
  · intro σ hR _
    have h' := h σ hR
    simp only [next, Code.config] at h'
    rw [hk]
    generalize Exec.step { store := σ, thread := t, limits := lim } = m at h' ⊢
    cases m with
    | next c =>
      simp only [Prod.mk.injEq, Code.running.injEq] at h'
      obtain ⟨⟨-, h1⟩, h2⟩ := h'
      refine ⟨?_, ?_, ?_, fun l _ => ?_⟩
      · simp [frameTransitionGas, Config.callDepth, h1, hd]
      · simp [ofMachine, h1]
      · simp [StepResult.store, h2]
      · simp [StepResult.store, h2]
    | done => simp at h'
    | trap => simp at h'
  · intro σ _ _ l hl _
    simp at hl
  isplitl [Hc]
  · iexact Hc
  isplitl [HRd]
  · iexact HRd
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  inext
  iintro %_ %_ _ Hc
  iapply Hwp $$ Hc

end Thread

section Rules

variable {GF : BundledGFunctors} [ι : WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {vs : List Value}
  {Φ : Post NearState GF} {Cg R : Nat}

/-- `br n` is the context's branch continuation; its charge is paid where
the label is consumed. -/
theorem mwpi_br (n : Nat) : Φ.br n vs f ⊢ mwpi cfg lim d f vs [.br n] Φ := by
  unfold mwpi mKont
  iintro HΦ %Ψ %C %_ #_ HK
  icases HK with ⟨-, ⟨HK, -⟩⟩
  ispecialize HK $$ %n %vs %f.locals
  simp only [Frame.withLocals_self]
  ispecialize HK $$ HΦ
  rw [List.singleton_append]
  iapply mwp_running_congr
    (fun s => by simp [nextInstructionGas, Config.nextInstr?, Config.labelIsLoop, loopBackedge,
      linearInstruction, Ctx.thread, Ctx.threadA]; split_ifs <;> simp_all)
    (by simp [Ctx.thread, Ctx.threadA]) (fun σ => next_br_rest σ lim C f vs C.labels n C.rest)
  iexact HK

theorem mwpi_return : Φ.ret vs f ⊢ mwpi cfg lim d f vs [.return] Φ := by
  unfold mwpi mKont
  iintro HΦ %Ψ %C %_ #_ HK
  icases HK with ⟨-, -, ⟨HK, -⟩⟩
  ispecialize HK $$ %vs %f.locals
  simp only [Frame.withLocals_self]
  ispecialize HK $$ HΦ
  rw [List.singleton_append]
  iapply mwp_running_congr
    (fun s => by simp [nextInstructionGas, Config.nextInstr?, loopBackedge, linearInstruction,
      Ctx.thread, Ctx.threadA])
    (by simp [Ctx.thread, Ctx.threadA]) (fun σ => next_return_rest σ lim C f vs C.labels C.rest)
  iexact HK

theorem mwpi_br_if_true (n : Nat) (c : UInt32) (hc : c ≠ 0) :
    Φ.br n vs f ⊢ mwpi cfg lim d f (vs ++ [.i32 c]) [.br_if n] Φ := by
  unfold mwpi mKont
  iintro HΦ %Ψ %C %_ #_ HK
  icases HK with ⟨-, ⟨HK, -⟩⟩
  ispecialize HK $$ %n %vs %f.locals
  simp only [Frame.withLocals_self]
  ispecialize HK $$ HΦ
  rw [List.singleton_append]
  iapply mwp_running_congr
    (fun s => by simp [nextInstructionGas, Config.nextInstr?, Config.labelIsLoop, Config.stackTop?,
      loopBackedge, linearInstruction, Ctx.thread, Ctx.threadA, hc]; split_ifs <;> simp_all)
    (by simp [Ctx.thread, Ctx.threadA]) (fun σ => next_br_if σ lim C f vs C.labels n c hc C.rest)
  iexact HK

theorem mwpi_br_table (ls : List Nat) (dflt : Nat) (c : UInt32) :
    Φ.br (ls[c.toNat]?.getD dflt) vs f ⊢ mwpi cfg lim d f (vs ++ [.i32 c]) [.br_table ls dflt] Φ := by
  unfold mwpi mKont
  iintro HΦ %Ψ %C %_ #_ HK
  icases HK with ⟨-, ⟨HK, -⟩⟩
  ispecialize HK $$ %(ls[c.toNat]?.getD dflt) %vs %f.locals
  simp only [Frame.withLocals_self]
  ispecialize HK $$ HΦ
  rw [List.singleton_append]
  iapply mwp_running_congr
    (fun s => by simp [nextInstructionGas, Config.nextInstr?, Config.labelIsLoop, Config.stackTop?,
      loopBackedge, linearInstruction, Ctx.thread, Ctx.threadA]; split_ifs <;> simp_all)
    (by simp [Ctx.thread, Ctx.threadA]) (fun σ => next_br_table σ lim C f vs C.labels ls dflt c C.rest)
  iexact HK

theorem next_br_if_false (σ : Store NearState) (C : Ctx) (f : Frame) (vs : List Value)
    (L : List Label) (n : Nat) (R : List Instr) :
    next σ lim (C.thread f (vs ++ [.i32 0]) L (.br_if n :: R)) =
      (.running lim (C.thread f vs L R), σ) := by
  simp only [next, Code.config, Exec.step, Exec.instr, Exec.i32, Ctx.thread, Ctx.threadA]
  simp [← List.append_assoc]

/-- A `br_if` not taken costs one `regular_op_cost`. -/
theorem mwpi_br_if_false (n : Nat) :
    credits Cg (cfg.regularOpCost + R) ∗ ▷ (credits Cg R -∗ Φ.normal vs f)
      ⊢ mwpi cfg lim d f (vs ++ [.i32 0]) [.br_if n] Φ := by
  unfold mwpi mKont
  iintro ⟨Hc, HΦ⟩ %Ψ %C %_ #_ HK
  icases HK with ⟨HK, -⟩
  rw [List.singleton_append]
  iapply mwpT_step [] (by simp) cfg.regularOpCost Cg R
    (fun s => by simp [nextInstructionGas, Config.nextInstr?, Config.stackTop?, loopBackedge,
      linearInstruction, Ctx.thread, Ctx.threadA])
    (by simp [Ctx.thread, Ctx.threadA]) (fun σ _ => next_br_if_false σ C f vs C.labels n C.rest)
  isplitl [Hc]
  · iexact Hc
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  inext
  iintro Hc
  ispecialize HK $$ %vs %f.locals
  simp only [Frame.withLocals_self]
  iapply HK
  iapply HΦ $$ Hc


/-- `P` once `k` more gas is paid, with what is left over: the credits a
label's consumer needs, carried by the postcondition. -/
def pay (Cg k : Nat) (P : IProp GF) : IProp GF :=
  iprop(∃ R, credits Cg (k + R) ∗ ▷ (credits Cg R -∗ P))

/-- How a block's body ending translates to the block ending. Falling off
the end pops the label, a free step that still needs the gas cell (`pay 0`);
branching to the label costs one `regular_op_cost`. -/
def Post.mblock (cfg : WasmConfig) (Cg r : Nat) (vs₀ : List Value) (Φ : Post NearState GF) :
    Post NearState GF where
  normal vs g := pay Cg 0 (Φ.normal (vs₀ ++ vs) g)
  br n X g := match n with
    | 0 => iprop(⌜r ≤ X.length⌝ ∗ pay Cg cfg.regularOpCost (Φ.normal (vs₀ ++ X.drop (X.length - r)) g))
    | n + 1 => Φ.br n (vs₀ ++ X) g
  ret X g := Φ.ret (vs₀ ++ X) g
  trap := Φ.trap

/-- The common part of `block` and `if`: the body runs under the block's label. -/
theorem mblock_body (C : Ctx) (vs₀ : List Value) (r : Nat) (Ψ : Ending → IProp GF) :
    mKont cfg lim C f Φ Ψ ⊢
      mKont cfg lim (C.enter vs₀ (blockLabel C vs₀ r none)) f (Post.mblock cfg Cg r vs₀ Φ) Ψ := by
  unfold mKont
  simp only [Post.mblock]
  iintro HK
  isplit
  · iintro %vs' %l HΦ
    simp only [Ctx.enter_labels, Ctx.enter_rest]
    iunfold pay at HΦ
    icases HΦ with ⟨%R', Hc, HΦ⟩
    iapply mwpT_step [] (by simp) 0 Cg R'
      (fun s => by simp [nextInstructionGas, Config.nextInstr?, Ctx.thread, Ctx.threadA])
      (by simp [Ctx.thread, Ctx.threadA, Ctx.enter])
      (fun σ _ => next_pop_label σ lim C (f.withLocals l) vs₀ vs' _ C.labels)
    isplitl [Hc]
    · iexact Hc
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    inext
    iintro Hc
    icases HK with ⟨HK, -⟩
    simp only [blockLabel_rest]
    iapply HK $$ %(vs₀ ++ vs') %l
    iapply HΦ $$ Hc
  isplit
  · iintro %n %X %l HΦ
    simp only [Ctx.enter_labels]
    rcases n with _ | n
    · iunfold pay at HΦ
      icases HΦ with ⟨%hr, %R', Hc, HΦ⟩
      iapply mwpT_step [] (by simp) cfg.regularOpCost Cg R'
        (fun s => by simp [nextInstructionGas, Config.nextInstr?, Config.labelIsLoop, loopBackedge,
          linearInstruction, Ctx.thread, Ctx.threadA, Ctx.enter, blockLabel])
        (by simp [Ctx.thread, Ctx.threadA, Ctx.enter])
        (fun σ _ => next_br_zero σ lim C (f.withLocals l) vs₀ X _ C.labels rfl rfl (by simpa using hr))
      isplitl [Hc]
      · iexact Hc
      isplitr
      · iapply BigSepL.bigSepL_nil.2; iempintro
      inext
      iintro Hc
      icases HK with ⟨HK, -⟩
      simp only [blockLabel_rest, blockLabel_arity]
      iapply HK $$ %(vs₀ ++ X.drop (X.length - r)) %l
      iapply HΦ $$ Hc
    · iapply mwp_running_congr
        (fun s => by simp [nextInstructionGas, Config.nextInstr?, Config.labelIsLoop, loopBackedge,
          linearInstruction, Ctx.thread, Ctx.threadA, Ctx.enter]; split_ifs <;> simp_all)
        (by simp [Ctx.thread, Ctx.threadA, Ctx.enter])
        (fun σ => next_br_succ σ lim C (f.withLocals l) vs₀ X _ C.labels n)
      icases HK with ⟨-, ⟨HK, -⟩⟩
      iapply HK $$ %n %(vs₀ ++ X) %l HΦ
  isplit
  · iintro %X %l HΦ
    simp only [Ctx.enter_labels]
    iapply mwp_running_congr
      (fun s => by simp [nextInstructionGas, Config.nextInstr?, loopBackedge, linearInstruction,
        Ctx.thread, Ctx.threadA])
      (by simp [Ctx.thread, Ctx.threadA, Ctx.enter])
      (fun σ => next_return_label σ lim C (f.withLocals l) vs₀ X _ C.labels)
    icases HK with ⟨-, -, ⟨HK, -⟩⟩
    iapply HK $$ %(vs₀ ++ X) %l HΦ
  · icases HK with ⟨-, -, -, HK⟩
    iexact HK

theorem inst_plain (f : Frame) : ∀ p ∈ [(Loc.inst f.inst, Cell.inst (H := NearState) f.mi)],
    isPlain p.1 := by
  intro p hp
  simp only [List.mem_singleton] at hp
  subst hp
  unfold isPlain; simp

/-- `block` costs nothing, but its step needs the gas cell. -/
theorem mwpi_block (bt : BlockType) (body : List Instr) (vs₀ args : List Value)
    (hp : args.length = (Exec.blockType f.mi bt).params.length) :
    credits Cg R ∗ ▷ (credits Cg R -∗
        mwpi cfg lim d f args body (Post.mblock cfg Cg (Exec.blockType f.mi bt).results.length vs₀ Φ))
      ⊢ mwpi cfg lim d f (vs₀ ++ args) [.block bt body] Φ := by
  iintro ⟨Hc, Hwp⟩
  unfold mwpi
  iintro %Ψ %C %hC #Hi HK
  rw [List.singleton_append]
  iapply mwpT_step [(Loc.inst f.inst, .inst f.mi)] (inst_plain f) 0 Cg R
    (fun s => by simp [nextInstructionGas, Config.nextInstr?, Ctx.thread, Ctx.threadA])
    (by simp [Ctx.thread, Ctx.threadA, Ctx.enter])
    (fun σ hRd => next_block σ lim C f vs₀ args bt body (hmi_of_see hRd) hp)
  isplitl [Hc]
  · simp only [Nat.zero_add]; iexact Hc
  isplitr
  · iapply seeInst $$ Hi
  inext
  iintro Hc
  ispecialize Hwp $$ Hc
  ispecialize Hwp $$ %Ψ %(C.enter vs₀ (blockLabel C vs₀ (Exec.blockType f.mi bt).results.length none))
    %(by simpa using hC) Hi
  simp only [Ctx.enter_labels, Ctx.enter_rest]
  iapply Hwp
  iapply mblock_body $$ HK

/-- `if`, taken: one `regular_op_cost`. -/
theorem mwpi_if_true (bt : BlockType) (th el : List Instr) (vs₀ args : List Value) (c : UInt32)
    (hc : c ≠ 0) (hp : args.length = (Exec.blockType f.mi bt).params.length) :
    credits Cg (cfg.regularOpCost + R) ∗ ▷ (credits Cg R -∗
        mwpi cfg lim d f args th (Post.mblock cfg Cg (Exec.blockType f.mi bt).results.length vs₀ Φ))
      ⊢ mwpi cfg lim d f (vs₀ ++ args ++ [.i32 c]) [.«if» bt th el] Φ := by
  iintro ⟨Hc, Hwp⟩
  unfold mwpi
  iintro %Ψ %C %hC #Hi HK
  rw [List.singleton_append]
  have hn := fun σ (hRd : ∀ p ∈ [(Loc.inst f.inst, Cell.inst (H := NearState) f.mi)],
      lookup σ p.1 = some p.2) => next_if σ lim C f vs₀ args c bt th el (hmi_of_see hRd) hp
  simp only [bne_iff_ne, ne_eq, hc, not_false_eq_true, ite_true] at hn
  iapply mwpT_step [(Loc.inst f.inst, .inst f.mi)] (inst_plain f) cfg.regularOpCost Cg R
    (fun s => by simp [nextInstructionGas, Config.nextInstr?, loopBackedge, linearInstruction,
      Ctx.thread, Ctx.threadA])
    (by simp [Ctx.thread, Ctx.threadA, Ctx.enter])
    hn
  isplitl [Hc]
  · iexact Hc
  isplitr
  · iapply seeInst $$ Hi
  inext
  iintro Hc
  ispecialize Hwp $$ Hc
  ispecialize Hwp $$ %Ψ %(C.enter vs₀ (blockLabel C vs₀ (Exec.blockType f.mi bt).results.length none))
    %(by simpa using hC) Hi
  simp only [Ctx.enter_labels, Ctx.enter_rest]
  iapply Hwp
  iapply mblock_body $$ HK

/-- `if`, not taken: one `regular_op_cost`. -/
theorem mwpi_if_false (bt : BlockType) (th el : List Instr) (vs₀ args : List Value)
    (hp : args.length = (Exec.blockType f.mi bt).params.length) :
    credits Cg (cfg.regularOpCost + R) ∗ ▷ (credits Cg R -∗
        mwpi cfg lim d f args el (Post.mblock cfg Cg (Exec.blockType f.mi bt).results.length vs₀ Φ))
      ⊢ mwpi cfg lim d f (vs₀ ++ args ++ [.i32 0]) [.«if» bt th el] Φ := by
  iintro ⟨Hc, Hwp⟩
  unfold mwpi
  iintro %Ψ %C %hC #Hi HK
  rw [List.singleton_append]
  have hn := fun σ (hRd : ∀ p ∈ [(Loc.inst f.inst, Cell.inst (H := NearState) f.mi)],
      lookup σ p.1 = some p.2) => next_if σ lim C f vs₀ args 0 bt th el (hmi_of_see hRd) hp
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false] at hn
  iapply mwpT_step [(Loc.inst f.inst, .inst f.mi)] (inst_plain f) cfg.regularOpCost Cg R
    (fun s => by simp [nextInstructionGas, Config.nextInstr?, loopBackedge, linearInstruction,
      Ctx.thread, Ctx.threadA])
    (by simp [Ctx.thread, Ctx.threadA, Ctx.enter])
    hn
  isplitl [Hc]
  · iexact Hc
  isplitr
  · iapply seeInst $$ Hi
  inext
  iintro Hc
  ispecialize Hwp $$ Hc
  ispecialize Hwp $$ %Ψ %(C.enter vs₀ (blockLabel C vs₀ (Exec.blockType f.mi bt).results.length none))
    %(by simpa using hC) Hi
  simp only [Ctx.enter_labels, Ctx.enter_rest]
  iapply Hwp
  iapply mblock_body $$ HK


/-- How a loop's body ending translates to the loop ending. Branching to the
loop's label is a back-edge, two `regular_op_cost`s, that enters the body
again from the loop's invariant `I` (operands, frame); the body is proved
once, from `I`, in `mwpi_loop`. -/
def Post.mloop (cfg : WasmConfig) (Cg p : Nat) (vs₀ : List Value) (I : List Value → Frame → IProp GF)
    (Φ : Post NearState GF) : Post NearState GF where
  normal vs g := pay Cg 0 (Φ.normal (vs₀ ++ vs) g)
  br n X g := match n with
    | 0 => iprop(⌜p ≤ X.length⌝ ∗ pay Cg (2 * cfg.regularOpCost) (I (X.drop (X.length - p)) g))
    | n + 1 => Φ.br n (vs₀ ++ X) g
  ret X g := Φ.ret (vs₀ ++ X) g
  trap := Φ.trap

/-- The loop's body, run from the invariant any number of times (Löb). -/
theorem loop_run (C : Ctx) (hC : C.below.length = d) (bt : BlockType) (body : List Instr)
    (vs₀ : List Value) (I : List Value → Frame → IProp GF) (Ψ : Ending → IProp GF) :
    ⊢ □ (∀ X l, I X (f.withLocals l) -∗ mwpi cfg lim d (f.withLocals l) X body
          (Post.mloop cfg Cg (Exec.blockType f.mi bt).params.length vs₀ I Φ)) -∗
      instPt (H := NearState) f.inst f.mi -∗
      ∀ X l, ⌜X.length = (Exec.blockType f.mi bt).params.length⌝ -∗ I X (f.withLocals l) -∗
        mKont cfg lim C f Φ Ψ -∗
        mwpT cfg lim ((C.enter vs₀ (blockLabel C vs₀ (Exec.blockType f.mi bt).params.length
          (some body))).thread (f.withLocals l) X
          (blockLabel C vs₀ (Exec.blockType f.mi bt).params.length (some body) :: C.labels)
          (body ++ [])) Ψ := by
  iintro #Hb #Hi
  iloeb as IH
  iintro %X %l %_ HI HK
  ihave Hw := Hb $$ %X %l HI
  iunfold mwpi at Hw
  simp only [Frame.withLocals_inst, Frame.withLocals_mi]
  ispecialize Hw $$ %Ψ %(C.enter vs₀ (blockLabel C vs₀ (Exec.blockType f.mi bt).params.length
    (some body))) %(by simpa using hC) Hi
  simp only [Ctx.enter_labels, Ctx.enter_rest]
  iapply Hw
  unfold mKont
  simp only [Post.mloop, Frame.withLocals_withLocals]
  isplit
  · iintro %vs' %l' HΦ
    simp only [Ctx.enter_labels, Ctx.enter_rest]
    iunfold pay at HΦ
    icases HΦ with ⟨%R', Hc, HΦ⟩
    iapply mwpT_step [] (by simp) 0 Cg R'
      (fun s => by simp [nextInstructionGas, Config.nextInstr?, Ctx.thread, Ctx.threadA])
      (by simp [Ctx.thread, Ctx.threadA, Ctx.enter])
      (fun σ _ => next_pop_label σ lim C (f.withLocals l') vs₀ vs' _ C.labels)
    isplitl [Hc]
    · iexact Hc
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    inext
    iintro Hc
    icases HK with ⟨HK, -⟩
    simp only [blockLabel_rest]
    iapply HK $$ %(vs₀ ++ vs') %l'
    iapply HΦ $$ Hc
  isplit
  · iintro %n %X' %l' HΦ
    simp only [Ctx.enter_labels]
    rcases n with _ | n
    · iunfold pay at HΦ
      icases HΦ with ⟨%hr, %R', Hc, HΦ⟩
      have hr' : (Exec.blockType (f.withLocals l').mi bt).params.length ≤ X'.length := by
        simpa using hr
      have hn := fun (σ : Store NearState) (hRd : ∀ p ∈ [(Loc.inst f.inst, Cell.inst (H := NearState) f.mi)],
          lookup σ p.1 = some p.2) =>
        (next_br_zero_loop σ lim C (f.withLocals l') vs₀ X' bt body
          (by simpa using hmi_of_see (Rd := []) hRd) hr').trans
        (next_loop σ lim C (f.withLocals l') vs₀ _ bt body (by simpa using hmi_of_see (Rd := []) hRd)
          (by simp; omega))
      simp only [Frame.withLocals_mi] at hn
      iapply mwpT_step [(Loc.inst f.inst, .inst f.mi)] (inst_plain f) (2 * cfg.regularOpCost) Cg R'
        (fun s => by
          simp [nextInstructionGas, Config.nextInstr?, Config.labelIsLoop, loopBackedge,
            linearInstruction, Ctx.thread, Ctx.threadA, Ctx.enter, blockLabel]; omega)
        (by simp [Ctx.thread, Ctx.threadA, Ctx.enter])
        hn
      isplitl [Hc]
      · iexact Hc
      isplitr
      · iapply seeInst $$ Hi
      inext
      iintro Hc
      iapply IH $$ %(X'.drop (X'.length - (Exec.blockType f.mi bt).params.length)) %l'
        %(by simp; omega) [HΦ Hc] HK
      iapply HΦ $$ Hc
    · iapply mwp_running_congr
        (fun s => by simp [nextInstructionGas, Config.nextInstr?, Config.labelIsLoop, loopBackedge,
          linearInstruction, Ctx.thread, Ctx.threadA, Ctx.enter]; split_ifs <;> simp_all)
        (by simp [Ctx.thread, Ctx.threadA, Ctx.enter])
        (fun σ => next_br_succ σ lim C (f.withLocals l') vs₀ X' _ C.labels n)
      icases HK with ⟨-, ⟨HK, -⟩⟩
      iapply HK $$ %n %(vs₀ ++ X') %l' HΦ
  isplit
  · iintro %X' %l' HΦ
    simp only [Ctx.enter_labels]
    iapply mwp_running_congr
      (fun s => by simp [nextInstructionGas, Config.nextInstr?, loopBackedge, linearInstruction,
        Ctx.thread, Ctx.threadA])
      (by simp [Ctx.thread, Ctx.threadA, Ctx.enter])
      (fun σ => next_return_label σ lim C (f.withLocals l') vs₀ X' _ C.labels)
    icases HK with ⟨-, -, ⟨HK, -⟩⟩
    iapply HK $$ %(vs₀ ++ X') %l' HΦ
  · icases HK with ⟨-, -, -, HK⟩
    iexact HK

/-- Iris-Wasm's `wp_loop`, with an invariant: `loop` costs one
`regular_op_cost` and enters the body from `I`; the body, proved once from
`I`, may branch back to the loop's label for two `regular_op_cost`s by
re-establishing `I` (`Post.mloop`). -/
theorem mwpi_loop (bt : BlockType) (body : List Instr) (vs₀ args : List Value)
    (I : List Value → Frame → IProp GF)
    (hp : args.length = (Exec.blockType f.mi bt).params.length) :
    □ (∀ X l, I X (f.withLocals l) -∗ mwpi cfg lim d (f.withLocals l) X body
          (Post.mloop cfg Cg (Exec.blockType f.mi bt).params.length vs₀ I Φ)) ∗
      credits Cg (cfg.regularOpCost + R) ∗ ▷ (credits Cg R -∗ I args f)
      ⊢ mwpi cfg lim d f (vs₀ ++ args) [.loop bt body] Φ := by
  iintro ⟨#Hb, Hc, HI⟩
  iunfold mwpi
  iintro %Ψ %C %hC #Hi HK
  rw [List.singleton_append]
  have hn := fun σ (hRd : ∀ p ∈ [(Loc.inst f.inst, Cell.inst (H := NearState) f.mi)],
      lookup σ p.1 = some p.2) => next_loop σ lim C f vs₀ args bt body (hmi_of_see hRd) hp
  iapply mwpT_step [(Loc.inst f.inst, .inst f.mi)] (inst_plain f) cfg.regularOpCost Cg R
    (fun s => by simp [nextInstructionGas, Config.nextInstr?, loopBackedge, linearInstruction,
      Ctx.thread, Ctx.threadA])
    (by simp [Ctx.thread, Ctx.threadA, Ctx.enter])
    hn
  isplitl [Hc]
  · iexact Hc
  isplitr
  · iapply seeInst $$ Hi
  inext
  iintro Hc
  have := loop_run (cfg := cfg) (lim := lim) (f := f) (Φ := Φ) (Cg := Cg) C hC bt body vs₀ I Ψ
  ihave Hr := this $$ Hb Hi
  ispecialize Hr $$ %args %f.locals %hp
  simp only [Frame.withLocals_self]
  iapply Hr $$ [HI Hc] HK
  iapply HI $$ Hc


/-! ## Blocks without parameters -/

theorem mwpi_block0 (bt : BlockType) (body : List Instr) (vs₀ : List Value)
    (hp : (Exec.blockType f.mi bt).params = []) :
    credits Cg R ∗ ▷ (credits Cg R -∗
        mwpi cfg lim d f [] body (Post.mblock cfg Cg (Exec.blockType f.mi bt).results.length vs₀ Φ))
      ⊢ mwpi cfg lim d f vs₀ [.block bt body] Φ := by
  have := mwpi_block (Φ := Φ) (cfg := cfg) (lim := lim) (d := d) (f := f) (Cg := Cg) (R := R)
    bt body vs₀ [] (by simp [hp])
  simpa using this

theorem mwpi_if0_true (bt : BlockType) (th el : List Instr) (vs₀ : List Value) (c : UInt32)
    (hc : c ≠ 0) (hp : (Exec.blockType f.mi bt).params = []) :
    credits Cg (cfg.regularOpCost + R) ∗ ▷ (credits Cg R -∗
        mwpi cfg lim d f [] th (Post.mblock cfg Cg (Exec.blockType f.mi bt).results.length vs₀ Φ))
      ⊢ mwpi cfg lim d f (vs₀ ++ [.i32 c]) [.«if» bt th el] Φ := by
  have := mwpi_if_true (Φ := Φ) (cfg := cfg) (lim := lim) (d := d) (f := f) (Cg := Cg) (R := R)
    bt th el vs₀ [] c hc (by simp [hp])
  simpa using this

theorem mwpi_if0_false (bt : BlockType) (th el : List Instr) (vs₀ : List Value)
    (hp : (Exec.blockType f.mi bt).params = []) :
    credits Cg (cfg.regularOpCost + R) ∗ ▷ (credits Cg R -∗
        mwpi cfg lim d f [] el (Post.mblock cfg Cg (Exec.blockType f.mi bt).results.length vs₀ Φ))
      ⊢ mwpi cfg lim d f (vs₀ ++ [.i32 0]) [.«if» bt th el] Φ := by
  have := mwpi_if_false (Φ := Φ) (cfg := cfg) (lim := lim) (d := d) (f := f) (Cg := Cg) (R := R)
    bt th el vs₀ [] (by simp [hp])
  simpa using this

theorem mwpi_loop0 (bt : BlockType) (body : List Instr) (vs₀ : List Value)
    (I : List Value → Frame → IProp GF) (hp : (Exec.blockType f.mi bt).params = []) :
    □ (∀ X l, I X (f.withLocals l) -∗ mwpi cfg lim d (f.withLocals l) X body
          (Post.mloop cfg Cg 0 vs₀ I Φ)) ∗
      credits Cg (cfg.regularOpCost + R) ∗ ▷ (credits Cg R -∗ I [] f)
      ⊢ mwpi cfg lim d f vs₀ [.loop bt body] Φ := by
  have := mwpi_loop (Φ := Φ) (cfg := cfg) (lim := lim) (d := d) (f := f) (Cg := Cg) (R := R)
    bt body vs₀ [] I (by simp [hp])
  simpa [hp] using this

@[simp] theorem Post.mblock_normal (r : Nat) (vs₀ : List Value) (Φ : Post NearState GF)
    (vs : List Value) (g : Frame) :
    (Post.mblock cfg Cg r vs₀ Φ).normal vs g = pay Cg 0 (Φ.normal (vs₀ ++ vs) g) := rfl
@[simp] theorem Post.mblock_br_zero (r : Nat) (vs₀ : List Value) (Φ : Post NearState GF)
    (X : List Value) (g : Frame) :
    (Post.mblock cfg Cg r vs₀ Φ).br 0 X g =
      iprop(⌜r ≤ X.length⌝ ∗ pay Cg cfg.regularOpCost (Φ.normal (vs₀ ++ X.drop (X.length - r)) g)) :=
  rfl
@[simp] theorem Post.mblock_br_succ (r : Nat) (vs₀ : List Value) (Φ : Post NearState GF) (n : Nat)
    (X : List Value) (g : Frame) : (Post.mblock cfg Cg r vs₀ Φ).br (n + 1) X g = Φ.br n (vs₀ ++ X) g :=
  rfl
@[simp] theorem Post.mblock_ret (r : Nat) (vs₀ : List Value) (Φ : Post NearState GF) (X : List Value)
    (g : Frame) : (Post.mblock cfg Cg r vs₀ Φ).ret X g = Φ.ret (vs₀ ++ X) g := rfl
@[simp] theorem Post.mblock_trap (r : Nat) (vs₀ : List Value) (Φ : Post NearState GF) :
    (Post.mblock cfg Cg r vs₀ Φ).trap = Φ.trap := rfl

end Rules

end NearLogic
