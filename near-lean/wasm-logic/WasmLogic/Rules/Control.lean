import WasmLogic.Rules.Memory

/-!
# Rules for structured control

`br`, `br_if`, `br_table` and `return` hand control to the context's branch
and return continuations. `block`, `if` and `loop` enter their body under a
new label; how the body ends is translated back to how the instruction ends
(`Post.block`, `Post.loop`): branching to the new label falls through the
block or re-enters the loop, branching further out branches one label less
far, returning returns.

As in Iris-Wasm, a loop that runs again is the same `loop` instruction run
again (`Post.loop`), so properties of loops are proved by Löb induction or
by induction on a measure, with the `▷` the rule provides on entry.
-/

namespace WasmLogic

open Wasm Iris Iris.BI Iris.ProgramLogic

section Thread

variable {H : Type} {GF : BundledGFunctors} [WasmGS H GF]

/-- A step that only moves the thread, from every store with the cells `Rd`. -/
theorem wpT_step {lim : ExecLimits} {t t' : Thread} {Ψ : Outcome → IProp GF}
    (Rd : List (Loc × Cell H))
    (h : ∀ σ : Store H, (∀ p ∈ Rd, lookup σ p.1 = some p.2) → next σ lim t = (.running lim t', σ)) :
    seeList Rd ∗ ▷ wpT (H := H) lim t' Ψ ⊢ wpT (H := H) lim t Ψ := by
  iintro ⟨HRd, Hwp⟩
  iapply wp_lift lim t Rd [] [] (.running lim t') List.nodup_nil List.nodup_nil
  · intro σ hRd _
    rw [h σ hRd]
    exact ⟨rfl, fun l => by simp⟩
  · intro σ _ _ l hl _
    simp at hl
  isplitl [HRd]
  · iexact HRd
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  · inext
    iintro _
    iexact Hwp

end Thread

section Next

variable {H : Type}

theorem next_br_rest (σ : Store H) (lim : ExecLimits) (C : Ctx) (f : Frame) (vs : List Value)
    (L : List Label) (n : Nat) (R : List Instr) :
    next σ lim (C.thread f vs L (.br n :: R)) = next σ lim (C.thread f vs L [.br n]) := by
  simp only [next, Code.config, Exec.step, Exec.instr, Ctx.thread, Ctx.threadA, Exec.branch]
  rcases hL : L[n]? with _ | label
  · simp [Exec.leave]
  · rcases hb : label.loop with _ | body <;> simp [hb]

theorem next_return_rest (σ : Store H) (lim : ExecLimits) (C : Ctx) (f : Frame) (vs : List Value)
    (L : List Label) (R : List Instr) :
    next σ lim (C.thread f vs L (.return :: R)) = next σ lim (C.thread f vs L [.return]) := by
  simp [next, Code.config, Exec.step, Exec.instr, Ctx.thread, Ctx.threadA, Exec.leave]

theorem branch_stack (A X : List Value) (r : Nat) (hr : r ≤ X.length) :
    ((Exec.popN (A ++ X).toArray r).1.shrink A.length ++ (Exec.popN (A ++ X).toArray r).2.toArray) =
      (A ++ X.drop (X.length - r)).toArray := by
  apply Array.toList_inj.mp
  simp [Exec.popN, List.take_append, List.drop_append]
  have e1 : A.length + X.length - r - A.length = X.length - r := by omega
  have e2 : A.length - min (A.length + X.length - r) A.length = 0 := by omega
  have e3 : A.length + X.length - (A.length + X.length - r) = r := by omega
  rw [e1, e2, e3, List.take_of_length_le (l := List.take _ A) (by simp; omega),
    List.take_of_length_le (l := A) (by omega),
    List.drop_of_length_le (l := A) (by omega)]
  simp
  rw [show r - (A.length - (A.length + X.length - r)) = r by omega,
    List.take_of_length_le (by simp; omega)]

/-- The context of a block body: the block's operands below it, its label
around it, nothing after it in the same code list. -/
def Ctx.enter (C : Ctx) (vs₀ : List Value) (ℓ : Label) : Ctx :=
  { C with base := C.base ++ vs₀, labels := ℓ :: C.labels, rest := [] }

@[simp] theorem Ctx.enter_labels (C : Ctx) (vs₀ : List Value) (ℓ : Label) :
    (C.enter vs₀ ℓ).labels = ℓ :: C.labels := rfl
@[simp] theorem Ctx.enter_rest (C : Ctx) (vs₀ : List Value) (ℓ : Label) :
    (C.enter vs₀ ℓ).rest = [] := rfl
@[simp] theorem Ctx.enter_below (C : Ctx) (vs₀ : List Value) (ℓ : Label) :
    (C.enter vs₀ ℓ).below = C.below := rfl

theorem Ctx.enter_thread (C : Ctx) (vs₀ X : List Value) (ℓ : Label) (g : Frame) (L : List Label)
    (code : List Instr) :
    (C.enter vs₀ ℓ).thread g X L code = C.thread g (vs₀ ++ X) L code := by
  simp [Ctx.enter, Ctx.thread, Ctx.threadA]

/-- The label a block, `if` or loop pushes. -/
def blockLabel (C : Ctx) (vs₀ : List Value) (arity : Nat) (loop : Option (List Instr)) : Label :=
  { arity := arity, height := (C.base ++ vs₀).length, rest := C.rest, loop := loop }

@[simp] theorem blockLabel_rest (C : Ctx) (vs₀ : List Value) (a : Nat) (lp : Option (List Instr)) :
    (blockLabel C vs₀ a lp).rest = C.rest := rfl
@[simp] theorem blockLabel_arity (C : Ctx) (vs₀ : List Value) (a : Nat) (lp : Option (List Instr)) :
    (blockLabel C vs₀ a lp).arity = a := rfl
@[simp] theorem blockLabel_loop (C : Ctx) (vs₀ : List Value) (a : Nat) (lp : Option (List Instr)) :
    (blockLabel C vs₀ a lp).loop = lp := rfl
@[simp] theorem blockLabel_height (C : Ctx) (vs₀ : List Value) (a : Nat) (lp : Option (List Instr)) :
    (blockLabel C vs₀ a lp).height = (C.base ++ vs₀).length := rfl

theorem next_block (σ : Store H) (lim : ExecLimits) (C : Ctx) (f : Frame) (vs₀ args : List Value)
    (bt : BlockType) (body : List Instr) (hmi : σ.modules[f.inst]? = some f.mi)
    (hp : args.length = (Exec.blockType f.mi bt).params.length) :
    next σ lim (C.thread f (vs₀ ++ args) C.labels (.block bt body :: C.rest)) =
      (.running lim ((C.enter vs₀ (blockLabel C vs₀ (Exec.blockType f.mi bt).results.length none)).thread
        f args (blockLabel C vs₀ (Exec.blockType f.mi bt).results.length none :: C.labels)
        (body ++ [])), σ) := by
  have hh : (C.base ++ (vs₀ ++ args)).length - (Exec.blockType f.mi bt).params.length =
      (C.base ++ vs₀).length := by simp; omega
  simp [next, Code.config, Exec.step, Exec.instr, Ctx.thread, Ctx.threadA, Ctx.enter,
    modules_get! hmi, blockLabel, ← hh]

theorem next_loop (σ : Store H) (lim : ExecLimits) (C : Ctx) (f : Frame) (vs₀ args : List Value)
    (bt : BlockType) (body : List Instr) (hmi : σ.modules[f.inst]? = some f.mi)
    (hp : args.length = (Exec.blockType f.mi bt).params.length) :
    next σ lim (C.thread f (vs₀ ++ args) C.labels (.loop bt body :: C.rest)) =
      (.running lim ((C.enter vs₀ (blockLabel C vs₀ (Exec.blockType f.mi bt).params.length
        (some body))).thread f args
        (blockLabel C vs₀ (Exec.blockType f.mi bt).params.length (some body) :: C.labels)
        (body ++ [])), σ) := by
  have hh : (C.base ++ (vs₀ ++ args)).length - (Exec.blockType f.mi bt).params.length =
      (C.base ++ vs₀).length := by simp; omega
  simp [next, Code.config, Exec.step, Exec.instr, Ctx.thread, Ctx.threadA, Ctx.enter,
    modules_get! hmi, blockLabel, ← hh]

theorem next_if (σ : Store H) (lim : ExecLimits) (C : Ctx) (f : Frame) (vs₀ args : List Value)
    (c : UInt32) (bt : BlockType) (th el : List Instr) (hmi : σ.modules[f.inst]? = some f.mi)
    (hp : args.length = (Exec.blockType f.mi bt).params.length) :
    next σ lim (C.thread f (vs₀ ++ args ++ [.i32 c]) C.labels (.«if» bt th el :: C.rest)) =
      (.running lim ((C.enter vs₀ (blockLabel C vs₀ (Exec.blockType f.mi bt).results.length none)).thread
        f args (blockLabel C vs₀ (Exec.blockType f.mi bt).results.length none :: C.labels)
        ((if c != 0 then th else el) ++ [])), σ) := by
  have hh : (C.base ++ (vs₀ ++ args)).length - (Exec.blockType f.mi bt).params.length =
      (C.base ++ vs₀).length := by simp; omega
  simp [next, Code.config, Exec.step, Exec.instr, Exec.i32, Ctx.thread, Ctx.threadA, Ctx.enter,
    modules_get! hmi, blockLabel, ← hh]

/-- Falling off the end of a body pops its label. -/
theorem next_pop_label (σ : Store H) (lim : ExecLimits) (C : Ctx) (g : Frame) (vs₀ X : List Value)
    (ℓ : Label) (L : List Label) :
    next σ lim ((C.enter vs₀ ℓ).thread g X (ℓ :: L) []) =
      (.running lim (C.thread g (vs₀ ++ X) L ℓ.rest), σ) := by
  simp [next, Code.config, Exec.step, Ctx.thread, Ctx.threadA, Ctx.enter]

/-- Branching to a block's own label falls through the block. -/
theorem next_br_zero (σ : Store H) (lim : ExecLimits) (C : Ctx) (g : Frame) (vs₀ X : List Value)
    (ℓ : Label) (L : List Label) (hloop : ℓ.loop = none) (hh : ℓ.height = (C.base ++ vs₀).length)
    (hr : ℓ.arity ≤ X.length) :
    next σ lim ((C.enter vs₀ ℓ).thread g X (ℓ :: L) [.br 0]) =
      (.running lim (C.thread g (vs₀ ++ X.drop (X.length - ℓ.arity)) L ℓ.rest), σ) := by
  have hs := branch_stack (C.base ++ vs₀) X ℓ.arity hr
  simp only [List.append_assoc] at hs
  have hs' := congrArg Array.toList hs
  simp at hs'
  simp [next, Code.config, Exec.step, Exec.instr, Exec.branch, Ctx.thread, Ctx.threadA, Ctx.enter,
    hloop, hh, hs']

/-- Branching past a block's label branches one label less far outside it. -/
theorem next_br_succ (σ : Store H) (lim : ExecLimits) (C : Ctx) (g : Frame) (vs₀ X : List Value)
    (ℓ : Label) (L : List Label) (n : Nat) :
    next σ lim ((C.enter vs₀ ℓ).thread g X (ℓ :: L) [.br (n + 1)]) =
      next σ lim (C.thread g (vs₀ ++ X) L [.br n]) := by
  simp only [next, Code.config, Exec.step, Exec.instr, Exec.branch, Ctx.thread, Ctx.threadA,
    Ctx.enter, List.getElem?_cons_succ, List.drop_succ_cons, List.append_assoc]
  rcases hL : L[n]? with _ | label
  · simp [Exec.leave]
  · rcases hb : label.loop with _ | body <;> simp [hb]

/-- Returning from inside a block returns. -/
theorem next_return_label (σ : Store H) (lim : ExecLimits) (C : Ctx) (g : Frame)
    (vs₀ X : List Value) (ℓ : Label) (L : List Label) :
    next σ lim ((C.enter vs₀ ℓ).thread g X (ℓ :: L) [.return]) =
      next σ lim (C.thread g (vs₀ ++ X) L [.return]) := by
  simp [next, Code.config, Exec.step, Exec.instr, Ctx.thread, Ctx.threadA, Ctx.enter, Exec.leave]

/-- Branching to a loop's label is entering the loop again. -/
theorem next_br_zero_loop (σ : Store H) (lim : ExecLimits) (C : Ctx) (g : Frame) (vs₀ X : List Value)
    (bt : BlockType) (body : List Instr) (hmi : σ.modules[g.inst]? = some g.mi)
    (hr : (Exec.blockType g.mi bt).params.length ≤ X.length) :
    next σ lim ((C.enter vs₀ (blockLabel C vs₀ (Exec.blockType g.mi bt).params.length
        (some body))).thread g X
        (blockLabel C vs₀ (Exec.blockType g.mi bt).params.length (some body) :: C.labels) [.br 0]) =
      next σ lim (C.thread g (vs₀ ++ X.drop (X.length - (Exec.blockType g.mi bt).params.length))
        C.labels (.loop bt body :: C.rest)) := by
  rw [next_loop σ lim C g vs₀ _ bt body hmi (by simp; omega)]
  have hs := branch_stack (C.base ++ vs₀) X (Exec.blockType g.mi bt).params.length hr
  simp only [List.append_assoc] at hs
  have hs' := congrArg Array.toList hs
  simp at hs'
  simp [next, Code.config, Exec.step, Exec.instr, Exec.branch, Ctx.thread, Ctx.threadA, Ctx.enter,
    blockLabel, hs']

theorem next_br_if (σ : Store H) (lim : ExecLimits) (C : Ctx) (f : Frame) (vs : List Value)
    (L : List Label) (n : Nat) (c : UInt32) (hc : c ≠ 0) (R : List Instr) :
    next σ lim (C.thread f (vs ++ [.i32 c]) L (.br_if n :: R)) =
      next σ lim (C.thread f vs L [.br n]) := by
  simp only [next, Code.config, Exec.step, Exec.instr, Exec.i32, Exec.branch, Ctx.thread,
    Ctx.threadA]
  simp only [List.pop_toArray, List.back?_toArray, ← List.append_assoc, List.dropLast_concat,
    List.getLast?_concat, Option.getD_some, bne_iff_ne, ne_eq, hc, not_false_eq_true, ite_true]
  rcases hL : L[n]? with _ | label
  · simp [Exec.leave]
  · rcases hb : label.loop with _ | body <;> simp [hb]

theorem next_br_table (σ : Store H) (lim : ExecLimits) (C : Ctx) (f : Frame) (vs : List Value)
    (L : List Label) (ls : List Nat) (dflt : Nat) (c : UInt32) (R : List Instr) :
    next σ lim (C.thread f (vs ++ [.i32 c]) L (.br_table ls dflt :: R)) =
      next σ lim (C.thread f vs L [.br (ls[c.toNat]?.getD dflt)]) := by
  simp only [next, Code.config, Exec.step, Exec.instr, Exec.i32, Exec.branch, Ctx.thread,
    Ctx.threadA]
  simp only [List.pop_toArray, List.back?_toArray, ← List.append_assoc, List.dropLast_concat,
    List.getLast?_concat, Option.getD_some]
  rcases hL : L[ls[c.toNat]?.getD dflt]? with _ | label
  · simp [Exec.leave]
  · rcases hb : label.loop with _ | body <;> simp [hb]

end Next

section Rules

variable {H : Type} {GF : BundledGFunctors} [WasmGS H GF]
variable {lim : ExecLimits} {d : Nat} {f : Frame} {vs : List Value} {Φ : Post H GF}

/-- Iris-Wasm's `wp_br`: a branch is the context's branch continuation. -/
theorem wpi_br (n : Nat) : Φ.br n vs f ⊢ wpi lim d f vs [.br n] Φ := by
  unfold wpi Kont
  iintro HΦ %Ψ %C %_ #_ HK
  icases HK with ⟨-, ⟨HK, -⟩⟩
  ispecialize HK $$ %n %vs %f.locals
  simp only [Frame.withLocals_self]
  ispecialize HK $$ HΦ
  rw [List.singleton_append]
  iapply wp_running_congr (fun σ => next_br_rest σ lim C f vs C.labels n C.rest)
  iexact HK

/-- Iris-Wasm's `wp_return`. -/
theorem wpi_return : Φ.ret vs f ⊢ wpi lim d f vs [.return] Φ := by
  unfold wpi Kont
  iintro HΦ %Ψ %C %_ #_ HK
  icases HK with ⟨-, -, ⟨HK, -⟩⟩
  ispecialize HK $$ %vs %f.locals
  simp only [Frame.withLocals_self]
  ispecialize HK $$ HΦ
  rw [List.singleton_append]
  iapply wp_running_congr (fun σ => next_return_rest σ lim C f vs C.labels C.rest)
  iexact HK

theorem wpi_br_if_true (n : Nat) (c : UInt32) (hc : c ≠ 0) :
    Φ.br n vs f ⊢ wpi lim d f (vs ++ [.i32 c]) [.br_if n] Φ := by
  unfold wpi Kont
  iintro HΦ %Ψ %C %_ #_ HK
  icases HK with ⟨-, ⟨HK, -⟩⟩
  ispecialize HK $$ %n %vs %f.locals
  simp only [Frame.withLocals_self]
  ispecialize HK $$ HΦ
  rw [List.singleton_append]
  iapply wp_running_congr (fun σ => next_br_if σ lim C f vs C.labels n c hc C.rest)
  iexact HK

theorem wpi_br_if_false (n : Nat) : ▷ Φ.normal vs f ⊢ wpi lim d f (vs ++ [.i32 0]) [.br_if n] Φ := by
  have := wpi_pure (Φ := Φ) (lim := lim) (d := d) (f := f) (vs := vs ++ [.i32 0]) (.br_if n) vs
    f.locals (fun σ base L R => by simp [Exec.instr, Exec.i32])
  simpa using this

theorem wpi_br_table (ls : List Nat) (dflt : Nat) (c : UInt32) :
    Φ.br (ls[c.toNat]?.getD dflt) vs f ⊢ wpi lim d f (vs ++ [.i32 c]) [.br_table ls dflt] Φ := by
  unfold wpi Kont
  iintro HΦ %Ψ %C %_ #_ HK
  icases HK with ⟨-, ⟨HK, -⟩⟩
  ispecialize HK $$ %(ls[c.toNat]?.getD dflt) %vs %f.locals
  simp only [Frame.withLocals_self]
  ispecialize HK $$ HΦ
  rw [List.singleton_append]
  iapply wp_running_congr (fun σ => next_br_table σ lim C f vs C.labels ls dflt c C.rest)
  iexact HK

/-- How a block's body ending translates to the block ending. -/
def Post.block (r : Nat) (vs₀ : List Value) (Φ : Post H GF) : Post H GF where
  normal vs g := Φ.normal (vs₀ ++ vs) g
  br n X g := match n with
    | 0 => iprop(⌜r ≤ X.length⌝ ∗ Φ.normal (vs₀ ++ X.drop (X.length - r)) g)
    | n + 1 => Φ.br n (vs₀ ++ X) g
  ret X g := Φ.ret (vs₀ ++ X) g
  trap := Φ.trap

/-- How a loop's body ending translates to the loop ending: branching to the
loop's label runs the loop again. -/
def Post.loop (lim : ExecLimits) (d : Nat) (bt : BlockType) (body : List Instr) (p : Nat)
    (vs₀ : List Value) (Φ : Post H GF) : Post H GF where
  normal vs g := Φ.normal (vs₀ ++ vs) g
  br n X g := match n with
    | 0 => iprop(⌜p ≤ X.length⌝ ∗ wpi lim d g (vs₀ ++ X.drop (X.length - p)) [.loop bt body] Φ)
    | n + 1 => Φ.br n (vs₀ ++ X) g
  ret X g := Φ.ret (vs₀ ++ X) g
  trap := Φ.trap

theorem hmi_of_see {σ : Store H} {f : Frame} {Rd : List (Loc × Cell H)}
    (h : ∀ p ∈ (Loc.inst f.inst, Cell.inst f.mi) :: Rd, lookup σ p.1 = some p.2) :
    σ.modules[f.inst]? = some f.mi := by
  have := h _ List.mem_cons_self
  simp only [lookup_inst, Option.map_eq_some_iff] at this
  obtain ⟨m, hm, he⟩ := this
  cases he; exact hm

theorem seeInst : instPt (H := H) (GF := GF) f.inst f.mi ⊢ seeList [(Loc.inst f.inst, .inst f.mi)] := by
  iintro #Hi
  iapply (seeList_cons _ _).2
  iunfold instPt at Hi
  isplitr
  · iexact Hi
  · iapply BigSepL.bigSepL_nil.2; iempintro

/-- The common part of `block` and `if`: the body runs under the block's label. -/
theorem block_body (C : Ctx) (vs₀ : List Value) (r : Nat) (Ψ : Outcome → IProp GF) :
    Kont lim C f Φ Ψ ⊢ Kont lim (C.enter vs₀ (blockLabel C vs₀ r none)) f (Post.block r vs₀ Φ) Ψ := by
  unfold Kont
  simp only [Post.block]
  iintro HK
  isplit
  · iintro %vs' %l HΦ
    simp only [Ctx.enter_labels, Ctx.enter_rest]
    iapply wpT_step [] (fun σ _ => next_pop_label σ lim C (f.withLocals l) vs₀ vs' _ C.labels)
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    inext
    icases HK with ⟨HK, -⟩
    simp only [blockLabel_rest]
    iapply HK $$ %(vs₀ ++ vs') %l HΦ
  isplit
  · iintro %n %X %l HΦ
    simp only [Ctx.enter_labels]
    rcases n with _ | n
    · icases HΦ with ⟨%hr, HΦ⟩
      iapply wpT_step [] (fun σ _ => next_br_zero σ lim C (f.withLocals l) vs₀ X _ C.labels rfl rfl
        (by simpa using hr))
      isplitr
      · iapply BigSepL.bigSepL_nil.2; iempintro
      inext
      icases HK with ⟨HK, -⟩
      simp only [blockLabel_rest, blockLabel_arity]
      iapply HK $$ %(vs₀ ++ X.drop (X.length - r)) %l HΦ
    · iapply wp_running_congr (fun σ => next_br_succ σ lim C (f.withLocals l) vs₀ X _ C.labels n)
      icases HK with ⟨-, ⟨HK, -⟩⟩
      iapply HK $$ %n %(vs₀ ++ X) %l HΦ
  isplit
  · iintro %X %l HΦ
    simp only [Ctx.enter_labels]
    iapply wp_running_congr (fun σ => next_return_label σ lim C (f.withLocals l) vs₀ X _ C.labels)
    icases HK with ⟨-, -, ⟨HK, -⟩⟩
    iapply HK $$ %(vs₀ ++ X) %l HΦ
  · icases HK with ⟨-, -, -, HK⟩
    iexact HK

/-- Iris-Wasm's `wp_block`. -/
theorem wpi_block (bt : BlockType) (body : List Instr) (vs₀ args : List Value)
    (hp : args.length = (Exec.blockType f.mi bt).params.length) :
    ▷ wpi lim d f args body (Post.block (Exec.blockType f.mi bt).results.length vs₀ Φ)
      ⊢ wpi lim d f (vs₀ ++ args) [.block bt body] Φ := by
  iintro Hwp
  unfold wpi
  iintro %Ψ %C %hC #Hi HK
  rw [List.singleton_append]
  iapply wpT_step [(Loc.inst f.inst, .inst f.mi)]
    (fun σ hRd => next_block σ lim C f vs₀ args bt body (hmi_of_see hRd) hp)
  isplitr
  · iapply seeInst $$ Hi
  inext
  ispecialize Hwp $$ %Ψ %(C.enter vs₀ (blockLabel C vs₀ (Exec.blockType f.mi bt).results.length none))
    %(by simpa using hC) Hi
  simp only [Ctx.enter_labels, Ctx.enter_rest]
  iapply Hwp
  iapply block_body $$ HK

/-- Iris-Wasm's `wp_if_true`. -/
theorem wpi_if_true (bt : BlockType) (th el : List Instr) (vs₀ args : List Value) (c : UInt32)
    (hc : c ≠ 0) (hp : args.length = (Exec.blockType f.mi bt).params.length) :
    ▷ wpi lim d f args th (Post.block (Exec.blockType f.mi bt).results.length vs₀ Φ)
      ⊢ wpi lim d f (vs₀ ++ args ++ [.i32 c]) [.«if» bt th el] Φ := by
  iintro Hwp
  unfold wpi
  iintro %Ψ %C %hC #Hi HK
  rw [List.singleton_append]
  iapply wpT_step [(Loc.inst f.inst, .inst f.mi)]
    (fun σ hRd => next_if σ lim C f vs₀ args c bt th el (hmi_of_see hRd) hp)
  isplitr
  · iapply seeInst $$ Hi
  inext
  simp only [bne_iff_ne, ne_eq, hc, not_false_eq_true, ite_true]
  ispecialize Hwp $$ %Ψ %(C.enter vs₀ (blockLabel C vs₀ (Exec.blockType f.mi bt).results.length none))
    %(by simpa using hC) Hi
  simp only [Ctx.enter_labels, Ctx.enter_rest]
  iapply Hwp
  iapply block_body $$ HK

/-- Iris-Wasm's `wp_if_false`. -/
theorem wpi_if_false (bt : BlockType) (th el : List Instr) (vs₀ args : List Value)
    (hp : args.length = (Exec.blockType f.mi bt).params.length) :
    ▷ wpi lim d f args el (Post.block (Exec.blockType f.mi bt).results.length vs₀ Φ)
      ⊢ wpi lim d f (vs₀ ++ args ++ [.i32 0]) [.«if» bt th el] Φ := by
  iintro Hwp
  unfold wpi
  iintro %Ψ %C %hC #Hi HK
  rw [List.singleton_append]
  iapply wpT_step [(Loc.inst f.inst, .inst f.mi)]
    (fun σ hRd => next_if σ lim C f vs₀ args 0 bt th el (hmi_of_see hRd) hp)
  isplitr
  · iapply seeInst $$ Hi
  inext
  simp only [bne_self_eq_false, Bool.false_eq_true, ite_false]
  ispecialize Hwp $$ %Ψ %(C.enter vs₀ (blockLabel C vs₀ (Exec.blockType f.mi bt).results.length none))
    %(by simpa using hC) Hi
  simp only [Ctx.enter_labels, Ctx.enter_rest]
  iapply Hwp
  iapply block_body $$ HK

/-- Iris-Wasm's `wp_loop`: the body runs under the loop's label, and
branching to it runs the loop instruction again. -/
theorem wpi_loop (bt : BlockType) (body : List Instr) (vs₀ args : List Value)
    (hp : args.length = (Exec.blockType f.mi bt).params.length) :
    ▷ wpi lim d f args body
        (Post.loop lim d bt body (Exec.blockType f.mi bt).params.length vs₀ Φ)
      ⊢ wpi lim d f (vs₀ ++ args) [.loop bt body] Φ := by
  iintro Hwp
  unfold wpi
  iintro %Ψ %C %hC #Hi HK
  rw [List.singleton_append]
  iapply wpT_step [(Loc.inst f.inst, .inst f.mi)]
    (fun σ hRd => next_loop σ lim C f vs₀ args bt body (hmi_of_see hRd) hp)
  isplitr
  · iapply seeInst $$ Hi
  inext
  ispecialize Hwp $$ %Ψ %(C.enter vs₀ (blockLabel C vs₀ (Exec.blockType f.mi bt).params.length
    (some body))) %(by simpa using hC) Hi
  simp only [Ctx.enter_labels, Ctx.enter_rest]
  iapply Hwp
  unfold Kont
  simp only [Post.loop]
  isplit
  · iintro %vs' %l HΦ
    simp only [Ctx.enter_labels, Ctx.enter_rest]
    iapply wpT_step [] (fun σ _ => next_pop_label σ lim C (f.withLocals l) vs₀ vs' _ C.labels)
    isplitr
    · iapply BigSepL.bigSepL_nil.2; iempintro
    inext
    icases HK with ⟨HK, -⟩
    simp only [blockLabel_rest]
    iapply HK $$ %(vs₀ ++ vs') %l HΦ
  isplit
  · iintro %n %X %l HΦ
    simp only [Ctx.enter_labels]
    rcases n with _ | n
    · icases HΦ with ⟨%hr, HΦ⟩
      have hr' : (Exec.blockType (f.withLocals l).mi bt).params.length ≤ X.length := by simpa using hr
      have hn := fun (σ : Store H) (hRd : ∀ p ∈ [(Loc.inst f.inst, Cell.inst f.mi)],
          lookup σ p.1 = some p.2) => next_br_zero_loop σ lim C (f.withLocals l) vs₀ X bt body
          (by simpa using hmi_of_see (Rd := []) hRd) hr'
      simp only [Frame.withLocals_mi] at hn
      iapply wp_running_congr_see [(Loc.inst f.inst, .inst f.mi)] hn
      isplitr
      · iapply seeInst $$ Hi
      iunfold wpi at HΦ
      simp only [Frame.withLocals_inst, Frame.withLocals_mi, List.singleton_append]
      iapply HΦ $$ %Ψ %C %hC Hi
      unfold Kont
      simp only [Frame.withLocals_withLocals]
      iexact HK
    · simp only
      iapply wp_running_congr (fun σ => next_br_succ σ lim C (f.withLocals l) vs₀ X _ C.labels n)
      icases HK with ⟨-, ⟨HK, -⟩⟩
      iapply HK $$ %n %(vs₀ ++ X) %l HΦ
  isplit
  · iintro %X %l HΦ
    simp only [Ctx.enter_labels]
    iapply wp_running_congr (fun σ => next_return_label σ lim C (f.withLocals l) vs₀ X _ C.labels)
    icases HK with ⟨-, -, ⟨HK, -⟩⟩
    iapply HK $$ %(vs₀ ++ X) %l HΦ
  · icases HK with ⟨-, -, -, HK⟩
    iexact HK

/-! ## Blocks without parameters

The usual case: block types `[] → []` or `[] → [t]`. The rules take the
operands below the block as they are. -/

theorem wpi_block0 (bt : BlockType) (body : List Instr) (vs₀ : List Value)
    (hp : (Exec.blockType f.mi bt).params = []) :
    ▷ wpi lim d f [] body (Post.block (Exec.blockType f.mi bt).results.length vs₀ Φ)
      ⊢ wpi lim d f vs₀ [.block bt body] Φ := by
  have := wpi_block (Φ := Φ) (lim := lim) (d := d) (f := f) bt body vs₀ [] (by simp [hp])
  simpa using this

theorem wpi_if0_true (bt : BlockType) (th el : List Instr) (vs₀ : List Value) (c : UInt32)
    (hc : c ≠ 0) (hp : (Exec.blockType f.mi bt).params = []) :
    ▷ wpi lim d f [] th (Post.block (Exec.blockType f.mi bt).results.length vs₀ Φ)
      ⊢ wpi lim d f (vs₀ ++ [.i32 c]) [.«if» bt th el] Φ := by
  have := wpi_if_true (Φ := Φ) (lim := lim) (d := d) (f := f) bt th el vs₀ [] c hc (by simp [hp])
  simpa using this

theorem wpi_if0_false (bt : BlockType) (th el : List Instr) (vs₀ : List Value)
    (hp : (Exec.blockType f.mi bt).params = []) :
    ▷ wpi lim d f [] el (Post.block (Exec.blockType f.mi bt).results.length vs₀ Φ)
      ⊢ wpi lim d f (vs₀ ++ [.i32 0]) [.«if» bt th el] Φ := by
  have := wpi_if_false (Φ := Φ) (lim := lim) (d := d) (f := f) bt th el vs₀ [] (by simp [hp])
  simpa using this

theorem wpi_loop0 (bt : BlockType) (body : List Instr) (vs₀ : List Value)
    (hp : (Exec.blockType f.mi bt).params = []) :
    ▷ wpi lim d f [] body (Post.loop lim d bt body 0 vs₀ Φ)
      ⊢ wpi lim d f vs₀ [.loop bt body] Φ := by
  have := wpi_loop (Φ := Φ) (lim := lim) (d := d) (f := f) bt body vs₀ [] (by simp [hp])
  simpa [hp] using this

omit [WasmGS H GF] in
@[simp] theorem Post.block_normal (r : Nat) (vs₀ : List Value) (Φ : Post H GF) (vs : List Value)
    (g : Frame) : (Post.block r vs₀ Φ).normal vs g = Φ.normal (vs₀ ++ vs) g := rfl
omit [WasmGS H GF] in
@[simp] theorem Post.block_br_succ (r : Nat) (vs₀ : List Value) (Φ : Post H GF) (n : Nat)
    (X : List Value) (g : Frame) : (Post.block r vs₀ Φ).br (n + 1) X g = Φ.br n (vs₀ ++ X) g := rfl
omit [WasmGS H GF] in
@[simp] theorem Post.block_ret (r : Nat) (vs₀ : List Value) (Φ : Post H GF) (X : List Value)
    (g : Frame) : (Post.block r vs₀ Φ).ret X g = Φ.ret (vs₀ ++ X) g := rfl
omit [WasmGS H GF] in
@[simp] theorem Post.block_trap (r : Nat) (vs₀ : List Value) (Φ : Post H GF) :
    (Post.block r vs₀ Φ).trap = Φ.trap := rfl

end Rules

end WasmLogic
