import WasmLogic.Resources

/-!
# Weakest preconditions for code fragments

`WP` over the language is about whole threads. Proofs about Wasm code are
about instruction sequences inside a function body, so this file defines a
weakest precondition for a fragment and derives it from thread `WP` by
quantifying over everything outside the fragment.

A fragment runs instructions `es` in a frame `f` (locals and module
instance) with operands `vs` on top of the stack. It ends in one of four
ways, which its postcondition `Φ : Post` describes, as Iris-Wasm's values do
(`immV`, `brV`, `retV`, `trapV`):

- `normal vs' f'`: it falls through with operands `vs'` and frame `f'`;
- `br n vs' f'`: it branches to the `n`-th label around it;
- `ret vs' f'`: it returns from the function;
- `trap`: it traps.

A context `C` is what surrounds the fragment in the thread: the operands
below it, the labels around it, the code after it, the rest of the function
frame and the frames below. `wpi` holds when, for every context and every
continuation `Kont` that knows how to carry on from each way of ending, the
thread running the fragment in that context satisfies `WP`. Branches and
returns carry on "as the context positioned at `br n` / `return`", so the
rules for `block`, `loop` and calls reduce to two threads stepping to the
same place (`wp_running_congr`).

`wpi` also assumes the frame's instance cell, `f.inst ↪[inst] f.mi`, as
Iris-Wasm's frame carries its instance record: rules can use `f.mi` freely.

Iris-Wasm's `↪[frame] f` is not a resource here: the frame is an index of
`wpi` and the postcondition receives the frame the fragment ends with. That
is the same information, threaded explicitly, because locals live in the
thread rather than in the store.
-/

namespace WasmLogic

open Wasm Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
  FromMathlib Std.LawfulSet

/-- A function frame as the logic sees it: locals, and the module instance
by store address and by value. -/
structure Frame where
  locals : Array Value
  inst : Nat
  mi : ModuleInst

/-- The same frame with other locals: a function body never changes its
instance, so this is every frame a fragment can end in. -/
def Frame.withLocals (f : Frame) (l : Array Value) : Frame := { f with locals := l }

@[simp] theorem Frame.withLocals_locals (f : Frame) (l : Array Value) :
    (f.withLocals l).locals = l := rfl
@[simp] theorem Frame.withLocals_inst (f : Frame) (l : Array Value) :
    (f.withLocals l).inst = f.inst := rfl
@[simp] theorem Frame.withLocals_mi (f : Frame) (l : Array Value) :
    (f.withLocals l).mi = f.mi := rfl
@[simp] theorem Frame.withLocals_self (f : Frame) : f.withLocals f.locals = f := rfl
@[simp] theorem Frame.withLocals_withLocals (f : Frame) (l l' : Array Value) :
    (f.withLocals l).withLocals l' = f.withLocals l' := rfl

/-- How a fragment may end. Unstated ways of ending are ruled out. -/
structure Post (H : Type) (GF : BundledGFunctors) where
  normal : List Value → Frame → IProp GF
  br : Nat → List Value → Frame → IProp GF := fun _ _ _ => iprop(False)
  ret : List Value → Frame → IProp GF := fun _ _ => iprop(False)
  trap : IProp GF := iprop(False)

/-- What surrounds a fragment in a thread. -/
structure Ctx where
  base : List Value
  labels : List Label
  rest : List Instr
  arity : Nat
  height : Nat
  below : List CallFrame

/-- The thread with a frame on top, from its whole operand stack. -/
def Ctx.threadA (C : Ctx) (f : Frame) (stack : Array Value) (labels : List Label)
    (code : List Instr) : Thread :=
  { stack := stack,
    frames := { locals := f.locals, inst := f.inst, arity := C.arity, height := C.height,
                labels := labels, code := code } :: C.below }

/-- The thread with a fragment's frame on top, operands `vs` above the base. -/
def Ctx.thread (C : Ctx) (f : Frame) (vs : List Value) (labels : List Label)
    (code : List Instr) : Thread :=
  C.threadA f (C.base ++ vs).toArray labels code

@[simp] theorem Ctx.thread_withRest (C : Ctx) (r : List Instr) :
    ({ C with rest := r } : Ctx).thread = C.thread := rfl

section Defs

variable {H : Type} {GF : BundledGFunctors} [WasmGS H GF]

/-- `WP` of a running thread, for the whole program's postcondition. -/
abbrev wpT (lim : ExecLimits) (t : Thread) (Ψ : Outcome → IProp GF) : IProp GF :=
  WP (Code.running (H := H) lim t) @ Stuckness.MaybeStuck; ⊤ {{ Ψ }}

/-- How the context carries on from each way the fragment can end. -/
def Kont (lim : ExecLimits) (C : Ctx) (f : Frame) (Φ : Post H GF) (Ψ : Outcome → IProp GF) :
    IProp GF :=
  iprop((∀ vs l, Φ.normal vs (f.withLocals l) -∗
      wpT (H := H) lim (C.thread (f.withLocals l) vs C.labels C.rest) Ψ) ∧
    (∀ n vs l, Φ.br n vs (f.withLocals l) -∗
      wpT (H := H) lim (C.thread (f.withLocals l) vs C.labels [.br n]) Ψ) ∧
    (∀ vs l, Φ.ret vs (f.withLocals l) -∗
      wpT (H := H) lim (C.thread (f.withLocals l) vs C.labels [.return]) Ψ) ∧
    (Φ.trap -∗ ∀ r, Ψ (.trap r)))

/-- The weakest precondition of a fragment `es` run in frame `f` on operands
`vs`, at call depth `d` (the number of frames below `f`) under limits `lim`. -/
def wpi (lim : ExecLimits) (d : Nat) (f : Frame) (vs : List Value) (es : List Instr)
    (Φ : Post H GF) : IProp GF :=
  iprop(∀ (Ψ : Outcome → IProp GF) (C : Ctx), ⌜C.below.length = d⌝ -∗ instPt (H := H) f.inst f.mi -∗
    Kont lim C f Φ Ψ -∗ wpT (H := H) lim (C.thread f vs C.labels (es ++ C.rest)) Ψ)

/-- One postcondition implies another, way of ending by way of ending. -/
def Post.wand (Φ Φ' : Post H GF) : IProp GF :=
  iprop((∀ vs f, Φ.normal vs f -∗ Φ'.normal vs f) ∧ (∀ n vs f, Φ.br n vs f -∗ Φ'.br n vs f) ∧
    (∀ vs f, Φ.ret vs f -∗ Φ'.ret vs f) ∧ (Φ.trap -∗ Φ'.trap))

/-- Sequencing: after `es₁` falls through, run `es₂`. -/
def Post.seq (lim : ExecLimits) (d : Nat) (es₂ : List Instr) (Φ : Post H GF) : Post H GF :=
  { Φ with normal := fun vs f => wpi lim d f vs es₂ Φ }

end Defs

section Structural

variable {H : Type} {GF : BundledGFunctors} [ι : WasmGS H GF]
variable {lim : ExecLimits} {d : Nat} {f : Frame} {vs : List Value} {es : List Instr}

theorem wpi_wand {Φ Φ' : Post H GF} : wpi lim d f vs es Φ ∗ Post.wand Φ Φ' ⊢ wpi lim d f vs es Φ' := by
  unfold wpi Post.wand Kont
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

/-- The empty fragment falls through at once. -/
theorem wpi_nil {Φ : Post H GF} : Φ.normal vs f ⊢ wpi lim d f vs [] Φ := by
  unfold wpi Kont
  iintro HΦ %Ψ %C %_ #_ HK
  icases HK with ⟨HK, -⟩
  simp only [List.nil_append]
  ispecialize HK $$ %vs %f.locals
  simp only [Frame.withLocals_self]
  iapply HK $$ HΦ

/-- Sequencing, Iris-Wasm's `wp_seq`. -/
theorem wpi_seq {es₁ es₂ : List Instr} {Φ : Post H GF} :
    wpi lim d f vs es₁ (Post.seq lim d es₂ Φ) ⊢ wpi lim d f vs (es₁ ++ es₂) Φ := by
  unfold wpi Post.seq Kont
  iintro Hwp %Ψ %C %hC #Hi HK
  rw [List.append_assoc]
  ispecialize Hwp $$ %Ψ %{ C with rest := es₂ ++ C.rest } %hC Hi
  simp only [Ctx.thread_withRest]
  iapply Hwp
  isplit
  · iintro %vs' %f' H2
    iunfold wpi, Kont at H2
    simp only [Frame.withLocals_inst, Frame.withLocals_mi, Frame.withLocals_withLocals]
    iapply H2 $$ %Ψ %C %hC Hi
    iexact HK
  · icases HK with ⟨-, HK⟩
    iexact HK

/-- Run one instruction, then the rest: the form proofs step through code in. -/
theorem wpi_cons {i : Instr} {es : List Instr} {Φ : Post H GF} :
    wpi lim d f vs [i] (Post.seq lim d es Φ) ⊢ wpi lim d f vs (i :: es) Φ :=
  wpi_seq (es₁ := [i]) (es₂ := es)

/-- Present the operand stack as its bottom and its top `k` values, the shape
instruction rules are stated in. -/
theorem wpi_split (k : Nat) {es : List Instr} {Φ : Post H GF} :
    wpi lim d f (vs.take (vs.length - k) ++ vs.drop (vs.length - k)) es Φ ⊢ wpi lim d f vs es Φ := by
  rw [List.take_append_drop]

@[simp] theorem Post.seq_normal (es : List Instr) (Φ : Post H GF) (vs : List Value) (g : Frame) :
    (Post.seq lim d es Φ).normal vs g = wpi lim d g vs es Φ := rfl
@[simp] theorem Post.seq_br (es : List Instr) (Φ : Post H GF) (n : Nat) (vs : List Value) (g : Frame) :
    (Post.seq lim d es Φ).br n vs g = Φ.br n vs g := rfl
@[simp] theorem Post.seq_ret (es : List Instr) (Φ : Post H GF) (vs : List Value) (g : Frame) :
    (Post.seq lim d es Φ).ret vs g = Φ.ret vs g := rfl
@[simp] theorem Post.seq_trap (es : List Instr) (Φ : Post H GF) :
    (Post.seq lim d es Φ).trap = Φ.trap := rfl

end Structural

end WasmLogic

/-! ## One instruction -/

namespace WasmLogic

open Wasm Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProgramLogic.Language.Notation
  FromMathlib Std.LawfulSet

section Step

variable {H : Type}

-- Instruction rules compute `Exec.instr` by `simp`; its effects are built
-- with these smart constructors.
attribute [simp] Exec.Effect.continue Exec.Effect.call Exec.Effect.return Exec.Effect.trap

theorem modules_get! {σ : Store H} {i : Nat} {mi : ModuleInst} (h : σ.modules[i]? = some mi) :
    σ.modules[i]! = mi := by
  simp [getElem!_def, h]

/-- A step of an instruction that continues in the same frame. -/
theorem next_instr_continue (σ : Store H) (lim : ExecLimits) (C : Ctx) (f : Frame)
    (vs : List Value) (L : List Label) (i : Instr) (R : List Instr)
    (hmi : σ.modules[f.inst]? = some f.mi) {σ' : Store H} {stack' : Array Value}
    {L' : List Label} {code' : List Instr} {loc' : Array Value}
    (h : Exec.instr σ f.mi f.locals (C.base ++ vs).toArray L i R =
      ⟨σ', .continue stack' L' code' loc'⟩) :
    next σ lim (C.thread f vs L (i :: R)) =
      (.running lim (C.threadA (f.withLocals loc') stack' L' code'), σ') := by
  simp [next, Code.config, Exec.step, Ctx.thread, Ctx.threadA, Frame.withLocals, modules_get! hmi,
    h]

/-- A step of an instruction that traps. -/
theorem next_instr_trap (σ : Store H) (lim : ExecLimits) (C : Ctx) (f : Frame)
    (vs : List Value) (L : List Label) (i : Instr) (R : List Instr)
    (hmi : σ.modules[f.inst]? = some f.mi) {σ' : Store H} {r : Trap}
    (h : Exec.instr σ f.mi f.locals (C.base ++ vs).toArray L i R = ⟨σ', .trap r⟩) :
    next σ lim (C.thread f vs L (i :: R)) = (.finished (.trap r), σ') := by
  simp [next, Code.config, Exec.step, Ctx.thread, Ctx.threadA, modules_get! hmi, h]

end Step

section Instr

variable {H : Type} {GF : BundledGFunctors} [ι : WasmGS H GF]
variable {lim : ExecLimits} {d : Nat} {f : Frame} {vs : List Value}

/-- The pointwise effect of a step on the heap: `Q` replaces `P`. -/
def Replaces (σ σ' : Store H) (P Q : List (Loc × Cell H)) : Prop :=
  ∀ l, lookup σ' l = (Q.lookup l).or (if (P.lookup l).isSome then none else lookup σ l)

/-- The generic rule for an instruction that falls through: it reads `Rd`,
owns `P` and leaves `Q`, from every store with those cells, the module
instance, and any operands below `vs`, labels and code after it. -/
theorem wpi_instr (i : Instr) (vs' : List Value) (loc' : Array Value)
    (Rd P Q : List (Loc × Cell H)) (hP : (P.map (·.1)).Nodup) (hQ : (Q.map (·.1)).Nodup)
    {Φ : Post H GF}
    (h : ∀ σ : Store H, σ.modules[f.inst]? = some f.mi → (∀ p ∈ Rd, lookup σ p.1 = some p.2) →
      (∀ p ∈ P, lookup σ p.1 = some p.2) → ∀ base L R, ∃ σ',
        Exec.instr σ f.mi f.locals (base ++ vs).toArray L i R =
          ⟨σ', .continue (base ++ vs').toArray L R loc'⟩ ∧ Replaces σ σ' P Q)
    (hfresh : ∀ σ : Store H, σ.modules[f.inst]? = some f.mi → (∀ p ∈ Rd, lookup σ p.1 = some p.2) →
      (∀ p ∈ P, lookup σ p.1 = some p.2) →
      ∀ l, (Q.lookup l).isSome → P.lookup l = none → lookup σ l = none) :
    seeList Rd ∗ ([∗list] p ∈ P, p.1 ↦ₛ p.2) ∗
      ▷ (([∗list] p ∈ Q, p.1 ↦ₛ p.2) -∗ Φ.normal vs' (f.withLocals loc'))
      ⊢ wpi lim d f vs [i] Φ := by
  unfold wpi Kont
  iintro ⟨HRd, HP, HΦ⟩ %Ψ %C %hC #Hi HK
  have hmi : ∀ σ : Store H, (∀ p ∈ (Loc.inst f.inst, Cell.inst f.mi) :: Rd,
      lookup σ p.1 = some p.2) → σ.modules[f.inst]? = some f.mi := by
    intro σ hσ
    have := hσ _ List.mem_cons_self
    simp only [lookup_inst, Option.map_eq_some_iff] at this
    obtain ⟨m, hm, he⟩ := this
    cases he; exact hm
  iapply wp_lift lim _ ((Loc.inst f.inst, .inst f.mi) :: Rd) P Q
    (.running lim (C.thread (f.withLocals loc') vs' C.labels C.rest)) hP hQ
  · intro σ hRd hPs
    obtain ⟨σ', hi, hrep⟩ := h σ (hmi σ hRd) (fun p hp => hRd p (List.mem_cons_of_mem _ hp)) hPs
      C.base C.labels C.rest
    rw [List.singleton_append, next_instr_continue σ lim C f vs C.labels i C.rest (hmi σ hRd) hi]
    exact ⟨rfl, hrep⟩
  · intro σ hRd hPs
    exact hfresh σ (hmi σ hRd) (fun p hp => hRd p (List.mem_cons_of_mem _ hp)) hPs
  isplitl [HRd]
  · iapply (seeList_cons _ _).2
    iunfold instPt at Hi
    isplitr
    · iexact Hi
    · iexact HRd
  isplitl [HP]
  · iexact HP
  inext
  iintro HQ
  icases HK with ⟨HK, -⟩
  iapply HK
  iapply HΦ $$ HQ

/-- The generic rule for an instruction that falls through, when its result
depends on the store beyond the owned cells: the continuation is given the
store's facts and chooses accordingly. -/
theorem wpi_instr_dep (i : Instr) (vs' : Store H → List Value) (loc' : Array Value)
    (Rd P : List (Loc × Cell H)) (Q : Store H → List (Loc × Cell H))
    (hP : (P.map (·.1)).Nodup) (hQ : ∀ σ, ((Q σ).map (·.1)).Nodup) {Φ : Post H GF}
    (h : ∀ σ : Store H, σ.modules[f.inst]? = some f.mi → (∀ p ∈ Rd, lookup σ p.1 = some p.2) →
      (∀ p ∈ P, lookup σ p.1 = some p.2) → ∀ base L R, ∃ σ',
        Exec.instr σ f.mi f.locals (base ++ vs).toArray L i R =
          ⟨σ', .continue (base ++ vs' σ).toArray L R loc'⟩ ∧ Replaces σ σ' P (Q σ))
    (hfresh : ∀ σ : Store H, σ.modules[f.inst]? = some f.mi → (∀ p ∈ Rd, lookup σ p.1 = some p.2) →
      (∀ p ∈ P, lookup σ p.1 = some p.2) →
      ∀ l, ((Q σ).lookup l).isSome → P.lookup l = none → lookup σ l = none) :
    seeList Rd ∗ ([∗list] p ∈ P, p.1 ↦ₛ p.2) ∗
      ▷ (∀ σ : Store H, ⌜(∀ p ∈ Rd, lookup σ p.1 = some p.2) ∧ (∀ p ∈ P, lookup σ p.1 = some p.2)⌝ -∗
        ([∗list] p ∈ Q σ, p.1 ↦ₛ p.2) -∗ Φ.normal (vs' σ) (f.withLocals loc'))
      ⊢ wpi lim d f vs [i] Φ := by
  unfold wpi Kont
  iintro ⟨HRd, HP, HΦ⟩ %Ψ %C %hC #Hi HK
  have hmi : ∀ σ : Store H, (∀ p ∈ (Loc.inst f.inst, Cell.inst f.mi) :: Rd,
      lookup σ p.1 = some p.2) → σ.modules[f.inst]? = some f.mi := by
    intro σ hσ
    have := hσ _ List.mem_cons_self
    simp only [lookup_inst, Option.map_eq_some_iff] at this
    obtain ⟨m, hm, he⟩ := this
    cases he; exact hm
  iapply wp_lift_dep lim _ ((Loc.inst f.inst, .inst f.mi) :: Rd) P Q
    (fun σ => .running lim (C.thread (f.withLocals loc') (vs' σ) C.labels C.rest)) hP hQ
  · intro σ hRd hPs
    obtain ⟨σ', hi, hrep⟩ := h σ (hmi σ hRd) (fun p hp => hRd p (List.mem_cons_of_mem _ hp)) hPs
      C.base C.labels C.rest
    rw [List.singleton_append, next_instr_continue σ lim C f vs C.labels i C.rest (hmi σ hRd) hi]
    exact ⟨rfl, hrep⟩
  · intro σ hRd hPs
    exact hfresh σ (hmi σ hRd) (fun p hp => hRd p (List.mem_cons_of_mem _ hp)) hPs
  isplitl [HRd]
  · iapply (seeList_cons _ _).2
    iunfold instPt at Hi
    isplitr
    · iexact Hi
    · iexact HRd
  isplitl [HP]
  · iexact HP
  inext
  iintro %σ %⟨hRd, hPs⟩ HQ
  icases HK with ⟨HK, -⟩
  iapply HK
  iapply HΦ $$ %σ %⟨fun p hp => hRd p (List.mem_cons_of_mem _ hp), hPs⟩ HQ

/-- An instruction that traps with reason `r` after reading `Rd` and owning
`P`, leaving `Q`. -/
theorem wpi_instr_trap (i : Instr) (r : Trap) (Rd P Q : List (Loc × Cell H))
    (hP : (P.map (·.1)).Nodup) (hQ : (Q.map (·.1)).Nodup) {Φ : Post H GF}
    (h : ∀ σ : Store H, σ.modules[f.inst]? = some f.mi → (∀ p ∈ Rd, lookup σ p.1 = some p.2) →
      (∀ p ∈ P, lookup σ p.1 = some p.2) → ∀ base L R, ∃ σ',
        Exec.instr σ f.mi f.locals (base ++ vs).toArray L i R = ⟨σ', .trap r⟩ ∧
          Replaces σ σ' P Q)
    (hfresh : ∀ σ : Store H, σ.modules[f.inst]? = some f.mi → (∀ p ∈ Rd, lookup σ p.1 = some p.2) →
      (∀ p ∈ P, lookup σ p.1 = some p.2) →
      ∀ l, (Q.lookup l).isSome → P.lookup l = none → lookup σ l = none) :
    seeList Rd ∗ ([∗list] p ∈ P, p.1 ↦ₛ p.2) ∗ ▷ (([∗list] p ∈ Q, p.1 ↦ₛ p.2) -∗ Φ.trap)
      ⊢ wpi lim d f vs [i] Φ := by
  unfold wpi Kont
  iintro ⟨HRd, HP, HΦ⟩ %Ψ %C %hC #Hi HK
  have hmi : ∀ σ : Store H, (∀ p ∈ (Loc.inst f.inst, Cell.inst f.mi) :: Rd,
      lookup σ p.1 = some p.2) → σ.modules[f.inst]? = some f.mi := by
    intro σ hσ
    have := hσ _ List.mem_cons_self
    simp only [lookup_inst, Option.map_eq_some_iff] at this
    obtain ⟨m, hm, he⟩ := this
    cases he; exact hm
  iapply wp_lift lim _ ((Loc.inst f.inst, .inst f.mi) :: Rd) P Q (.finished (.trap r)) hP hQ
  · intro σ hRd hPs
    obtain ⟨σ', hi, hrep⟩ := h σ (hmi σ hRd) (fun p hp => hRd p (List.mem_cons_of_mem _ hp)) hPs
      C.base C.labels C.rest
    rw [List.singleton_append, next_instr_trap σ lim C f vs C.labels i C.rest (hmi σ hRd) hi]
    exact ⟨rfl, hrep⟩
  · intro σ hRd hPs
    exact hfresh σ (hmi σ hRd) (fun p hp => hRd p (List.mem_cons_of_mem _ hp)) hPs
  isplitl [HRd]
  · iapply (seeList_cons _ _).2
    iunfold instPt at Hi
    isplitr
    · iexact Hi
    · iexact HRd
  isplitl [HP]
  · iexact HP
  inext
  iintro HQ
  icases HK with ⟨-, -, -, HK⟩
  iapply wp_finished
  ispecialize HΦ $$ HQ
  ispecialize HK $$ HΦ
  ispecialize HK $$ %r
  iexact HK

/-- An instruction that only moves operands and locals: no store access. -/
theorem wpi_pure (i : Instr) (vs' : List Value) (loc' : Array Value) {Φ : Post H GF}
    (h : ∀ σ : Store H, ∀ base L R, Exec.instr σ f.mi f.locals (base ++ vs).toArray L i R =
      ⟨σ, .continue (base ++ vs').toArray L R loc'⟩) :
    ▷ Φ.normal vs' (f.withLocals loc') ⊢ wpi lim d f vs [i] Φ := by
  iintro HΦ
  iapply wpi_instr i vs' loc' [] [] [] List.nodup_nil List.nodup_nil
  · intro σ _ _ _ base L R
    exact ⟨σ, h σ base L R, fun l => by simp⟩
  · intro σ _ _ _ l hl _
    simp at hl
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  inext
  iintro _
  iexact HΦ

/-- An instruction that traps without touching the store. -/
theorem wpi_pure_trap (i : Instr) (r : Trap) {Φ : Post H GF}
    (h : ∀ σ : Store H, ∀ base L R, Exec.instr σ f.mi f.locals (base ++ vs).toArray L i R =
      ⟨σ, .trap r⟩) :
    ▷ Φ.trap ⊢ wpi lim d f vs [i] Φ := by
  iintro HΦ
  iapply wpi_instr_trap i r [] [] [] List.nodup_nil List.nodup_nil
  · intro σ _ _ _ base L R
    exact ⟨σ, h σ base L R, fun l => by simp⟩
  · intro σ _ _ _ l hl _
    simp at hl
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  inext
  iintro _
  iexact HΦ

end Instr

end WasmLogic
