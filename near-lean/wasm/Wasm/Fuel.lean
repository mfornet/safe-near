import Wasm.HostInvariant

/-!
# How far the machine can run without executing an instruction

Most steps of the machine execute an instruction. Three do not: entering a
`block`, falling off the end of a block (popping its label), and falling off
the end of a function (leaving its frame). A metered runner that charges per
instruction charges nothing for these, so its step budget cannot be derived
from gas alone. This file bounds them.

`Config.measure` is the size of every frame's remaining code plus the
continuations its labels hold. Each free step strictly decreases it, and no
step lets it exceed `(maxBody + 1) * depth`: control only ever moves into code
that was part of a function body, and frames are at most the call-depth limit.
So between two instructions there are fewer than that many free steps.
-/

namespace Wasm.Exec

/-! ## The measure -/

mutual
/-- Size of an instruction: one, plus its nested bodies. -/
def instrSize : Instr → Nat
  | .block _ body => codeSize body + 2
  | .loop _ body => codeSize body + 2
  | .«if» _ thenBody elseBody => codeSize thenBody + codeSize elseBody + 2
  | _ => 1

def codeSize : List Instr → Nat
  | [] => 1
  | i :: rest => instrSize i + codeSize rest
end

def _root_.Wasm.Label.weight (label : Label) : Nat := codeSize label.rest + 1

/-- A loop label also holds its body, to re-enter on a branch. -/
def _root_.Wasm.Label.loopSize (label : Label) : Nat :=
  match label.loop with
  | some body => codeSize body
  | none => 0

def labelsWeight : List Label → Nat
  | [] => 0
  | label :: labels => label.weight + labelsWeight labels

def _root_.Wasm.CallFrame.measure (frame : CallFrame) : Nat := codeSize frame.code + labelsWeight frame.labels

def framesMeasure : List CallFrame → Nat
  | [] => 0
  | frame :: frames => frame.measure + 1 + framesMeasure frames

def _root_.Wasm.Config.measure (c : Config H) : Nat := framesMeasure c.thread.frames

/-- Labels nested within a function body of size at most `S`: re-entering any
of them, a loop through its body, stays within `S`. -/
def LabelsFit (S : Nat) : List Label → Prop
  | [] => True
  | label :: labels => label.loopSize + labelsWeight (label :: labels) ≤ S ∧ LabelsFit S labels

def _root_.Wasm.CallFrame.Fits (S : Nat) (frame : CallFrame) : Prop :=
  frame.measure ≤ S ∧ LabelsFit S frame.labels

/-- The largest Wasm function body in the store. -/
def maxBody (store : Store H) : Nat :=
  store.funcs.foldl (fun m fn => match fn with
    | .wasm _ _ code => max m (codeSize code.body)
    | .host _ => m) 0

/-- What every configuration of a run satisfies. -/
structure Bounded (c : Config H) : Prop where
  fits : ∀ frame ∈ c.thread.frames, frame.Fits (maxBody c.store)
  depth : c.thread.frames.length ≤ max 1 c.limits.maxCallDepth

/-! ## Arithmetic on labels -/

theorem labelsWeight_drop_le (labels : List Label) (l : Nat) :
    labelsWeight (labels.drop l) ≤ labelsWeight labels := by
  induction labels generalizing l with
  | nil => simp [labelsWeight]
  | cons label labels ih =>
    cases l with
    | zero => exact Nat.le_refl _
    | succ l => simp only [List.drop_succ_cons, labelsWeight]; have := ih l; omega

theorem labelsWeight_drop_of_get {labels : List Label} {l : Nat} {label : Label}
    (h : labels[l]? = some label) :
    labelsWeight (labels.drop l) = label.weight + labelsWeight (labels.drop (l + 1)) := by
  induction labels generalizing l with
  | nil => simp at h
  | cons head labels ih =>
    cases l with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; rfl
    | succ l => exact ih h

theorem LabelsFit.drop {S : Nat} {labels : List Label} (h : LabelsFit S labels) (l : Nat) :
    LabelsFit S (labels.drop l) := by
  induction labels generalizing l with
  | nil => simp [LabelsFit]
  | cons label labels ih =>
    cases l with
    | zero => exact h
    | succ l => exact ih h.2 l

theorem LabelsFit.get {S : Nat} {labels : List Label} (h : LabelsFit S labels) {l : Nat}
    {label : Label} (hget : labels[l]? = some label) :
    label.loopSize + labelsWeight (labels.drop l) ≤ S := by
  induction labels generalizing l with
  | nil => simp at hget
  | cons head labels ih =>
    cases l with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst hget; exact h.1
    | succ l => exact ih h.2 hget

theorem LabelsFit.weight_le {S : Nat} {labels : List Label} (h : LabelsFit S labels)
    (hne : labels ≠ []) : labelsWeight labels ≤ S := by
  cases labels with
  | nil => exact absurd rfl hne
  | cons label labels => have := h.1; omega

/-! ## How an instruction moves control -/

/-- The labels and code an instruction continues with: the next instruction,
a nested body (under a new label for the instruction's continuation), or a
label's target. -/
def Move (labels : List Label) (i : Instr) (rest : List Instr) (labels' : List Label)
    (code : List Instr) : Prop :=
  (labels' = labels ∧ code = rest) ∨
  (∃ label : Label, labels' = label :: labels ∧ label.rest = rest ∧ codeSize code + 2 ≤ instrSize i ∧
    (label.loop = none ∨ label.loop = some code)) ∨
  (∃ l label, labels[l]? = some label ∧
    ((label.loop = some code ∧ labels' = labels.drop l) ∨
     (label.loop = none ∧ code = label.rest ∧ labels' = labels.drop (l + 1))))

theorem branch_move {store : Store H} {stack : Array Value} {labels : List Label}
    {locals : Array Value} {l : Nat} {i : Instr} {rest : List Instr} {stack' : Array Value}
    {labels' : List Label} {code : List Instr} {locals' : Array Value}
    (h : (branch store stack labels locals l).kind = .continue stack' labels' code locals') :
    Move labels i rest labels' code := by
  unfold branch at h
  split at h
  · cases h
  · rename_i label hget
    dsimp only at h
    split at h
    · rename_i body hloop
      cases h
      exact Or.inr (Or.inr ⟨l, label, hget, Or.inl ⟨hloop, rfl⟩⟩)
    · rename_i hloop
      cases h
      exact Or.inr (Or.inr ⟨l, label, hget, Or.inr ⟨hloop, rfl, rfl⟩⟩)

theorem evalMemOp_move {store : Store H} {inst : ModuleInst} {stack : Array Value}
    {labels : List Label} {rest : List Instr} {locals : Array Value} {k : Memory → Option Memory}
    {i : Instr} {stack' : Array Value} {labels' : List Label} {code : List Instr}
    {locals' : Array Value}
    (h : (evalMemOp store inst stack labels rest locals k).kind = .continue stack' labels' code locals') :
    Move labels i rest labels' code := by
  unfold evalMemOp at h
  repeat' split at h
  all_goals first | (cases h; done) | (cases h; exact Or.inl ⟨rfl, rfl⟩)

set_option maxHeartbeats 4000000 in
/-- Every instruction continues on, into one of its own bodies, or to a label. -/
theorem instr_move (store : Store H) (inst : ModuleInst) (locals stack : Array Value)
    (labels : List Label) (i : Instr) (rest : List Instr) {stack' : Array Value}
    {labels' : List Label} {code : List Instr} {locals' : Array Value}
    (h : (instr store inst locals stack labels i rest).kind = .continue stack' labels' code locals') :
    Move labels i rest labels' code := by
  unfold instr at h
  cases i <;> dsimp only at h <;> (repeat' split at h) <;>
    first
    | (cases h; done)
    | (cases h; exact Or.inl ⟨rfl, rfl⟩)
    | exact branch_move h
    | exact evalMemOp_move h
    | (cases h
       refine Or.inr (Or.inl ⟨_, rfl, rfl, ?_, by simp⟩)
       simp only [instrSize]
       split <;> omega)
    | (cases h
       refine Or.inr (Or.inl ⟨_, rfl, rfl, ?_, by simp⟩)
       simp only [instrSize]
       omega)

/-! ## The store's function bodies -/

theorem maxBody_congr {s t : Store H} (h : s.funcs = t.funcs) : maxBody s = maxBody t := by
  unfold maxBody; rw [h]

theorem foldl_maxBody_ge (fs : List (FuncInst H)) (m : Nat) :
    m ≤ fs.foldl (fun m fn => match fn with
      | .wasm _ _ code => max m (codeSize code.body)
      | .host _ => m) m := by
  induction fs generalizing m with
  | nil => exact Nat.le_refl _
  | cons fn fs ih =>
    simp only [List.foldl_cons]
    refine Nat.le_trans ?_ (ih _)
    split
    · exact Nat.le_max_left _ _
    · exact Nat.le_refl _

theorem le_foldl_maxBody {type : FuncType} {inst : Nat} {code : Func} (fs : List (FuncInst H))
    (m : Nat) (hmem : FuncInst.wasm type inst code ∈ fs) :
    codeSize code.body ≤ fs.foldl (fun m fn => match fn with
      | .wasm _ _ code => max m (codeSize code.body)
      | .host _ => m) m := by
  induction fs generalizing m with
  | nil => simp at hmem
  | cons fn fs ih =>
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact Nat.le_trans (Nat.le_max_right _ _) (foldl_maxBody_ge fs _)
    · exact ih _ hmem

theorem le_maxBody {store : Store H} {addr : Nat} {type : FuncType} {inst : Nat} {code : Func}
    (h : store.funcs[addr]? = some (.wasm type inst code)) : codeSize code.body ≤ maxBody store := by
  unfold maxBody
  rw [← Array.foldl_toList]
  exact le_foldl_maxBody _ _ (by rw [Array.mem_toList_iff]; exact Array.mem_of_getElem? h)

/-! ## Steps -/

theorem codeSize_pos (code : List Instr) : 0 < codeSize code := by
  cases code with
  | nil => simp [codeSize]
  | cons i rest =>
    simp only [codeSize]
    cases i <;> simp only [instrSize] <;> omega

theorem instrSize_pos (i : Instr) : 0 < instrSize i := by
  cases i <;> simp only [instrSize] <;> omega

theorem leave_next {c : Config H} {store : Store H} {stack : Array Value} {frame : CallFrame}
    {frames : List CallFrame} {c' : Config H} (h : leave c store stack frame frames = .next c') :
    c'.thread.frames = frames ∧ c'.limits = c.limits ∧ c'.store = store := by
  unfold leave at h
  dsimp only at h
  split at h
  · cases h
  · cases h; exact ⟨rfl, rfl, rfl⟩

/-- A call keeps the frames, after a host call, or pushes the callee's frame. -/
theorem enter_next {c : Config H} {stack : Array Value} {frames : List CallFrame} {addr : Nat}
    {c' : Config H} (h : enter c stack frames addr = .next c') :
    c'.limits = c.limits ∧ c'.store.funcs = c.store.funcs ∧
    (c'.thread.frames = frames ∨
      ∃ type inst code locals arity height, c.store.funcs[addr]? = some (.wasm type inst code) ∧
        frames.length < c.limits.maxCallDepth ∧
        c'.thread.frames = { locals, inst, arity, height, labels := [], code := code.body } :: frames) := by
  have hfuncs := enter_funcs c stack frames addr
  rw [h] at hfuncs
  refine ⟨?_, hfuncs, ?_⟩ <;> unfold enter at h <;> split at h
  · cases h
  · rename_i fn hfn
    dsimp only at h
    split at h
    · split at h
      · cases h
      · cases h; rfl
    · cases h
  · rename_i type inst code hfn
    dsimp only at h
    split at h
    · cases h
    · cases h; rfl
  · cases h
  · rename_i fn hfn
    dsimp only at h
    split at h
    · split at h
      · cases h
      · cases h; exact Or.inl rfl
    · cases h
  · rename_i type inst code hfn
    dsimp only at h
    split at h
    · cases h
    · rename_i hdepth
      cases h
      exact Or.inr ⟨type, inst, code, _, _, _, hfn, by omega, rfl⟩

theorem Fits.rest {S : Nat} {frame : CallFrame} {i : Instr} {rest : List Instr}
    (hcode : frame.code = i :: rest) (hf : frame.Fits S) : ({ frame with code := rest } : CallFrame).Fits S := by
  refine ⟨?_, hf.2⟩
  have := hf.1
  have := instrSize_pos i
  simp only [CallFrame.measure, hcode, codeSize] at *
  omega

theorem Fits.move {S : Nat} {frame : CallFrame} {i : Instr} {rest : List Instr}
    {labels : List Label} {code : List Instr} {locals : Array Value}
    (hcode : frame.code = i :: rest) (hf : frame.Fits S) (hm : Move frame.labels i rest labels code) :
    ({ frame with labels := labels, code := code, locals := locals } : CallFrame).Fits S := by
  obtain ⟨hmeasure, hlabels⟩ := hf
  simp only [CallFrame.measure, hcode, codeSize] at hmeasure
  rcases hm with ⟨rfl, rfl⟩ | ⟨label, rfl, hrest, hsize, hloop⟩ | ⟨l, label, hget, hbranch⟩
  · have := instrSize_pos i
    exact ⟨by simp only [CallFrame.measure]; omega, hlabels⟩
  · have hloopSize : label.loopSize ≤ codeSize code := by
      unfold Label.loopSize
      rcases hloop with h | h <;> rw [h]
      · exact Nat.zero_le _
      · exact Nat.le_refl _
    have hw : label.weight = codeSize rest + 1 := by simp [Label.weight, hrest]
    refine ⟨?_, ⟨?_, hlabels⟩⟩
    · simp only [CallFrame.measure, labelsWeight, hw]; omega
    · simp only [labelsWeight, hw]; omega
  · have hfit := hlabels.get hget
    have hdrop := labelsWeight_drop_le frame.labels l
    rcases hbranch with ⟨hloop, rfl⟩ | ⟨hloop, rfl, rfl⟩
    · refine ⟨?_, hlabels.drop l⟩
      simp only [CallFrame.measure]
      simp only [Label.loopSize, hloop] at hfit
      exact hfit
    · refine ⟨?_, hlabels.drop (l + 1)⟩
      have := labelsWeight_drop_of_get hget
      simp only [CallFrame.measure]
      simp only [Label.weight] at this
      omega

theorem Fits.pop {S : Nat} {frame : CallFrame} {label : Label} {labels : List Label}
    (hcode : frame.code = []) (hl : frame.labels = label :: labels) (hf : frame.Fits S) :
    ({ frame with labels := labels, code := label.rest } : CallFrame).Fits S := by
  obtain ⟨hmeasure, hlabels⟩ := hf
  rw [hl] at hlabels
  refine ⟨?_, hlabels.2⟩
  simp only [CallFrame.measure, hcode, hl, labelsWeight, codeSize, Label.weight] at hmeasure ⊢
  omega

set_option maxHeartbeats 4000000 in
/-- A call returns to the instruction's continuation. -/
theorem instr_call_rest (store : Store H) (inst : ModuleInst) (locals stack : Array Value)
    (labels : List Label) (i : Instr) (rest : List Instr) {stack' : Array Value} {addr : Nat}
    {rest' : List Instr}
    (h : (instr store inst locals stack labels i rest).kind = .call stack' addr rest') : rest' = rest := by
  unfold instr at h
  cases i <;> dsimp only at h <;> (repeat' split at h) <;>
    first
    | (cases h; done)
    | (cases h; rfl)
    | (unfold branch at h; (repeat' split at h) <;> cases h)
    | (unfold evalMemOp at h; (repeat' split at h) <;> cases h)

theorem step_store_funcs {c c' : Config H} (h : step c = .next c') : c'.store.funcs = c.store.funcs := by
  have := step_funcs c
  rw [h] at this
  exact this

/-- Every step keeps the frames within the store's function bodies and the
call-depth limit. -/
theorem step_bounded {c c' : Config H} (h : step c = .next c') (hb : Bounded c) : Bounded c' := by
  have hS : maxBody c'.store = maxBody c.store := maxBody_congr (step_store_funcs h)
  unfold step at h
  split at h
  · cases h
  · rename_i frame frames hframes
    have hfit : frame.Fits (maxBody c.store) := hb.fits frame (by rw [hframes]; simp)
    have hrest : ∀ f ∈ frames, f.Fits (maxBody c.store) :=
      fun f hf => hb.fits f (by rw [hframes]; simp [hf])
    have hdepth := hb.depth
    rw [hframes] at hdepth
    simp only [List.length_cons] at hdepth
    split at h
    · obtain ⟨hf', hl, _⟩ := leave_next h
      refine ⟨by rw [hS, hf']; exact hrest, by rw [hf', hl]; omega⟩
    · rename_i label labels hcode hlabels
      cases h
      refine ⟨?_, by simpa using hdepth⟩
      intro f hf
      simp only [List.mem_cons] at hf
      rcases hf with rfl | hf
      · exact Fits.pop hcode hlabels hfit
      · exact hrest f hf
    · rename_i labels i rest hcode
      dsimp only at h
      split at h
      · rename_i stack' labels' code locals' hkind
        cases h
        have hm := instr_move _ _ _ _ _ _ _ hkind
        refine ⟨?_, by simpa using hdepth⟩
        intro f hf
        rw [hS]
        simp only [List.mem_cons] at hf
        rcases hf with rfl | hf
        · exact Fits.move hcode hfit hm
        · exact hrest f hf
      · rename_i stack' addr rest' hkind
        have hr := instr_call_rest _ _ _ _ _ _ _ hkind
        subst hr
        obtain ⟨hl, hfuncs, hframes'⟩ := enter_next h
        have hhead := Fits.rest (frame := frame) hcode hfit
        rcases hframes' with hf' | ⟨type, inst, code, locals, arity, height, hfn, hlt, hf'⟩
        · refine ⟨?_, by rw [hf', hl]; simpa using hdepth⟩
          rw [hS, hf']
          intro f hf
          simp only [List.mem_cons] at hf
          rcases hf with rfl | hf
          · exact hhead
          · exact hrest f hf
        · refine ⟨?_, by rw [hf', hl]; simp only [List.length_cons] at hlt ⊢; omega⟩
          rw [hS, hf']
          intro f hf
          simp only [List.mem_cons] at hf
          rcases hf with rfl | rfl | hf
          · refine ⟨?_, trivial⟩
            have hle := le_maxBody hfn
            rw [maxBody_congr hfuncs.symm, hS] at hle
            simpa [CallFrame.measure, labelsWeight] using hle
          · exact hhead
          · exact hrest f hf
      · obtain ⟨hf', hl, _⟩ := leave_next h
        refine ⟨by rw [hS, hf']; exact hrest, by rw [hf', hl]; omega⟩
      · cases h

/-- A step that executes no instruction: entering a block, or falling off the
end of a block or of a function. -/
def FreeStep (c : Config H) : Prop :=
  c.nextInstr? = none ∨ ∃ bt body, c.nextInstr? = some (.block bt body)

/-- Free steps shrink the measure. -/
theorem step_free_decreases {c c' : Config H} (h : step c = .next c') (hfree : FreeStep c) :
    c'.measure < c.measure := by
  unfold step at h
  split at h
  · cases h
  · rename_i frame frames hframes
    have hnext : c.nextInstr? = frame.code.head? := by
      simp [Config.nextInstr?, hframes]
    unfold Config.measure
    rw [hframes]
    split at h
    · obtain ⟨hf', _, _⟩ := leave_next h
      rw [hf']
      simp only [framesMeasure]
      omega
    · rename_i label labels hcode hlabels
      cases h
      simp only [framesMeasure, CallFrame.measure, hcode, hlabels, labelsWeight, codeSize,
        Label.weight]
      omega
    · rename_i labels i rest hcode
      unfold FreeStep at hfree
      rw [hnext, hcode] at hfree
      rcases hfree with hnone | ⟨bt, body, hblock⟩
      · simp at hnone
      · simp only [List.head?_cons, Option.some.injEq] at hblock
        subst hblock
        dsimp only at h
        split at h
        · rename_i stack' labels' code locals' hkind
          simp only [instr, Effect.continue] at hkind
          cases hkind
          cases h
          simp only [framesMeasure, CallFrame.measure, hcode, labelsWeight, codeSize, instrSize,
            Label.weight]
          omega
        all_goals simp [instr, Effect.continue] at *

theorem framesMeasure_le {S : Nat} (frames : List CallFrame) (h : ∀ f ∈ frames, f.Fits S) :
    framesMeasure frames ≤ frames.length * (S + 1) := by
  induction frames with
  | nil => simp [framesMeasure]
  | cons f fs ih =>
    have hf := (h f (by simp)).1
    have := ih fun g hg => h g (by simp [hg])
    simp only [framesMeasure, List.length_cons, Nat.succ_mul]
    omega

/-- No configuration of a run is far from executing an instruction. -/
theorem Bounded.measure_le {c : Config H} (hb : Bounded c) :
    c.measure ≤ max 1 c.limits.maxCallDepth * (maxBody c.store + 1) :=
  Nat.le_trans (framesMeasure_le _ hb.fits) (Nat.mul_le_mul_right _ hb.depth)

end Wasm.Exec
