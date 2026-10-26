import WasmLogic.Examples.Stack.Map

/-!
# The stack module's instance, function by function

The functions of the stack module as a client calls them: the instance the
linker builds for it (functions at store addresses 0 to 6, table 0,
memory 0), and for each exported function a `wpInvoke` specification,
derived from its fragment specification in `Specs.lean` or `Map.lean`.
-/

namespace WasmLogic.Examples.Stack

open Wasm Iris Iris.BI Iris.ProgramLogic WasmLogic

def newStackFn : Func := { type := 0, locals := [i32t], body := new_stack, bodySize := 35 }
def isEmptyFn : Func := { type := 1, locals := [], body := is_empty, bodySize := 27 }
def isFullFn : Func := { type := 1, locals := [], body := is_full, bodySize := 39 }
def lengthFn : Func := { type := 1, locals := [], body := length_stack, bodySize := 30 }
def popFn : Func := { type := 1, locals := [i32t], body := pop, bodySize := 53 }
def pushFn : Func := { type := 2, locals := [i32t], body := push, bodySize := 67 }
def mapFn : Func := { type := 2, locals := [i32t, i32t], body := stack_map, bodySize := 67 }

def stackInst : ModuleInst :=
  { types := stackTypes, funcAddrs := #[0, 1, 2, 3, 4, 5, 6], tableAddrs := #[0], memAddrs := #[0],
    exports := #[("new_stack", .func 0), ("is_empty", .func 1), ("is_full", .func 2),
      ("pop", .func 3), ("push", .func 4), ("stack_map", .func 5), ("stack_length", .func 6),
      ("table", .table 0)] }


section Proof

variable {H : Type} {GF : BundledGFunctors} [WasmGS H GF] {lim : ExecLimits}

/-- A function satisfies its body's triple. -/
theorem invoke_of_triple {d : Nat} (type : FuncType) (inst : Nat) (mi : ModuleInst) (code : Func)
    (args : List Value) (P : IProp GF) (Q : List Value → Frame → IProp GF) (Φf : FunPost GF)
    (h : Triple (H := H) (GF := GF) lim d ⟨entryLocals code args, inst, mi⟩ P code.body Q) :
    P ∗ (∀ vs g, Q vs g -∗ (Post.func (H := H) type.results.length Φf).normal vs g)
      ⊢ wpInvoke lim d type inst mi code args Φf := by
  iintro HP
  iapply wpInvoke_intro
  iapply h (Post.func (H := H) type.results.length Φf)
  iexact HP

theorem invoke_new_stack (d : Nat) (Φf : FunPost GF) :
    (0 : Nat) ↦[wmlength] 0 ∗
      (∀ vs, ((⌜vs = [.i32 0xFFFFFFFF]⌝ ∗ (0 : Nat) ↦[wmlength] 0) ∨
          (⌜vs = [u32 0]⌝ ∗ isStack 0 [] 0 ∗ (0 : Nat) ↦[wmlength] (0 + pageSize))) -∗ Φf.ret vs)
      ⊢ wpInvoke (H := H) lim d stackTypes[0]! 0 stackInst newStackFn [] Φf := by
  iintro ⟨Hlen, HΦ⟩
  iapply invoke_of_triple stackTypes[0]! 0 stackInst newStackFn [] _ _ Φf
    (spec_new_stack (H := H) (GF := GF) (lim := lim) (d := d) ⟨entryLocals newStackFn [], 0, stackInst⟩ 0 0)
  isplitl [Hlen]
  · isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; decide
    isplitr
    · ipureintro; exact Nat.dvd_zero _
    · iexact Hlen
  iintro %vs %g ⟨Hd, -⟩
  icases Hd with (⟨%hvs, Hl⟩ | ⟨%hvs, Hs, Hl⟩)
  · subst hvs
    simp only [Post.func]
    isplitr
    · ipureintro; decide
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    · iexact Hl
  · subst hvs
    simp only [Post.func]
    isplitr
    · ipureintro; decide
    iapply HΦ
    iright
    isplitr
    · ipureintro; rfl
    isplitl [Hs]
    · iexact Hs
    · iexact Hl

theorem invoke_push (d v : Nat) (a : UInt32) (s : List UInt32) (hs : s.length < two14 - 1)
    (Φf : FunPost GF) :
    isStack v s 0 ∗ (isStack v (a :: s) 0 -∗ Φf.ret [])
      ⊢ wpInvoke (H := H) lim d stackTypes[2]! 0 stackInst pushFn [u32 v, .i32 a] Φf := by
  iintro ⟨Hs, HΦ⟩
  iapply invoke_of_triple stackTypes[2]! 0 stackInst pushFn [u32 v, .i32 a] _ _ Φf
    (spec_push (H := H) (GF := GF) (lim := lim) (d := d)
      ⟨entryLocals pushFn [u32 v, .i32 a], 0, stackInst⟩ 0 v a s)
  isplitl [Hs]
  · isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; simp [entryLocals, pushFn]
    isplitr
    · ipureintro; exact hs
    · iexact Hs
  iintro %vs %g ⟨%hvs, Hs, -⟩
  subst hvs
  have hr : stackTypes[2]!.results.length = 0 := rfl
  simp only [Post.func, hr, List.length_nil, Nat.sub_zero, List.drop_zero]
  isplitr
  · ipureintro; exact Nat.le_refl _
  iapply HΦ $$ Hs

theorem invoke_pop (d v : Nat) (a : UInt32) (s : List UInt32) (Φf : FunPost GF) :
    isStack v (a :: s) 0 ∗ (isStack v s 0 -∗ Φf.ret [.i32 a])
      ⊢ wpInvoke (H := H) lim d stackTypes[1]! 0 stackInst popFn [u32 v] Φf := by
  iintro ⟨Hs, HΦ⟩
  iapply invoke_of_triple stackTypes[1]! 0 stackInst popFn [u32 v] _ _ Φf
    (spec_pop (H := H) (GF := GF) (lim := lim) (d := d) ⟨entryLocals popFn [u32 v], 0, stackInst⟩ 0 v a s)
  isplitl [Hs]
  · isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; simp [entryLocals, popFn]
    · iexact Hs
  iintro %vs %g ⟨%hvs, Hs, -⟩
  subst hvs
  have hr : stackTypes[1]!.results.length = 1 := rfl
  simp only [Post.func, hr, List.length_singleton, Nat.sub_self, List.drop_zero]
  isplitr
  · ipureintro; exact Nat.le_refl _
  iapply HΦ $$ Hs

theorem invoke_stack_map (d v : Nat) (fn : UInt32) (s : List UInt32) (a : Nat) (ctype : FuncType)
    (cinst : Nat) (cmi : ModuleInst) (ccode : Func) (Φ : UInt32 → IProp GF)
    (Ψ : UInt32 → UInt32 → IProp GF) (hd : d + 1 < lim.maxCallDepth)
    (hct : ctype = { params := [i32t], results := [i32t] }) (Φf : FunPost GF) :
    isStack v s 0 ∗ stackAll s Φ ∗ (0 : Nat) ↦[wt][ fn.toNat ] Ref.func a ∗
      a ↪[wf] FuncInst.wasm ctype cinst ccode ∗ cinst ↪[inst] cmi ∗
      CalleeSpec (H := H) lim d 0 a fn ctype cinst cmi ccode Φ Ψ ∗
      (∀ s', isStack v s' 0 ∗ stackAll2 s s' Ψ ∗ (0 : Nat) ↦[wt][ fn.toNat ] Ref.func a -∗ Φf.ret [])
      ⊢ wpInvoke (H := H) lim d stackTypes[2]! 0 stackInst mapFn [u32 v, .i32 fn] Φf := by
  iintro ⟨Hs, Hall, Ht, #Hf, #Hi, #Hspec, HΦ⟩
  iapply invoke_of_triple stackTypes[2]! 0 stackInst mapFn [u32 v, .i32 fn] _ _ Φf
    (spec_stack_map (H := H) (GF := GF) (lim := lim) (d := d)
      ⟨entryLocals mapFn [u32 v, .i32 fn], 0, stackInst⟩ 0 v fn s 0 a ctype cinst cmi ccode Φ Ψ hd hct)
  isplitl [Hs Hall Ht]
  · isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; rfl
    isplitl [Hs]
    · iexact Hs
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; simp [entryLocals, mapFn]
    isplitl [Hall]
    · iexact Hall
    isplitr
    · ipureintro; subst hct; rfl
    isplitr
    · ipureintro; rfl
    isplitl [Ht]
    · iexact Ht
    isplitr
    · iexact Hf
    isplitr
    · iexact Hi
    · iexact Hspec
  iintro %vs %g ⟨%hvs, ⟨%s', Hs, H2⟩, -, Ht⟩
  subst hvs
  have hr : stackTypes[2]!.results.length = 0 := rfl
  simp only [Post.func, hr, List.length_nil, Nat.sub_zero, List.drop_zero]
  isplitr
  · ipureintro; exact Nat.le_refl _
  iapply HΦ
  isplitl [Hs]
  · iexact Hs
  isplitl [H2]
  · iexact H2
  · iexact Ht

/-- What `stack_map` is told about table entry 0, `square`: it returns the
square of its argument and gives the entry back. -/

theorem invoke_is_empty (d v : Nat) (s : List UInt32) (Φf : FunPost GF) :
    isStack v s 0 ∗ (∀ k : Nat, ⌜(k = 1 ∧ s = []) ∨ (k = 0 ∧ s ≠ [])⌝ -∗ isStack v s 0 -∗ Φf.ret [u32 k])
      ⊢ wpInvoke (H := H) lim d stackTypes[1]! 0 stackInst isEmptyFn [u32 v] Φf := by
  iintro ⟨Hs, HΦ⟩
  iapply invoke_of_triple stackTypes[1]! 0 stackInst isEmptyFn [u32 v] _ _ Φf
    (spec_is_empty (H := H) (GF := GF) (lim := lim) (d := d) ⟨entryLocals isEmptyFn [u32 v], 0, stackInst⟩ 0 v s)
  isplitl [Hs]
  · isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; rfl
    · iexact Hs
  iintro %vs %g ⟨%k, %hvs, Hs, %hk, -⟩
  subst hvs
  have hr : stackTypes[1]!.results.length = 1 := rfl
  simp only [Post.func, hr, List.length_singleton, Nat.sub_self, List.drop_zero]
  isplitr
  · ipureintro; exact Nat.le_refl _
  iapply HΦ $$ %k %hk Hs

theorem invoke_is_full (d v : Nat) (s : List UInt32) (Φf : FunPost GF) :
    isStack v s 0 ∗ (∀ k : Nat, ⌜(k = 1 ∧ s.length = two14 - 1) ∨ (k = 0 ∧ s.length < two14 - 1)⌝ -∗
        isStack v s 0 -∗ Φf.ret [u32 k])
      ⊢ wpInvoke (H := H) lim d stackTypes[1]! 0 stackInst isFullFn [u32 v] Φf := by
  iintro ⟨Hs, HΦ⟩
  iapply invoke_of_triple stackTypes[1]! 0 stackInst isFullFn [u32 v] _ _ Φf
    (spec_is_full (H := H) (GF := GF) (lim := lim) (d := d) ⟨entryLocals isFullFn [u32 v], 0, stackInst⟩ 0 v s)
  isplitl [Hs]
  · isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; rfl
    · iexact Hs
  iintro %vs %g ⟨%k, %hvs, Hs, %hk, -⟩
  subst hvs
  have hr : stackTypes[1]!.results.length = 1 := rfl
  simp only [Post.func, hr, List.length_singleton, Nat.sub_self, List.drop_zero]
  isplitr
  · ipureintro; exact Nat.le_refl _
  iapply HΦ $$ %k %hk Hs

theorem invoke_stack_length (d v : Nat) (s : List UInt32) (Φf : FunPost GF) :
    isStack v s 0 ∗ (isStack v s 0 -∗ Φf.ret [u32 s.length])
      ⊢ wpInvoke (H := H) lim d stackTypes[1]! 0 stackInst lengthFn [u32 v] Φf := by
  iintro ⟨Hs, HΦ⟩
  iapply invoke_of_triple stackTypes[1]! 0 stackInst lengthFn [u32 v] _ _ Φf
    (spec_stack_length (H := H) (GF := GF) (lim := lim) (d := d) ⟨entryLocals lengthFn [u32 v], 0, stackInst⟩
      0 v s s.length)
  isplitl [Hs]
  · isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; rfl
    isplitr
    · ipureintro; rfl
    · iexact Hs
  iintro %vs %g ⟨%hvs, Hs, -⟩
  subst hvs
  have hr : stackTypes[1]!.results.length = 1 := rfl
  simp only [Post.func, hr, List.length_singleton, Nat.sub_self, List.drop_zero]
  isplitr
  · ipureintro; exact Nat.le_refl _
  iapply HΦ $$ Hs

end Proof

end WasmLogic.Examples.Stack
