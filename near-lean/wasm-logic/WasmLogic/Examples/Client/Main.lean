import WasmLogic.Examples.Stack.Specs
import WasmLogic.Examples.Client.Code

/-!
# The client, end to end

The stack module and the client are linked the way the runtime links them:
the stack is instantiated, the client's imports are resolved against its
exports by name, and the client is instantiated; `linked_instantiates`
checks with the kernel that this gives `linkedStore`.

`main_spec` proves `main` from the stack's specifications alone: the client
never looks at the stack's memory, only at `isStack`. `main_adequate` then
says what every run of `main` in `linkedStore` does: it returns `2`, or `-1`
if the stack could not get a page, and never traps.
-/

namespace WasmLogic.Examples.Client

open Wasm Iris Iris.BI Iris.ProgramLogic WasmLogic WasmLogic.Examples.Stack

/-! ## Linking -/

def newStackFn : Func := { type := 0, locals := [i32t], body := new_stack }
def popFn : Func := { type := 1, locals := [i32t], body := pop }
def pushFn : Func := { type := 2, locals := [i32t], body := push }

def stackInst : ModuleInst :=
  { types := stackTypes, funcAddrs := #[0, 1, 2, 3, 4, 5, 6], tableAddrs := #[0], memAddrs := #[0],
    exports := #[("new_stack", .func 0), ("is_empty", .func 1), ("is_full", .func 2),
      ("pop", .func 3), ("push", .func 4), ("stack_map", .func 5), ("stack_length", .func 6),
      ("table", .table 0)] }

def clientInst : ModuleInst :=
  { types := clientTypes, funcAddrs := #[0, 4, 3, 7], exports := #[("main", .func 7)] }

def linkedStore : Store Unit :=
  { funcs := #[
      .wasm stackTypes[0]! 0 newStackFn,
      .wasm stackTypes[1]! 0 { type := 1, locals := [], body := is_empty },
      .wasm stackTypes[1]! 0 { type := 1, locals := [], body := is_full },
      .wasm stackTypes[1]! 0 popFn,
      .wasm stackTypes[2]! 0 pushFn,
      .wasm stackTypes[2]! 0 { type := 2, locals := [i32t, i32t], body := stack_map },
      .wasm stackTypes[1]! 0 { type := 1, locals := [], body := length_stack },
      .wasm clientTypes[0]! 1 mainFunc],
    tables := #[{ elemType := .funcref, elems := #[.null .funcref], max := none }],
    mems := #[{ pages := #[], max := none }],
    modules := #[stackInst, clientInst],
    host := () }

/-- Both modules validate under nearcore's features; the stack instantiates
with no imports, and the client instantiates against the stack's exports,
giving `linkedStore`. The kernel runs the validator and the linker. -/
theorem linked_instantiates :
    (do let vs ← (stackModule.validate (.nearcore false)).toOption
        let (s₁, si) ← (Link.instantiateWith (Store.empty ()) {} [] vs).toOption
        let vc ← (clientModule.validate (.nearcore false)).toOption
        (Link.instantiateWith s₁ {} [("stack", si)] vc).toOption) = some (linkedStore, clientInst) := by
  kernel_rfl

/-! ## The client's proof -/

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

/-! The stack's functions as the client sees them: specifications of
function invocations, from the fragment specifications of `Specs.lean`. -/

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

/-- `main`, from the stack's specifications: it returns `2` and memory has
grown by a page, or `-1` and memory is as it was, when `new_stack` fails.
Its resources are the stack's functions and instance and the stack's memory
length; it never sees the stack's memory. -/
theorem main_spec (hlim : 1 < lim.maxCallDepth) (Φf : FunPost GF) :
    (0 : Nat) ↪[wf] FuncInst.wasm (H := H) stackTypes[0]! 0 newStackFn ∗
      (3 : Nat) ↪[wf] FuncInst.wasm (H := H) stackTypes[1]! 0 popFn ∗
      (4 : Nat) ↪[wf] FuncInst.wasm (H := H) stackTypes[2]! 0 pushFn ∗
      (0 : Nat) ↪[inst] stackInst ∗ (0 : Nat) ↦[wmlength] 0 ∗
      (∀ k : UInt32, ((⌜k = 2⌝ ∗ (0 : Nat) ↦[wmlength] pageSize) ∨
          (⌜k = 0xFFFFFFFF⌝ ∗ (0 : Nat) ↦[wmlength] 0)) -∗ Φf.ret [.i32 k])
      ⊢ wpInvoke (H := H) lim 0 clientTypes[0]! 1 clientInst mainFunc [] Φf := by
  iintro ⟨#H0, #H3, #H4, #Hsi, Hlen, HΦ⟩
  iapply wpInvoke_intro
  rw [show mainFunc.body = mainBody from rfl, show entryLocals mainFunc [] = #[.i32 0] from rfl,
    show clientTypes[0]!.results.length = 1 from rfl]
  simp only [mainBody]
  wp_step 0 wpi_call 0 0 stackTypes[0]! 0 stackInst newStackFn [] [] rfl rfl (by omega)
  isplitr
  · iexact H0
  isplitr
  · iexact Hsi
  inext
  iapply invoke_new_stack
  isplitl [Hlen]
  · iexact Hlen
  iintro %vs Hd
  icases Hd with (⟨%hvs, Hl⟩ | ⟨%hvs, Hs, Hl⟩)
  · -- `new_stack` failed: return -1.
    subst hvs
    simp only [Post.seq_normal, List.nil_append]
    wp_step 1 wpi_local_tee 0 (.i32 0xFFFFFFFF)
    inext; simp only [Post.seq_normal]
    wp_step 0 wpi_i32_const 0xFFFFFFFF
    inext; simp only [Post.seq_normal]
    wp_step 2 wpi_i32_relop .eq 0xFFFFFFFF 0xFFFFFFFF
    inext; simp only [Post.seq_normal]
    rw [show Numeric.bool (Numeric.irelop32 .eq 0xFFFFFFFF 0xFFFFFFFF) = 1 by decide]
    wp_step 1 wpi_if0_true (.val (.num .i32)) _ _ [] 1 (by decide) rfl
    inext
    wp_step 0 wpi_i32_const 0xFFFFFFFF
    inext; simp only [Post.seq_normal]
    iapply wpi_nil
    simp only [Post.block_normal, Post.seq_normal, List.nil_append]
    iapply wpi_nil
    simp only [Post.func, List.length_singleton, Nat.sub_self, List.drop_zero]
    isplitr
    · ipureintro; exact Nat.le_refl _
    iapply HΦ
    iright
    isplitr
    · ipureintro; rfl
    · iexact Hl
  · -- A stack at address 0: push 4 and 6, pop twice, subtract.
    subst hvs
    simp only [Post.seq_normal, List.nil_append]
    wp_step 1 wpi_local_tee 0 (u32 0)
    inext; simp only [Post.seq_normal]
    wp_step 0 wpi_i32_const 0xFFFFFFFF
    inext; simp only [Post.seq_normal]
    wp_step 2 wpi_i32_relop .eq (UInt32.ofNat 0) 0xFFFFFFFF
    inext; simp only [Post.seq_normal]
    rw [show Numeric.bool (Numeric.irelop32 .eq (UInt32.ofNat 0) 0xFFFFFFFF) = 0 by decide]
    wp_step 1 wpi_if0_false (.val (.num .i32)) _ _ [] rfl
    inext
    wp_step 0 wpi_local_get 0 (u32 0) rfl
    inext; simp only [Post.seq_normal]
    wp_step 0 wpi_i32_const 4
    inext; simp only [Post.seq_normal]
    wp_step 2 wpi_call 1 4 stackTypes[2]! 0 stackInst pushFn [] [u32 0, .i32 4] rfl rfl (by omega)
    isplitr
    · iexact H4
    isplitr
    · iexact Hsi
    inext
    iapply invoke_push 1 0 4 [] (by decide)
    isplitl [Hs]
    · iexact Hs
    iintro Hs
    simp only [Post.seq_normal, List.append_nil]
    wp_step 0 wpi_local_get 0 (u32 0) rfl
    inext; simp only [Post.seq_normal]
    wp_step 0 wpi_i32_const 6
    inext; simp only [Post.seq_normal]
    wp_step 2 wpi_call 1 4 stackTypes[2]! 0 stackInst pushFn [] [u32 0, .i32 6] rfl rfl (by omega)
    isplitr
    · iexact H4
    isplitr
    · iexact Hsi
    inext
    iapply invoke_push 1 0 6 [4] (by decide)
    isplitl [Hs]
    · iexact Hs
    iintro Hs
    simp only [Post.seq_normal, List.append_nil]
    wp_step 0 wpi_local_get 0 (u32 0) rfl
    inext; simp only [Post.seq_normal]
    wp_step 1 wpi_call 2 3 stackTypes[1]! 0 stackInst popFn [] [u32 0] rfl rfl (by omega)
    isplitr
    · iexact H3
    isplitr
    · iexact Hsi
    inext
    iapply invoke_pop 1 0 6 [4]
    isplitl [Hs]
    · iexact Hs
    iintro Hs
    simp only [Post.seq_normal, List.nil_append]
    wp_step 0 wpi_local_get 0 (u32 0) rfl
    inext; simp only [Post.seq_normal]
    wp_step 1 wpi_call 2 3 stackTypes[1]! 0 stackInst popFn [.i32 6] [u32 0] rfl rfl (by omega)
    isplitr
    · iexact H3
    isplitr
    · iexact Hsi
    inext
    iapply invoke_pop 1 0 4 []
    isplitl [Hs]
    · iexact Hs
    iintro -
    simp only [Post.seq_normal]
    wp_step 2 wpi_i32_binop .sub 6 4 2 rfl
    inext; simp only [Post.seq_normal]
    iapply wpi_nil
    simp only [Post.block_normal, Post.seq_normal, List.nil_append]
    iapply wpi_nil
    simp only [Post.func, List.length_singleton, Nat.sub_self, List.drop_zero]
    isplitr
    · ipureintro; exact Nat.le_refl _
    iapply HΦ
    ileft
    isplitr
    · ipureintro; rfl
    · simp only [Nat.zero_add]; iexact Hl

end Proof

/-! ## Every run of `main` -/

/-- The cells of `linkedStore` that `main_spec` needs. -/
def mainCells : List (Loc × Cell Unit) :=
  [(Loc.inst 1, .inst clientInst), (Loc.func 0, .func (.wasm stackTypes[0]! 0 newStackFn)),
    (Loc.func 3, .func (.wasm stackTypes[1]! 0 popFn)), (Loc.func 4, .func (.wasm stackTypes[2]! 0 pushFn)),
    (Loc.inst 0, .inst stackInst), (Loc.memLength 0, .memLength 0)]

theorem mainCells_get : ∀ p ∈ mainCells, Iris.Std.get? (heapOf linkedStore) p.1 = some p.2 := by
  intro p hp
  simp only [mainCells, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> rw [get?_heapOf]
  all_goals first | rfl | simp [linkedStore, Memory.wf, Memory.byteSize]

/-- What `main` leaves in memory 0: one page if it returned 2, else nothing. -/
def mainFinal (vs : List Value) : List (Loc × Cell Unit) :=
  [(Loc.memLength 0, .memLength (if vs = [.i32 2] then pageSize else 0))]

/-- Every run of the linked client's `main` that finishes returns `2`, with
the stack's memory grown to one page, or returns `-1` with memory still
empty; none traps. -/
theorem main_adequate (c : Config Unit) (hc : Exec.startWasm linkedStore {} 7 [] = some c) (fuel : Nat) :
    match Exec.run fuel c with
    | .done vs σ' =>
      (vs = [.i32 2] ∧ ∃ mem, σ'.mems[0]? = some mem ∧ mem.byteSize = pageSize) ∨
        (vs = [.i32 0xFFFFFFFF] ∧ ∃ mem, σ'.mems[0]? = some mem ∧ mem.byteSize = 0)
    | .trap _ _ => False
    | .outOfFuel _ => True := by
  have h := adequacy_cells linkedStore {} 7 [] clientTypes[0]! 1 clientInst mainFunc rfl
    (fun vs => vs = [.i32 2] ∨ vs = [.i32 0xFFFFFFFF]) False mainFinal (fun _ => by simp [mainFinal])
    ?_ c hc fuel
  · revert h
    cases Exec.run fuel c with
    | done vs σ' =>
      intro ⟨hvs, hcells⟩
      obtain ⟨mem, hmem, -, hlen⟩ := memLength_facts (hcells _ List.mem_cons_self)
      rcases hvs with rfl | rfl
      · exact .inl ⟨rfl, mem, hmem, by simpa [mainFinal] using hlen⟩
      · exact .inr ⟨rfl, mem, hmem, by simpa [mainFinal] using hlen⟩
    | trap => exact id
    | outOfFuel => exact id
  intro _
  iintro Hcells
  icases ownCells_take _ mainCells (by decide) mainCells_get $$ Hcells with Hl
  simp only [mainCells]
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hi1, Hl⟩
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hf0, Hl⟩
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hf3, Hl⟩
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hf4, Hl⟩
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hi0, Hl⟩
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hlen, -⟩
  imod pointsTo_persist $$ Hi1 with #Hi1
  imod pointsTo_persist $$ Hf0 with #Hf0
  imod pointsTo_persist $$ Hf3 with #Hf3
  imod pointsTo_persist $$ Hf4 with #Hf4
  imod pointsTo_persist $$ Hi0 with #Hi0
  imodintro
  isplitr
  · iunfold instPt; iexact Hi1
  iapply main_spec (by decide)
  isplitr
  · iunfold funcPt; iexact Hf0
  isplitr
  · iunfold funcPt; iexact Hf3
  isplitr
  · iunfold funcPt; iexact Hf4
  isplitr
  · iunfold instPt; iexact Hi0
  isplitl [Hlen]
  · iunfold memLength; iexact Hlen
  iintro %k Hk
  icases Hk with (⟨%hk, Hl⟩ | ⟨%hk, Hl⟩)
  · subst hk
    isplitr
    · ipureintro; exact .inl rfl
    · simp only [mainFinal, ite_eq_left]
      iapply BigSepL.bigSepL_singleton.2
      iunfold memLength at Hl
      iexact Hl
  · subst hk
    isplitr
    · ipureintro; exact .inr rfl
    · simp only [mainFinal]
      rw [ite_eq_right (by decide)]
      iapply BigSepL.bigSepL_singleton.2
      iunfold memLength at Hl
      iexact Hl

end WasmLogic.Examples.Client
