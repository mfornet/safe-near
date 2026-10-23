import WasmLogic.Examples.Stack.Map
import WasmLogic.Examples.Client.Code

/-!
# The client, end to end

Iris-Wasm's `stack_client.v`. The stack module and the client are linked the
way the runtime links them: the stack is instantiated, the client's imports
are resolved against its exports by name, and the client is allocated and
its element segment written into the stack's table; `client_links` checks
with the kernel that this gives `linkedStore`. The linker then runs the
client's start function, `main`.

`main_spec` proves `main` from the stack's specifications alone: the client
never looks at the stack's memory, only at `isStack`. `square_spec` is the
specification `stack_map` is given for the table entry. `start_adequate`
says what every run of the start function does, for any fuel: it never
traps, and when it finishes, `answer` holds 20 and the stack's memory has
one page, or `answer` holds -1 and memory is empty.
-/

namespace WasmLogic.Examples.Client

open Wasm Iris Iris.BI Iris.ProgramLogic WasmLogic WasmLogic.Examples.Stack

/-! ## Linking -/

def newStackFn : Func := { type := 0, locals := [i32t], body := new_stack }
def popFn : Func := { type := 1, locals := [i32t], body := pop }
def pushFn : Func := { type := 2, locals := [i32t], body := push }
def mapFn : Func := { type := 2, locals := [i32t, i32t], body := stack_map }

def stackInst : ModuleInst :=
  { types := stackTypes, funcAddrs := #[0, 1, 2, 3, 4, 5, 6], tableAddrs := #[0], memAddrs := #[0],
    exports := #[("new_stack", .func 0), ("is_empty", .func 1), ("is_full", .func 2),
      ("pop", .func 3), ("push", .func 4), ("stack_map", .func 5), ("stack_length", .func 6),
      ("table", .table 0)] }

def clientInst : ModuleInst :=
  { types := clientTypes, funcAddrs := #[0, 1, 2, 3, 4, 5, 6, 7, 8], tableAddrs := #[0],
    globalAddrs := #[0], elemAddrs := #[0], exports := #[("answer", .global 0)] }

/-- The store after both modules are allocated and the client's element
segment is written, before the start function runs. -/
def linkedStore : Store Unit :=
  { funcs := #[
      .wasm stackTypes[0]! 0 newStackFn,
      .wasm stackTypes[1]! 0 { type := 1, locals := [], body := is_empty },
      .wasm stackTypes[1]! 0 { type := 1, locals := [], body := is_full },
      .wasm stackTypes[1]! 0 popFn,
      .wasm stackTypes[2]! 0 pushFn,
      .wasm stackTypes[2]! 0 mapFn,
      .wasm stackTypes[1]! 0 { type := 1, locals := [], body := length_stack },
      .wasm clientTypes[0]! 1 mainFunc,
      .wasm clientTypes[2]! 1 squareFunc],
    tables := #[{ elemType := .funcref, elems := #[.func 8], max := none }],
    mems := #[{ pages := #[], max := none }],
    globals := #[{ type := answerType, value := .i32 0 }],
    elems := #[{ elems := #[] }],
    modules := #[stackInst, clientInst],
    host := () }

/-- Both modules validate under the features `NearVM` validates with; the stack instantiates
with no imports; the client's imports resolve against the stack's exports,
and allocating the client gives `linkedStore`. The kernel runs the
validator, the resolver and the linker. -/
theorem client_links :
    (do let vs ← (stackModule.validate (.nearcore true)).toOption
        let (s₁, si) ← (Link.instantiateWith (Store.empty ()) {} [] vs).toOption
        let vc ← (clientModule.validate (.nearcore true)).toOption
        let imports ← (Link.resolve (H := Unit) [("stack", si)] vc.module).toOption
        let r ← (Link.instantiateModule s₁ vc imports).toOption
        pure (vc.module, r)) = some (clientModule, linkedStore, clientInst) := by
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
abbrev squarePost : UInt32 → UInt32 → IProp GF := fun u w => iprop(⌜w = u * u⌝)

theorem square_spec (d : Nat) :
    ⊢ CalleeSpec (H := H) (GF := GF) lim d 0 8 0 clientTypes[2]! 1 clientInst squareFunc
      (fun _ => iprop(emp)) squarePost := by
  iintro !> %u %Φf ⟨-, Ht, HΦ⟩
  iapply wpInvoke_intro
  rw [show squareFunc.body = square from rfl, show entryLocals squareFunc [.i32 u] = #[.i32 u] from rfl,
    show clientTypes[2]!.results.length = 1 from rfl]
  simp only [square]
  wp_step 0 wpi_local_get 0 (.i32 u) rfl
  inext; simp only [Post.seq_normal]
  wp_step 0 wpi_local_get 0 (.i32 u) rfl
  inext; simp only [Post.seq_normal]
  wp_step 2 wpi_i32_binop .mul u u (u * u) rfl
  inext; simp only [Post.seq_normal]
  iapply wpi_nil
  simp only [Post.func, List.nil_append, List.length_singleton, Nat.sub_self, List.drop_zero]
  isplitr
  · ipureintro; exact Nat.le_refl _
  iapply HΦ
  isplitr
  · ipureintro; rfl
  · iexact Ht

theorem stackAll_emp (s : List UInt32) : ⊢ stackAll (GF := GF) s (fun _ => iprop(emp)) := by
  unfold stackAll
  induction s with
  | nil => iapply BigSepL.bigSepL_nil.2; iempintro
  | cons a s ih =>
    iapply BigSepL.bigSepL_cons.2
    isplitr
    · iempintro
    · iapply ih

/-- `stackAll2` of squares determines the second list. -/
theorem stackAll2_square (s s' : List UInt32) :
    stackAll2 (GF := GF) s s' squarePost ⊢ ⌜s' = s.map (fun u => u * u)⌝ := by
  induction s generalizing s' with
  | nil =>
    cases s' with
    | nil => iintro -; ipureintro; rfl
    | cons b s' => iintro H; simp only [stackAll2]; iexfalso; iexact H
  | cons a s ih =>
    cases s' with
    | nil => iintro H; simp only [stackAll2]; iexfalso; iexact H
    | cons b s' =>
      rw [stackAll2_cons]
      iintro ⟨%hb, H⟩
      ihave %hs := ih s' $$ H
      ipureintro
      simp [hb, hs]

/-- The global `answer` holding `k`. -/
abbrev answerPt (k : UInt32) : IProp GF := (0 : Nat) ↦[wg] { type := answerType, value := .i32 k }

/-- `main`, from the stack's specifications and `square_spec`: it stores
`20` in `answer` and the stack's memory has grown by a page, or, when
`new_stack` fails, it stores `-1` and memory is as it was. -/
theorem main_spec (hlim : 2 < lim.maxCallDepth) (Φf : FunPost GF) :
    (0 : Nat) ↪[wf] FuncInst.wasm (H := H) stackTypes[0]! 0 newStackFn ∗
      (3 : Nat) ↪[wf] FuncInst.wasm (H := H) stackTypes[1]! 0 popFn ∗
      (4 : Nat) ↪[wf] FuncInst.wasm (H := H) stackTypes[2]! 0 pushFn ∗
      (5 : Nat) ↪[wf] FuncInst.wasm (H := H) stackTypes[2]! 0 mapFn ∗
      (8 : Nat) ↪[wf] FuncInst.wasm (H := H) clientTypes[2]! 1 squareFunc ∗
      (0 : Nat) ↪[inst] stackInst ∗ (1 : Nat) ↪[inst] clientInst ∗
      (0 : Nat) ↦[wmlength] 0 ∗ (0 : Nat) ↦[wt][ 0 ] Ref.func 8 ∗ answerPt 0 ∗
      (∀ k : UInt32, ((⌜k = 20⌝ ∗ (0 : Nat) ↦[wmlength] pageSize) ∨
          (⌜k = 0xFFFFFFFF⌝ ∗ (0 : Nat) ↦[wmlength] 0)) ∗ answerPt k -∗ Φf.ret [])
      ⊢ wpInvoke (H := H) lim 0 clientTypes[0]! 1 clientInst mainFunc [] Φf := by
  iintro ⟨#H0, #H3, #H4, #H5, #H8, #Hsi, #Hci, Hlen, Ht, Ha, HΦ⟩
  iapply wpInvoke_intro
  rw [show mainFunc.body = main from rfl, show entryLocals mainFunc [] = #[.i32 0] from rfl,
    show clientTypes[0]!.results.length = 0 from rfl]
  simp only [main]
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
  · -- `new_stack` failed: store -1 and return.
    subst hvs
    simp only [Post.seq_normal, List.nil_append]
    wp_step 1 wpi_local_tee 0 (.i32 0xFFFFFFFF)
    inext; simp only [Post.seq_normal]
    wp_step 0 wpi_i32_const 0xFFFFFFFF
    inext; simp only [Post.seq_normal]
    wp_step 2 wpi_i32_relop .eq 0xFFFFFFFF 0xFFFFFFFF
    inext; simp only [Post.seq_normal]
    rw [show Numeric.bool (Numeric.irelop32 .eq 0xFFFFFFFF 0xFFFFFFFF) = 1 by decide]
    wp_step 1 wpi_if0_true .empty _ _ [] 1 (by decide) rfl
    inext
    wp_step 0 wpi_i32_const 0xFFFFFFFF
    inext; simp only [Post.seq_normal]
    wp_step 1 wpi_global_set 0 0 { type := answerType, value := .i32 0 } (.i32 0xFFFFFFFF) rfl
    isplitl [Ha]
    · iexact Ha
    inext; iintro Ha; simp only [Post.seq_normal]
    wp_step 0 wpi_return
    simp only [Post.block_ret, Post.seq_ret, Post.func, List.nil_append, List.length_nil,
      Nat.sub_zero, List.drop_zero]
    isplitr
    · ipureintro; exact Nat.le_refl _
    iapply HΦ
    isplitl [Hl]
    · iright
      isplitr
      · ipureintro; rfl
      · iexact Hl
    · iexact Ha
  · -- A stack at address 0: push 4 and 6, square both, pop 36 and 16.
    subst hvs
    simp only [Post.seq_normal, List.nil_append]
    wp_step 1 wpi_local_tee 0 (u32 0)
    inext; simp only [Post.seq_normal]
    wp_step 0 wpi_i32_const 0xFFFFFFFF
    inext; simp only [Post.seq_normal]
    wp_step 2 wpi_i32_relop .eq (UInt32.ofNat 0) 0xFFFFFFFF
    inext; simp only [Post.seq_normal]
    rw [show Numeric.bool (Numeric.irelop32 .eq (UInt32.ofNat 0) 0xFFFFFFFF) = 0 by decide]
    wp_step 1 wpi_if0_false .empty _ _ [] rfl
    inext
    iapply wpi_nil
    simp only [Post.block_normal, Post.seq_normal, List.nil_append]
    wp_step 0 wpi_local_get 0 (u32 0) rfl
    inext; simp only [Post.seq_normal]
    wp_step 0 wpi_i32_const 4
    inext; simp only [Post.seq_normal]
    wp_step 2 wpi_call 4 4 stackTypes[2]! 0 stackInst pushFn [] [u32 0, .i32 4] rfl rfl (by omega)
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
    wp_step 2 wpi_call 4 4 stackTypes[2]! 0 stackInst pushFn [] [u32 0, .i32 6] rfl rfl (by omega)
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
    wp_step 0 wpi_i32_const 0
    inext; simp only [Post.seq_normal]
    wp_step 2 wpi_call 5 5 stackTypes[2]! 0 stackInst mapFn [] [u32 0, .i32 0] rfl rfl (by omega)
    isplitr
    · iexact H5
    isplitr
    · iexact Hsi
    inext
    iapply invoke_stack_map 1 0 0 [6, 4] 8 clientTypes[2]! 1 clientInst squareFunc (fun _ => iprop(emp))
      squarePost (by omega) rfl
    rw [show UInt32.toNat 0 = 0 from rfl]
    isplitl [Hs]
    · iexact Hs
    isplitr
    · iapply stackAll_emp
    isplitl [Ht]
    · iexact Ht
    isplitr
    · iexact H8
    isplitr
    · iexact Hci
    isplitr
    · iapply square_spec
    iintro %s' ⟨Hs, H2, -⟩
    ihave %hs' := stackAll2_square [6, 4] s' $$ H2
    simp only [List.map_cons, List.map_nil] at hs'
    subst hs'
    simp only [Post.seq_normal, List.append_nil]
    wp_step 0 wpi_local_get 0 (u32 0) rfl
    inext; simp only [Post.seq_normal]
    wp_step 1 wpi_call 3 3 stackTypes[1]! 0 stackInst popFn [] [u32 0] rfl rfl (by omega)
    isplitr
    · iexact H3
    isplitr
    · iexact Hsi
    inext
    iapply invoke_pop 1 0 (6 * 6) [4 * 4]
    isplitl [Hs]
    · iexact Hs
    iintro Hs
    simp only [Post.seq_normal, List.nil_append]
    wp_step 0 wpi_local_get 0 (u32 0) rfl
    inext; simp only [Post.seq_normal]
    wp_step 1 wpi_call 3 3 stackTypes[1]! 0 stackInst popFn [.i32 (6 * 6)] [u32 0] rfl rfl (by omega)
    isplitr
    · iexact H3
    isplitr
    · iexact Hsi
    inext
    iapply invoke_pop 1 0 (4 * 4) []
    isplitl [Hs]
    · iexact Hs
    iintro -
    simp only [Post.seq_normal]
    wp_step 2 wpi_i32_binop .sub (6 * 6) (4 * 4) 20 rfl
    inext; simp only [Post.seq_normal]
    wp_step 1 wpi_global_set 0 0 { type := answerType, value := .i32 0 } (.i32 20) rfl
    isplitl [Ha]
    · iexact Ha
    inext; iintro Ha; simp only [Post.seq_normal]
    iapply wpi_nil
    simp only [Post.func, List.length_nil, Nat.sub_zero, List.drop_zero]
    isplitr
    · ipureintro; exact Nat.le_refl _
    iapply HΦ
    isplitl [Hl]
    · ileft
      isplitr
      · ipureintro; rfl
      · simp only [Nat.zero_add]; iexact Hl
    · iexact Ha

end Proof

/-! ## Every run of the start function -/

/-- The cells of `linkedStore` that `main_spec` needs. -/
def mainCells : List (Loc × Cell Unit) :=
  [(Loc.inst 1, .inst clientInst), (Loc.func 0, .func (.wasm stackTypes[0]! 0 newStackFn)),
    (Loc.func 3, .func (.wasm stackTypes[1]! 0 popFn)), (Loc.func 4, .func (.wasm stackTypes[2]! 0 pushFn)),
    (Loc.func 5, .func (.wasm stackTypes[2]! 0 mapFn)),
    (Loc.func 8, .func (.wasm clientTypes[2]! 1 squareFunc)),
    (Loc.inst 0, .inst stackInst), (Loc.memLength 0, .memLength 0),
    (Loc.tableElem 0 0, .ref (.func 8)), (Loc.global 0, .global { type := answerType, value := .i32 0 })]

theorem mainCells_get : ∀ p ∈ mainCells, Iris.Std.get? (heapOf linkedStore) p.1 = some p.2 := by
  intro p hp
  simp only [mainCells, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [get?_heapOf]
  all_goals first | rfl | simp [linkedStore, Memory.wf, Memory.byteSize]

/-- What the run leaves: `answer` and the stack's memory length. -/
def finalCells (k : UInt32) (len : Nat) : List (Loc × Cell Unit) :=
  [(Loc.global 0, .global { type := answerType, value := .i32 k }), (Loc.memLength 0, .memLength len)]

/-- What the start function leaves in the store. -/
def Answered (cs : List (Loc × Cell Unit)) : Prop :=
  cs = finalCells 20 pageSize ∨ cs = finalCells 0xFFFFFFFF 0

/-- Every run of the start function from `linkedStore` that finishes stores
20 in `answer` with the stack's memory grown to one page, or -1 with memory
still empty; none traps. -/
theorem main_adequate (c : Config Unit) (hc : Exec.startWasm linkedStore {} 7 [] = some c) (fuel : Nat) :
    match Exec.run fuel c with
    | .done vs σ' => vs = [] ∧ ∃ cs, Answered cs ∧ ∀ p ∈ cs, lookup σ' p.1 = some p.2
    | .trap _ _ => False
    | .outOfFuel _ => True := by
  have h := adequacy_cells linkedStore {} 7 [] clientTypes[0]! 1 clientInst mainFunc rfl
    (fun vs => vs = []) False (fun _ => Answered) ?_ c hc fuel
  · revert h
    cases Exec.run fuel c <;> exact id
  intro _
  iintro Hcells
  icases ownCells_take _ mainCells (by decide) mainCells_get $$ Hcells with Hl
  simp only [mainCells]
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hi1, Hl⟩
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hf0, Hl⟩
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hf3, Hl⟩
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hf4, Hl⟩
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hf5, Hl⟩
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hf8, Hl⟩
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hi0, Hl⟩
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hlen, Hl⟩
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Ht, Hl⟩
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Ha, -⟩
  imod pointsTo_persist $$ Hi1 with #Hi1
  imod pointsTo_persist $$ Hf0 with #Hf0
  imod pointsTo_persist $$ Hf3 with #Hf3
  imod pointsTo_persist $$ Hf4 with #Hf4
  imod pointsTo_persist $$ Hf5 with #Hf5
  imod pointsTo_persist $$ Hf8 with #Hf8
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
  · iunfold funcPt; iexact Hf5
  isplitr
  · iunfold funcPt; iexact Hf8
  isplitr
  · iunfold instPt; iexact Hi0
  isplitr
  · iunfold instPt; iexact Hi1
  isplitl [Hlen]
  · iunfold memLength; iexact Hlen
  isplitl [Ht]
  · iunfold tablePt; iexact Ht
  isplitl [Ha]
  · iunfold answerPt; iunfold globalPt; iexact Ha
  iintro %k ⟨Hk, Ha⟩
  isplitr
  · ipureintro; rfl
  icases Hk with (⟨%hk, Hl⟩ | ⟨%hk, Hl⟩)
  · subst hk
    iexists finalCells 20 pageSize
    isplitr
    · ipureintro; exact ⟨.inl rfl, by decide⟩
    iunfold answerPt at Ha
    iunfold globalPt at Ha
    iunfold memLength at Hl
    simp only [finalCells]
    iapply BigSepL.bigSepL_cons.2
    isplitl [Ha]
    · iexact Ha
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hl]
    · iexact Hl
    · iapply BigSepL.bigSepL_nil.2; iempintro
  · subst hk
    iexists finalCells 0xFFFFFFFF 0
    isplitr
    · ipureintro; exact ⟨.inr rfl, by decide⟩
    iunfold answerPt at Ha
    iunfold globalPt at Ha
    iunfold memLength at Hl
    simp only [finalCells]
    iapply BigSepL.bigSepL_cons.2
    isplitl [Ha]
    · iexact Ha
    iapply BigSepL.bigSepL_cons.2
    isplitl [Hl]
    · iexact Hl
    · iapply BigSepL.bigSepL_nil.2; iempintro

/-- The configuration the start function begins in. -/
def mainConfig : Config Unit :=
  let frame : CallFrame :=
    { locals := #[.i32 0], inst := 1, arity := 0, height := 0, labels := [], code := main }
  { store := linkedStore, limits := {}, thread := { stack := #[], frames := [frame] } }

/-- What the linker does with the start function, for any fuel: run `main`
from `linkedStore`. It never traps; when it finishes, `answer` holds 20 and
the stack's memory one page, or `answer` holds -1 and memory is empty. -/
theorem start_adequate (fuel : Nat) :
    match Link.runStart linkedStore {} fuel clientModule clientInst with
    | .ok σ' => ∃ cs, Answered cs ∧ ∀ p ∈ cs, lookup σ' p.1 = some p.2
    | .error e => e = .internal "start function ran out of fuel" := by
  have h := main_adequate mainConfig rfl fuel
  have hstart : Exec.start linkedStore {} 7 [] = .next mainConfig := rfl
  simp only [Link.runStart, clientModule, show clientInst.funcAddrs[7]! = 7 from rfl, Exec.invoke, hstart]
  revert h
  cases Exec.run fuel mainConfig with
  | done vs σ' => exact fun h => h.2
  | trap => exact False.elim
  | outOfFuel => exact fun _ => rfl

/-- **The client, end to end.** For any fuel: validating the stack module,
instantiating it, validating the client, resolving its imports against the
stack's exports and instantiating it (which runs `main` as its start
function) never fails validation or linking and never traps. When `main`
finishes, the client instance is `clientInst`, its global `answer` (store
global 0) holds 20 and the stack's memory one page, or `answer` holds -1 and
memory is empty. -/
theorem client_adequate (fuel : Nat) :
    match (do let vs ← (stackModule.validate (.nearcore true)).toOption
              let (s₁, si) ← (Link.instantiateWith (Store.empty ()) {} [] vs).toOption
              let vc ← (clientModule.validate (.nearcore true)).toOption
              let imports ← (Link.resolve (H := Unit) [("stack", si)] vc.module).toOption
              pure (Link.instantiate s₁ {} vc imports fuel)) with
    | some (.ok (σ', ci)) => ci = clientInst ∧ ∃ cs, Answered cs ∧ ∀ p ∈ cs, lookup σ' p.1 = some p.2
    | some (.error e) => e = .internal "start function ran out of fuel"
    | none => False := by
  have hl := client_links
  revert hl
  cases (stackModule.validate (.nearcore true)).toOption with
  | none => simp
  | some vs =>
  simp only [Option.bind_eq_bind, Option.bind_some]
  cases (Link.instantiateWith (Store.empty ()) {} [] vs).toOption with
  | none => simp
  | some r₁ =>
  obtain ⟨s₁, si⟩ := r₁
  simp only [Option.bind_some]
  cases (clientModule.validate (.nearcore true)).toOption with
  | none => simp
  | some vc =>
  simp only [Option.bind_some]
  cases (Link.resolve (H := Unit) [("stack", si)] vc.module).toOption with
  | none => simp
  | some imports =>
  simp only [Option.bind_some]
  cases hm : Link.instantiateModule s₁ vc imports with
  | error e => simp [Except.toOption]
  | ok r =>
  simp only [Except.toOption, Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq]
  rintro ⟨hvc, rfl⟩
  have h := start_adequate fuel
  simp only [Link.instantiate, hm, bind, Except.bind, Pure.pure, Except.pure, hvc]
  revert h
  cases Link.runStart linkedStore {} fuel clientModule clientInst with
  | ok σ' => exact fun h => ⟨rfl, h⟩
  | error e => exact id

end WasmLogic.Examples.Client
