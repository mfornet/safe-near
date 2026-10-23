import WasmLogic.Examples.Stack.Instance
import WasmLogic.Examples.Probe.Code

/-!
# The probe, end to end

As for the client (`../Client/Main.lean`): the stack and the probe are
linked by the runtime's linker (`probe_links`), `main` is proved from the
stack's function specifications (`main_spec`), and `probe_adequate` says
what instantiating the probe, which runs `main`, does for any fuel: it never
traps, and `answer` ends 1001 with one page of memory, or -1 with none.
-/

namespace WasmLogic.Examples.Probe

open Wasm Iris Iris.BI Iris.ProgramLogic WasmLogic WasmLogic.Examples.Stack

/-! ## Linking -/

def probeInst : ModuleInst :=
  { types := probeTypes, funcAddrs := #[0, 1, 2, 4, 6, 7], globalAddrs := #[0],
    exports := #[("answer", .global 0)] }

def linkedStore : Store Unit :=
  { funcs := #[
      .wasm stackTypes[0]! 0 newStackFn,
      .wasm stackTypes[1]! 0 isEmptyFn,
      .wasm stackTypes[1]! 0 isFullFn,
      .wasm stackTypes[1]! 0 popFn,
      .wasm stackTypes[2]! 0 pushFn,
      .wasm stackTypes[2]! 0 mapFn,
      .wasm stackTypes[1]! 0 lengthFn,
      .wasm probeTypes[0]! 1 mainFunc],
    tables := #[{ elemType := .funcref, elems := #[.null .funcref], max := none }],
    mems := #[{ pages := #[], max := none }],
    globals := #[{ type := answerType, value := .i32 0 }],
    modules := #[stackInst, probeInst],
    host := () }

theorem probe_links :
    (do let vs ← (stackModule.validate (.nearcore true)).toOption
        let (s₁, si) ← (Link.instantiateWith (Store.empty ()) {} [] vs).toOption
        let vp ← (probeModule.validate (.nearcore true)).toOption
        let imports ← (Link.resolve (H := Unit) [("stack", si)] vp.module).toOption
        let r ← (Link.instantiateModule s₁ vp imports).toOption
        pure (vp.module, r)) = some (probeModule, linkedStore, probeInst) := by
  kernel_rfl

/-! ## The probe's proof -/

section Proof

variable {H : Type} {GF : BundledGFunctors} [WasmGS H GF] {lim : ExecLimits}

abbrev answerPt (k : UInt32) : IProp GF := (0 : Nat) ↦[wg] { type := answerType, value := .i32 k }

/-- `main`, from the stack's specifications: `answer` ends 1001 and memory
has grown by a page, or -1 and memory is as it was. -/
theorem main_spec (hlim : 1 < lim.maxCallDepth) (Φf : FunPost GF) :
    (0 : Nat) ↪[wf] FuncInst.wasm (H := H) stackTypes[0]! 0 newStackFn ∗
      (1 : Nat) ↪[wf] FuncInst.wasm (H := H) stackTypes[1]! 0 isEmptyFn ∗
      (2 : Nat) ↪[wf] FuncInst.wasm (H := H) stackTypes[1]! 0 isFullFn ∗
      (4 : Nat) ↪[wf] FuncInst.wasm (H := H) stackTypes[2]! 0 pushFn ∗
      (6 : Nat) ↪[wf] FuncInst.wasm (H := H) stackTypes[1]! 0 lengthFn ∗
      (0 : Nat) ↪[inst] stackInst ∗ (0 : Nat) ↦[wmlength] 0 ∗ answerPt 0 ∗
      (∀ k : UInt32, ((⌜k = 1001⌝ ∗ (0 : Nat) ↦[wmlength] pageSize) ∨
          (⌜k = 0xFFFFFFFF⌝ ∗ (0 : Nat) ↦[wmlength] 0)) ∗ answerPt k -∗ Φf.ret [])
      ⊢ wpInvoke (H := H) lim 0 probeTypes[0]! 1 probeInst mainFunc [] Φf := by
  iintro ⟨#H0, #H1, #H2, #H4, #H6, #Hsi, Hlen, Ha, HΦ⟩
  iapply wpInvoke_intro
  rw [show mainFunc.body = main from rfl, show entryLocals mainFunc [] = #[.i32 0] from rfl,
    show probeTypes[0]!.results.length = 0 from rfl]
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
  · subst hvs
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
  · subst hvs
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
    -- is_empty on the empty stack: 1
    wp_step 0 wpi_local_get 0 (u32 0) rfl
    inext; simp only [Post.seq_normal]
    wp_step 1 wpi_call 1 1 stackTypes[1]! 0 stackInst isEmptyFn [] [u32 0] rfl rfl (by omega)
    isplitr
    · iexact H1
    isplitr
    · iexact Hsi
    inext
    iapply invoke_is_empty 1 0 []
    isplitl [Hs]
    · iexact Hs
    iintro %e₀ %he₀ Hs
    obtain rfl : e₀ = 1 := by rcases he₀ with ⟨h, -⟩ | ⟨-, h⟩ <;> first | exact h | exact absurd rfl h
    simp only [Post.seq_normal, List.nil_append]
    -- push 4
    wp_step 0 wpi_local_get 0 (u32 0) rfl
    inext; simp only [Post.seq_normal]
    wp_step 0 wpi_i32_const 4
    inext; simp only [Post.seq_normal]
    wp_step 2 wpi_call 3 4 stackTypes[2]! 0 stackInst pushFn [u32 1] [u32 0, .i32 4] rfl rfl (by omega)
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
    -- is_empty on [4]: 0
    wp_step 0 wpi_local_get 0 (u32 0) rfl
    inext; simp only [Post.seq_normal]
    wp_step 1 wpi_call 1 1 stackTypes[1]! 0 stackInst isEmptyFn [u32 1] [u32 0] rfl rfl (by omega)
    isplitr
    · iexact H1
    isplitr
    · iexact Hsi
    inext
    iapply invoke_is_empty 1 0 [4]
    isplitl [Hs]
    · iexact Hs
    iintro %e₁ %he₁ Hs
    obtain rfl : e₁ = 0 := by rcases he₁ with ⟨-, h⟩ | ⟨h, -⟩ <;> first | exact h | cases h
    simp only [Post.seq_normal]
    wp_step 0 wpi_i32_const 10
    inext; simp only [Post.seq_normal]
    wp_step 2 wpi_i32_binop .mul (UInt32.ofNat 0) 10 0 rfl
    inext; simp only [Post.seq_normal]
    wp_step 2 wpi_i32_binop .add (UInt32.ofNat 1) 0 1 rfl
    inext; simp only [Post.seq_normal]
    -- is_full on [4]: 0
    wp_step 0 wpi_local_get 0 (u32 0) rfl
    inext; simp only [Post.seq_normal]
    wp_step 1 wpi_call 2 2 stackTypes[1]! 0 stackInst isFullFn [.i32 1] [u32 0] rfl rfl (by omega)
    isplitr
    · iexact H2
    isplitr
    · iexact Hsi
    inext
    iapply invoke_is_full 1 0 [4]
    isplitl [Hs]
    · iexact Hs
    iintro %f₀ %hf₀ Hs
    obtain rfl : f₀ = 0 := by rcases hf₀ with ⟨-, h⟩ | ⟨h, -⟩ <;> first | exact h | simp [two14] at h
    simp only [Post.seq_normal]
    wp_step 0 wpi_i32_const 100
    inext; simp only [Post.seq_normal]
    wp_step 2 wpi_i32_binop .mul (UInt32.ofNat 0) 100 0 rfl
    inext; simp only [Post.seq_normal]
    wp_step 2 wpi_i32_binop .add 1 0 1 rfl
    inext; simp only [Post.seq_normal]
    -- stack_length of [4]: 1
    wp_step 0 wpi_local_get 0 (u32 0) rfl
    inext; simp only [Post.seq_normal]
    wp_step 1 wpi_call 4 6 stackTypes[1]! 0 stackInst lengthFn [.i32 1] [u32 0] rfl rfl (by omega)
    isplitr
    · iexact H6
    isplitr
    · iexact Hsi
    inext
    iapply invoke_stack_length 1 0 [4]
    isplitl [Hs]
    · iexact Hs
    iintro -
    simp only [Post.seq_normal, List.length_singleton]
    wp_step 0 wpi_i32_const 1000
    inext; simp only [Post.seq_normal]
    wp_step 2 wpi_i32_binop .mul (UInt32.ofNat 1) 1000 1000 rfl
    inext; simp only [Post.seq_normal]
    wp_step 2 wpi_i32_binop .add 1 1000 1001 rfl
    inext; simp only [Post.seq_normal]
    wp_step 1 wpi_global_set 0 0 { type := answerType, value := .i32 0 } (.i32 1001) rfl
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

def mainCells : List (Loc × Cell Unit) :=
  [(Loc.inst 1, .inst probeInst), (Loc.func 0, .func (.wasm stackTypes[0]! 0 newStackFn)),
    (Loc.func 1, .func (.wasm stackTypes[1]! 0 isEmptyFn)), (Loc.func 2, .func (.wasm stackTypes[1]! 0 isFullFn)),
    (Loc.func 4, .func (.wasm stackTypes[2]! 0 pushFn)), (Loc.func 6, .func (.wasm stackTypes[1]! 0 lengthFn)),
    (Loc.inst 0, .inst stackInst), (Loc.memLength 0, .memLength 0),
    (Loc.global 0, .global { type := answerType, value := .i32 0 })]

theorem mainCells_get : ∀ p ∈ mainCells, Iris.Std.get? (heapOf linkedStore) p.1 = some p.2 := by
  intro p hp
  simp only [mainCells, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rw [get?_heapOf]
  all_goals first | rfl | simp [linkedStore, Memory.wf, Memory.byteSize]

def finalCells (k : UInt32) (len : Nat) : List (Loc × Cell Unit) :=
  [(Loc.global 0, .global { type := answerType, value := .i32 k }), (Loc.memLength 0, .memLength len)]

def Answered (cs : List (Loc × Cell Unit)) : Prop :=
  cs = finalCells 1001 pageSize ∨ cs = finalCells 0xFFFFFFFF 0

theorem main_adequate (c : Config Unit) (hc : Exec.startWasm linkedStore {} 7 [] = some c) (fuel : Nat) :
    match Exec.run fuel c with
    | .done vs σ' => vs = [] ∧ ∃ cs, Answered cs ∧ ∀ p ∈ cs, lookup σ' p.1 = some p.2
    | .trap _ _ => False
    | .outOfFuel _ => True := by
  have h := adequacy_cells linkedStore {} 7 [] probeTypes[0]! 1 probeInst mainFunc rfl
    (fun vs => vs = []) False (fun _ => Answered) ?_ c hc fuel
  · revert h
    cases Exec.run fuel c <;> exact id
  intro _
  iintro Hcells
  icases ownCells_take _ mainCells (by decide) mainCells_get $$ Hcells with Hl
  simp only [mainCells]
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hi1, Hl⟩
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hf0, Hl⟩
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hf1, Hl⟩
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hf2, Hl⟩
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hf4, Hl⟩
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hf6, Hl⟩
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hi0, Hl⟩
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Hlen, Hl⟩
  icases BigSepL.bigSepL_cons.1 $$ Hl with ⟨Ha, -⟩
  imod pointsTo_persist $$ Hi1 with #Hi1
  imod pointsTo_persist $$ Hf0 with #Hf0
  imod pointsTo_persist $$ Hf1 with #Hf1
  imod pointsTo_persist $$ Hf2 with #Hf2
  imod pointsTo_persist $$ Hf4 with #Hf4
  imod pointsTo_persist $$ Hf6 with #Hf6
  imod pointsTo_persist $$ Hi0 with #Hi0
  imodintro
  isplitr
  · iunfold instPt; iexact Hi1
  iapply main_spec (by decide)
  isplitr
  · iunfold funcPt; iexact Hf0
  isplitr
  · iunfold funcPt; iexact Hf1
  isplitr
  · iunfold funcPt; iexact Hf2
  isplitr
  · iunfold funcPt; iexact Hf4
  isplitr
  · iunfold funcPt; iexact Hf6
  isplitr
  · iunfold instPt; iexact Hi0
  isplitl [Hlen]
  · iunfold memLength; iexact Hlen
  isplitl [Ha]
  · iunfold answerPt; iunfold globalPt; iexact Ha
  iintro %k ⟨Hk, Ha⟩
  isplitr
  · ipureintro; rfl
  icases Hk with (⟨%hk, Hl⟩ | ⟨%hk, Hl⟩)
  · subst hk
    iexists finalCells 1001 pageSize
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

def mainConfig : Config Unit :=
  let frame : CallFrame :=
    { locals := #[.i32 0], inst := 1, arity := 0, height := 0, labels := [], code := main }
  { store := linkedStore, limits := {}, thread := { stack := #[], frames := [frame] } }

theorem start_adequate (fuel : Nat) :
    match Link.runStart linkedStore {} fuel probeModule probeInst with
    | .ok σ' => ∃ cs, Answered cs ∧ ∀ p ∈ cs, lookup σ' p.1 = some p.2
    | .error e => e = .internal "start function ran out of fuel" := by
  have h := main_adequate mainConfig rfl fuel
  have hstart : Exec.start linkedStore {} 7 [] = .next mainConfig := rfl
  simp only [Link.runStart, probeModule, show probeInst.funcAddrs[5]! = 7 from rfl, Exec.invoke, hstart]
  revert h
  cases Exec.run fuel mainConfig with
  | done vs σ' => exact fun h => h.2
  | trap => exact False.elim
  | outOfFuel => exact fun _ => rfl

/-- **The probe, end to end.** For any fuel, validating and instantiating
the stack, then the probe against it (which runs `main`), never fails and
never traps; when `main` finishes, `answer` holds 1001 (`is_empty` was 1
then 0, `is_full` 0, `stack_length` 1) and the stack's memory one page, or
`answer` holds -1 and memory is empty. -/
theorem probe_adequate (fuel : Nat) :
    match (do let vs ← (stackModule.validate (.nearcore true)).toOption
              let (s₁, si) ← (Link.instantiateWith (Store.empty ()) {} [] vs).toOption
              let vp ← (probeModule.validate (.nearcore true)).toOption
              let imports ← (Link.resolve (H := Unit) [("stack", si)] vp.module).toOption
              pure (Link.instantiate s₁ {} vp imports fuel)) with
    | some (.ok (σ', pi)) => pi = probeInst ∧ ∃ cs, Answered cs ∧ ∀ p ∈ cs, lookup σ' p.1 = some p.2
    | some (.error e) => e = .internal "start function ran out of fuel"
    | none => False := by
  have hl := probe_links
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
  cases (probeModule.validate (.nearcore true)).toOption with
  | none => simp
  | some vp =>
  simp only [Option.bind_some]
  cases (Link.resolve (H := Unit) [("stack", si)] vp.module).toOption with
  | none => simp
  | some imports =>
  simp only [Option.bind_some]
  cases hm : Link.instantiateModule s₁ vp imports with
  | error e => simp [Except.toOption]
  | ok r =>
  simp only [Except.toOption, Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq]
  rintro ⟨hvp, rfl⟩
  have h := start_adequate fuel
  simp only [Link.instantiate, hm, bind, Except.bind, Pure.pure, Except.pure, hvp]
  revert h
  cases Link.runStart linkedStore {} fuel probeModule probeInst with
  | ok σ' => exact fun h => ⟨rfl, h⟩
  | error e => exact id

end WasmLogic.Examples.Probe
