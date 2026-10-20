-- Ported from Talos GcdStdio/KernelProof.lean at 80644390de3ad4db3055445259a034413ae41577 (AGPL-3.0).
import Programs.GcdStdio.Contracts
import Programs.GcdStdio.KernelProof

/-!
# Total call proof for the optimized `num-integer` kernel

The proof follows the optimized standalone GCD example instruction for
instruction.  Its loop uses the same decreasing sum of the two positive odd
operands, but is stated as a call contract so the stream driver can compose it.
-/

namespace Programs.GcdStdio.CallKernelProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Programs.GcdStdio.Contracts
open scoped Wasm.SmallStep.Outcome

-- Unfold the definitionally equal generic/outcome Iris instances when matching WPs.
set_option backward.isDefEq.respectTransparency false

private abbrev loopBody : Program := Programs.GcdStdio.KernelProof.loopBody
private abbrev innerBody : Program := Programs.GcdStdio.KernelProof.innerBody
private abbrev outerBody : Program := Programs.GcdStdio.KernelProof.gcdOuterBody
private abbrev loopFrame : ControlFrame :=
  Programs.GcdStdio.KernelProof.gcdLoopFrame
private abbrev innerFrame : ControlFrame :=
  Programs.GcdStdio.KernelProof.gcdInnerFrame
private abbrev outerFrame : ControlFrame :=
  Programs.GcdStdio.KernelProof.gcdOuterFrame outerBody

private theorem func1_index :
    Programs.GcdStdio.module.funcs[1]? = some Programs.GcdStdio.func1Def := by
  rfl

local notation "oddPart_toNat" => UInt64.shr_ctz_mod_toNat

private theorem twp_eqzI64
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Phi : ObservableOutcome → HeapIProp}
    {params localValues values : List Value}
    {value : UInt64} {result : UInt32}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hresult : result = if value = 0 then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr Universal.State)
      @ s; E [{ Phi }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 value :: values⟩,
        .eqzI64 :: code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Phi }] :=
  twp_pureStep _ _ _ (fun _ => Step.eqzI64 hresult)

private theorem twp_finishGcd
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Phi : ObservableOutcome → HeapIProp}
    (g gy shared expected : UInt64)
    (hrecombine : g <<< (shared % 64) = expected)
    (K : HeapIProp)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    RuntimeContext ∗ K ∗
      (RuntimeContext -∗ K -∗
        ResumeWP [.i64 expected] callerLocals stack code arity remainder
          controls calls s E Phi) ⊢
    WP (.running
      ⟨⟨[.i64 g, .i64 gy], [.i64 shared], []⟩,
        [.localGet 0, .localGet 2, .shlI64, .localSet 2],
        1, [],
        [Programs.GcdStdio.KernelProof.gcdOuterFrame
          Programs.GcdStdio.KernelProof.gcdOuterBody],
        { locals := { callerLocals with values := stack }
          continuation := code
          resultArity := arity
          callerRemainder := remainder
          control := controls
          returningInstance := ⟨0⟩ } :: calls⟩ : Expr Universal.State)
      @ s; E [{ Phi }] := by
  iintro ⟨Hruntime, HK, Hcont⟩
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_shlI64
  iapply twp_localSet rfl
  iapply twp_exitControl rfl
  simp only [Programs.GcdStdio.KernelProof.gcdOuterFrame,
    Programs.GcdStdio.KernelProof.gcdOuterBody, List.take_nil, List.nil_append]
  iapply twp_localGet rfl
  rw [hrecombine]
  isimp only [RuntimeContext] at Hruntime
  icases Hruntime with ⟨Hmodule, Henv⟩
  iapply twp_returnFromCallFallthrough $$ Hmodule
  iintro Hmodule
  simp only [List.take_succ_cons, List.take_zero, List.cons_append,
    List.nil_append]
  isimp only [ResumeWP, resumeExpr,
    Programs.ProofSupport.StreamMemory.resumeExpr, List.singleton_append] at Hcont
  ihave Hruntime' : RuntimeContext $$ [Hmodule Henv]
  · iunfold RuntimeContext
    iframe Hmodule Henv
  iapply Hcont $$ Hruntime' HK

private theorem twp_gcdLoop
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Phi : ObservableOutcome → HeapIProp}
    (ao bo x y shared expected : UInt64)
    (hxne : x ≠ 0) (hyne : y ≠ 0)
    (hxodd : x.toNat % 2 = 1) (hyodd : y.toNat % 2 = 1)
    (hxyne : x ≠ y)
    (hgcd : Nat.gcd x.toNat y.toNat = Nat.gcd ao.toNat bo.toNat)
    (hrecombine : ∀ g : UInt64,
      g.toNat = Nat.gcd ao.toNat bo.toNat →
      g <<< (shared % 64) = expected)
    (K : HeapIProp)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    RuntimeContext ∗ K ∗
      (RuntimeContext -∗ K -∗
        ResumeWP [.i64 expected] callerLocals stack code arity remainder
          controls calls s E Phi) ⊢
    WP (.running
      ⟨⟨[.i64 x, .i64 y], [.i64 shared], []⟩,
        Programs.GcdStdio.KernelProof.loopBody, 1, [],
        [{ kind := .loop
           paramArity := 0
           resultArity := 0
           body := Programs.GcdStdio.KernelProof.loopBody
           continuation := [.localGet 1, .localSet 0]
           belowStack := [] },
         Programs.GcdStdio.KernelProof.gcdInnerFrame,
         Programs.GcdStdio.KernelProof.gcdOuterFrame
           Programs.GcdStdio.KernelProof.gcdOuterBody],
        { locals := { callerLocals with values := stack }
          continuation := code
          resultArity := arity
          callerRemainder := remainder
          control := controls
          returningInstance := ⟨0⟩ } :: calls⟩ : Expr Universal.State)
      @ s; E [{ Phi }] := by
  induction hmeasure : x.toNat + y.toNat using Nat.strong_induction_on
      generalizing x y with
  | h n ih =>
    subst n
    iintro Hresources
    simp only [Programs.GcdStdio.KernelProof.loopBody]
    iapply twp_block
    iapply twp_localGet rfl
    iapply twp_localGet rfl
    by_cases hgt : y < x
    · iapply twp_gtUI64 (result := 1) (by simp [hgt])
      iapply twp_brIf (by decide) rfl
      simp only [List.take_nil, List.drop_nil, List.nil_append]
      iapply twp_localGet rfl
      iapply twp_localGet rfl
      iapply twp_subI64
      iapply twp_localTee rfl
      iapply twp_localGet rfl
      iapply twp_ctzI64
      iapply twp_shrUI64
      iapply twp_localTee rfl
      simp only [List.set]
      let x' := (x - y) >>> (UInt64.ofNat (ctz64 64 (x - y)) % 64)
      obtain ⟨hx'ne, hx'odd, hgcd', hdec⟩ :=
        UInt64.stein_step_x x y hxne hyne hxodd hyodd hgt
      by_cases hx'y : x' = y
      · change (x - y) >>>
            (UInt64.ofNat (ctz64 64 (x - y)) % 64) = y at hx'y
        iapply twp_localGet rfl
        iapply twp_neI64 (result := 0) (by simp [hx'y])
        iapply twp_brIfZero
        iapply twp_exitControl rfl
        simp only [List.take_nil, List.nil_append]
        iapply twp_localGet rfl
        iapply twp_localSet rfl
        simp only [List.set]
        iapply twp_exitControl rfl
        simp only [Programs.GcdStdio.KernelProof.gcdInnerFrame,
          List.take_nil, List.nil_append]
        have hh :
            (x - y).toNat >>> (ctz64 64 (x - y) % 64) = y.toNat := by
          rw [← oddPart_toNat, hx'y]
        have hyGcd : y.toNat = Nat.gcd ao.toNat bo.toNat := by
          rw [← hgcd, ← hgcd', hh, Nat.gcd_self]
        iapply twp_finishGcd y y shared expected (hrecombine y hyGcd)
          K callerLocals stack code arity remainder controls calls
        iexact Hresources
      · change (x - y) >>>
            (UInt64.ofNat (ctz64 64 (x - y)) % 64) ≠ y at hx'y
        iapply twp_localGet rfl
        iapply twp_neI64 (result := 1) (by simp [hx'y])
        iapply twp_brIf (by decide) rfl
        simp only [List.take_nil, List.nil_append]
        have hdecrease : x'.toNat + y.toNat < x.toNat + y.toNat := by
          simpa [x', oddPart_toNat] using hdec
        have Hnext := ih (x'.toNat + y.toNat) hdecrease x' y hx'ne hyne
          (by simpa [x', oddPart_toNat] using hx'odd) hyodd hx'y
          (by simpa [x', oddPart_toNat] using hgcd'.trans hgcd) rfl
        simp only [x', Programs.GcdStdio.KernelProof.loopBody] at Hnext
        iapply Hnext
        iexact Hresources
    · iapply twp_gtUI64 (result := 0) (by simp [hgt])
      iapply twp_brIfZero
      iapply twp_localGet rfl
      iapply twp_localGet rfl
      iapply twp_localGet rfl
      iapply twp_subI64
      iapply twp_localTee rfl
      iapply twp_localGet rfl
      iapply twp_ctzI64
      iapply twp_shrUI64
      iapply twp_localTee rfl
      simp only [List.set]
      let y' := (y - x) >>> (UInt64.ofNat (ctz64 64 (y - x)) % 64)
      obtain ⟨hy'ne, hy'odd, hgcd', hdec⟩ :=
        UInt64.stein_step_y x y hxne hyne hxodd hyodd hgt hxyne
      by_cases hxy' : x = y'
      · change x = (y - x) >>>
            (UInt64.ofNat (ctz64 64 (y - x)) % 64) at hxy'
        iapply twp_eqI64 (result := 1) (by rw [ite_eq_left hxy'])
        iapply twp_brIf (by decide) rfl
        simp only [Programs.GcdStdio.KernelProof.gcdInnerFrame,
          List.take_nil, List.nil_append]
        rw [← hxy']
        have hh :
            (y - x).toNat >>> (ctz64 64 (y - x) % 64) = x.toNat := by
          rw [← oddPart_toNat, ← hxy']
        have hxGcd : x.toNat = Nat.gcd ao.toNat bo.toNat := by
          rw [← hgcd, ← hgcd', hh, Nat.gcd_self]
        iapply twp_finishGcd x x shared expected (hrecombine x hxGcd)
          K callerLocals stack code arity remainder controls calls
        iexact Hresources
      · change x ≠ (y - x) >>>
            (UInt64.ofNat (ctz64 64 (y - x)) % 64) at hxy'
        iapply twp_eqI64 (result := 0) (by rw [ite_eq_right hxy'])
        iapply twp_brIfZero
        iapply twp_br rfl
        simp only [List.take_nil, List.nil_append]
        have hdecrease : x.toNat + y'.toNat < x.toNat + y.toNat := by
          simpa [y', oddPart_toNat] using hdec
        have Hnext := ih (x.toNat + y'.toNat) hdecrease x y' hxne hy'ne
          hxodd (by simpa [y', oddPart_toNat] using hy'odd) hxy'
          (by simpa [y', oddPart_toNat] using hgcd'.trans hgcd) rfl
        simp only [y', Programs.GcdStdio.KernelProof.loopBody] at Hnext
        iapply Hnext
        iexact Hresources

private theorem twp_gcdInner
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Phi : ObservableOutcome → HeapIProp}
    (p0 p1 shared expected : UInt64)
    (hp0 : p0 ≠ 0) (hp1 : p1 ≠ 0)
    (hrecombine : ∀ g : UInt64,
      g.toNat = Nat.gcd
        (p0 >>> (UInt64.ofNat (ctz64 64 p0) % 64)).toNat
        (p1 >>> (UInt64.ofNat (ctz64 64 p1) % 64)).toNat →
      g <<< (shared % 64) = expected)
    (K : HeapIProp)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    RuntimeContext ∗ K ∗
      (RuntimeContext -∗ K -∗
        ResumeWP [.i64 expected] callerLocals stack code arity remainder
          controls calls s E Phi) ⊢
    WP (.running
      ⟨⟨[.i64 p0, .i64 p1], [.i64 shared], []⟩,
        Programs.GcdStdio.KernelProof.innerBody, 1, [],
        [Programs.GcdStdio.KernelProof.gcdInnerFrame,
         Programs.GcdStdio.KernelProof.gcdOuterFrame
           Programs.GcdStdio.KernelProof.gcdOuterBody],
        { locals := { callerLocals with values := stack }
          continuation := code
          resultArity := arity
          callerRemainder := remainder
          control := controls
          returningInstance := ⟨0⟩ } :: calls⟩ : Expr Universal.State)
      @ s; E [{ Phi }] := by
  iintro Hresources
  simp only [Programs.GcdStdio.KernelProof.innerBody]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_ctzI64
  iapply twp_shrUI64
  iapply twp_localTee rfl
  simp only [List.set]
  let ao := p0 >>> (UInt64.ofNat (ctz64 64 p0) % 64)
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_ctzI64
  iapply twp_shrUI64
  iapply twp_localTee rfl
  simp only [List.set]
  let bo := p1 >>> (UInt64.ofNat (ctz64 64 p1) % 64)
  have haone : ao ≠ 0 := UInt64.shr_ctz_ne_zero p0 hp0
  have hbone : bo ≠ 0 := UInt64.shr_ctz_ne_zero p1 hp1
  have haodd : ao.toNat % 2 = 1 := by
    simpa [ao, oddPart_toNat] using UInt64.shr_ctz_toNat_odd p0 hp0
  have hbodd : bo.toNat % 2 = 1 := by
    simpa [bo, oddPart_toNat] using UInt64.shr_ctz_toNat_odd p1 hp1
  by_cases hab : ao = bo
  · iapply twp_eqI64 (result := 1) (by rw [ite_eq_left hab])
    iapply twp_brIf (by decide) rfl
    simp only [Programs.GcdStdio.KernelProof.gcdInnerFrame,
      List.take_nil, List.nil_append]
    have haoGcd : ao.toNat = Nat.gcd ao.toNat bo.toNat := by
      rw [← hab, Nat.gcd_self]
    iapply twp_finishGcd ao bo shared expected (hrecombine ao haoGcd)
      K callerLocals stack code arity remainder controls calls
    iexact Hresources
  · iapply twp_eqI64 (result := 0) (by rw [ite_eq_right hab])
    iapply twp_brIfZero
    iapply twp_loop
    simp only [List.drop_nil]
    rw [show
      ({ kind := .loop
         paramArity := 0
         resultArity := 0
         body := loopBody
         continuation := [.localGet 1, .localSet 0]
         belowStack := [] } : ControlFrame) = loopFrame from rfl]
    have Hloop := twp_gcdLoop (hlc := hlc) (s := s) (E := E)
      (Phi := Phi) ao bo ao bo shared expected
      haone hbone haodd hbodd hab rfl hrecombine
      K callerLocals stack code arity remainder controls calls
    simp only [ao, bo] at Hloop
    simp only [loopFrame, Programs.GcdStdio.KernelProof.gcdLoopFrame]
    iapply Hloop
    iexact Hresources

private theorem twp_func1_body
    [WasmSmallStepGS hlc Universal.State]
    {s : Stuckness} {E : CoPset}
    {Phi : ObservableOutcome → HeapIProp}
    (a b : UInt64) (K : HeapIProp)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame) :
    RuntimeContext ∗ K ∗
      (RuntimeContext -∗ K -∗
        ResumeWP [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))]
          callerLocals stack code arity remainder controls calls s E Phi) ⊢
    WP (.running
      ⟨⟨[.i64 a, .i64 b], [ValueType.i64.zero], []⟩,
        Programs.GcdStdio.func1, 1, [], [],
        { locals := { callerLocals with values := stack }
          continuation := code
          resultArity := arity
          callerRemainder := remainder
          control := controls
          returningInstance := ⟨0⟩ } :: calls⟩ : Expr Universal.State)
      @ s; E [{ Phi }] := by
  iintro Hresources
  rw [show Programs.GcdStdio.func1 =
    [.localGet 1, .localGet 0, .orI64, .localSet 2,
      .block 0 0 outerBody, .localGet 2] from rfl]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_orI64
  iapply twp_localSet rfl
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  iapply twp_block
  simp only [outerBody, Programs.GcdStdio.KernelProof.gcdOuterBody,
    List.drop_nil]
  iapply twp_localGet rfl
  by_cases ha : a = 0
  · subst a
    iapply twp_eqzI64 (result := 1) (by decide)
    iapply twp_brIf (by decide) rfl
    simp only [List.take_nil, List.nil_append]
    iapply twp_localGet rfl
    rw [show b ||| (0 : UInt64) =
      UInt64.ofNat (Nat.gcd (0 : UInt64).toNat b.toNat) by simp]
    isimp only [RuntimeContext] at Hresources
    icases Hresources with ⟨⟨Hmodule, Henv⟩, HK, Hcont⟩
    iapply twp_returnFromCallFallthrough $$ Hmodule
    iintro Hmodule
    simp only [List.take_succ_cons, List.take_zero, List.cons_append,
      List.nil_append]
    isimp only [ResumeWP, resumeExpr,
      Programs.ProofSupport.StreamMemory.resumeExpr, List.singleton_append] at Hcont
    ihave Hruntime' : RuntimeContext $$ [Hmodule Henv]
    · iunfold RuntimeContext
      isplitl [Hmodule]
      · iexact Hmodule
      · iexact Henv
    isimp only [RuntimeContext] at Hruntime'
    iapply Hcont $$ Hruntime' HK
  · iapply twp_eqzI64 (result := 0) (by rw [ite_eq_right ha])
    iapply twp_brIfZero
    iapply twp_localGet rfl
    by_cases hb : b = 0
    · subst b
      iapply twp_eqzI64 (result := 1) (by decide)
      iapply twp_brIf (by decide) rfl
      simp only [List.take_nil, List.nil_append]
      iapply twp_localGet rfl
      rw [show (0 : UInt64) ||| a =
        UInt64.ofNat (Nat.gcd a.toNat (0 : UInt64).toNat) by simp]
      isimp only [RuntimeContext] at Hresources
      icases Hresources with ⟨⟨Hmodule, Henv⟩, HK, Hcont⟩
      iapply twp_returnFromCallFallthrough $$ Hmodule
      iintro Hmodule
      simp only [List.take_succ_cons, List.take_zero, List.cons_append,
        List.nil_append]
      isimp only [ResumeWP, resumeExpr,
        Programs.ProofSupport.StreamMemory.resumeExpr, List.singleton_append] at Hcont
      ihave Hruntime' : RuntimeContext $$ [Hmodule Henv]
      · iunfold RuntimeContext
        isplitl [Hmodule]
        · iexact Hmodule
        · iexact Henv
      isimp only [RuntimeContext] at Hruntime'
      iapply Hcont $$ Hruntime' HK
    · iapply twp_eqzI64 (result := 0) (by rw [ite_eq_right hb])
      iapply twp_brIfZero
      iapply twp_localGet rfl
      iapply twp_ctzI64
      iapply twp_localSet rfl
      simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
        Nat.reduceSub, List.set]
      iapply twp_block
      simp only [List.drop_nil]
      have Hinner := twp_gcdInner (hlc := hlc) (s := s) (E := E)
        (Phi := Phi) a b
        (UInt64.ofNat (ctz64 64 (b ||| a)))
        (UInt64.ofNat (Nat.gcd a.toNat b.toNat)) ha hb (by
          intro g hg
          apply UInt64.recombine_loop a b g ha hb
          rw [Nat.gcd_self, hg]
          rw [oddPart_toNat, oddPart_toNat])
        K callerLocals stack code arity remainder controls calls
      simp only [Programs.GcdStdio.KernelProof.gcdInnerFrame,
        Programs.GcdStdio.KernelProof.gcdOuterFrame,
        Programs.GcdStdio.KernelProof.gcdOuterBody] at Hinner
      iapply Hinner
      iexact Hresources

theorem func1_correct [WasmSmallStepGS hlc Universal.State] :
    Func1Spec (hlc := hlc) := by
  unfold Func1Spec CallContract callExpr
  intro a b callerLocals stack code arity remainder controls calls s E Phi
  iintro ⟨Hruntime, Hcont⟩
  isimp only [RuntimeContext] at Hruntime
  icases Hruntime with ⟨Hmodule, Henv⟩
  simp only [Programs.ProofSupport.StreamMemory.callExpr]
  iapply twp_call Programs.GcdStdio.module 4 Programs.GcdStdio.func1Def
      (by decide) func1_index $$ Hmodule
  iintro Hmodule
  simp [Programs.GcdStdio.func1Def, Function.toLocals, Function.numParams]
  ihave Hruntime' : RuntimeContext $$ [Hmodule Henv]
  · iunfold RuntimeContext
    iframe Hmodule Henv
  isimp only [KernelContinuation] at Hcont
  iapply twp_func1_body a b (iprop(True)) callerLocals stack code arity
    remainder controls calls
  isplitl [Hruntime']
  · iexact Hruntime'
  isplitl []
  · itrivial
  iintro Hruntime _Htrue
  iapply Hcont $$ Hruntime

end Programs.GcdStdio.CallKernelProof
