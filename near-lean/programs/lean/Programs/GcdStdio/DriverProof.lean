-- Ported from Talos GcdStdio/DriverProof.lean at 80644390de3ad4db3055445259a034413ae41577 (AGPL-3.0).
import Programs.GcdStdio.HostProof

set_option maxRecDepth 8388608
set_option maxHeartbeats 0

/-!
# Proof of the GCD stream-driver suffix

The generated allocator is discharged by the concrete checked prefix in
`Adequacy.lean`.  This file starts immediately after that prefix, at the first
read-shim instruction, and proves the rest of the driver with total Iris WP.
-/

namespace Programs.GcdStdio.DriverProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Programs.GcdStdio.Contracts
open scoped Wasm.SmallStep.Outcome

-- Unfold the definitionally equal generic/outcome Iris instances when matching WPs.
set_option backward.isDefEq.respectTransparency false

private abbrev HeapIProp := IProp (WasmHeapGF Universal.State)

def successBody : Program :=
  [.localGet 1, .const 16, .call 10, .const 16, .ne, .br_if 0,
    .localGet 0, .localGet 1, .load64 0,
    .localGet 1, .load64 8, .call 4, .store64 8,
    .localGet 0, .const 8, .add, .const 8, .call 11,
    .localGet 1, .const 16, .const 1, .call 8, .br 1]

def fallbackBody : Program :=
  [.localGet 1, .const 16, .const 1, .call 8]

def restoreBody : Program :=
  [.localGet 0, .const 16, .add, .globalSet 0, .ret]

def oomBody : Program :=
  [.const 1, .const 16, .call 17, .unreachable]

def middleBody : Program :=
  [.block 0 0 successBody] ++ fallbackBody

def outerBody : Program :=
  [.const 16, .const 1, .call 9, .localTee 1, .eqz, .br_if 0,
    .block 0 0 middleBody] ++ restoreBody

def innerFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := successBody
    continuation := fallbackBody
    belowStack := [] }

def middleFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := middleBody
    continuation := restoreBody
    belowStack := [] }

def outerFrame : ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := outerBody
    continuation := oomBody
    belowStack := [] }

def wrapperFrame : CallFrame :=
  { locals := {}
    continuation := []
    resultArity := 0
    callerRemainder := []
    control := []
    returningInstance := ⟨0⟩ }

def afterAllocExpr : Expr Universal.State := .running
  { locals := ⟨[], [.i32 entryStackLow, .i32 heapBase], []⟩
    code := successBody
    resultArity := 0
    callerRemainder := []
    control := [innerFrame, middleFrame, outerFrame]
    calls := [wrapperFrame] }

private theorem encodeWord_eq_u64Bytes (x : UInt64) :
    Wasm.Examples.SelectionSort.StdIO.encodeWord x =
      [u64Byte x 0, u64Byte x 1, u64Byte x 2, u64Byte x 3,
       u64Byte x 4, u64Byte x 5, u64Byte x 6, u64Byte x 7] := by
  have hall (y : UInt8) : y &&& 255 = y := by bv_normalize
  simp [Wasm.Examples.SelectionSort.StdIO.encodeWord, u64Byte, hall]

private theorem pointsTo_u64_as_bytes [WasmHeapGS α]
    (memId : Nat) (addr : UInt32) (value : UInt64) :
    pointsTo_u64 memId addr value ⊣⊢ pointsToBytes memId addr
      [u64Byte value 0, u64Byte value 1, u64Byte value 2,
       u64Byte value 3, u64Byte value 4, u64Byte value 5,
       u64Byte value 6, u64Byte value 7] := by
  have e2 : addr + 1 + 1 = addr + 2 := by bv_normalize
  have e3 : addr + 2 + 1 = addr + 3 := by bv_normalize
  have e4 : addr + 3 + 1 = addr + 4 := by bv_normalize
  have e5 : addr + 4 + 1 = addr + 5 := by bv_normalize
  have e6 : addr + 5 + 1 = addr + 6 := by bv_normalize
  have e7 : addr + 6 + 1 = addr + 7 := by bv_normalize
  simp only [pointsTo_u64, pointsToBytes, e2, e3, e4, e5, e6, e7,
    (BI.sep_emp (PROP := IProp (WasmHeapGF α))).to_eq]
  exact .rfl

private theorem ByteSlice_word [WasmHeapGS Universal.State]
    (ptr : UInt32) (value : UInt64)
    (hnowrap : ptr.toNat + 8 < UInt32.size) :
    Programs.GcdStdio.Contracts.ByteSlice ptr
        (Programs.GcdStdio.Spec.codec.encode value) ⊣⊢
      pointsTo_u64 0 ptr value := by
  unfold Programs.GcdStdio.Contracts.ByteSlice
    Programs.ProofSupport.StreamMemory.ByteSlice
  rw [show Programs.GcdStdio.Spec.codec.encode value =
      Wasm.Examples.SelectionSort.StdIO.encodeWord value by rfl,
    encodeWord_eq_u64Bytes value]
  constructor
  · iintro ⟨%_, Hbytes⟩
    iapply (pointsTo_u64_as_bytes 0 ptr value).mpr
    iexact Hbytes
  · iintro Hword
    isplitl []
    · ipureintro
      simpa only [List.length_cons, List.length_nil, Nat.reduceAdd] using
        hnowrap
    · iapply (pointsTo_u64_as_bytes 0 ptr value).mp
      iexact Hword

private theorem ByteSlice_input_words [WasmHeapGS Universal.State]
    (a b : UInt64) :
    Programs.GcdStdio.Contracts.ByteSlice heapBase
        (Programs.GcdStdio.Spec.encodeInput a b) ⊢
      iprop(pointsTo_u64 0 heapBase a ∗
        pointsTo_u64 0 (heapBase + 8) b) := by
  rw [show Programs.GcdStdio.Spec.encodeInput a b =
    Programs.GcdStdio.Spec.codec.encode a ++
      Programs.GcdStdio.Spec.codec.encode b by rfl]
  iintro Hslice
  isimp only [Programs.GcdStdio.Contracts.ByteSlice] at Hslice
  icases (Programs.ProofSupport.StreamMemory.ByteSlice_append
      heapBase (Programs.GcdStdio.Spec.codec.encode a)
        (Programs.GcdStdio.Spec.codec.encode b)).mp $$ Hslice with
    ⟨Ha, Hb⟩
  isimp only [Programs.ProofSupport.StreamMemory.ByteSlice] at Ha
  icases Ha with ⟨%ha, Habytes⟩
  isimp only [Programs.ProofSupport.StreamMemory.ByteSlice] at Hb
  icases Hb with ⟨%hb, Hbbytes⟩
  isimp only [Programs.GcdStdio.Spec.codec,
    Wasm.Examples.SelectionSort.StdIO.codec] at Habytes Hbbytes
  isimp only [encodeWord_eq_u64Bytes a] at Habytes Hbbytes
  isimp only [encodeWord_eq_u64Bytes b] at Hbbytes
  isplitl [Habytes]
  · iapply (pointsTo_u64_as_bytes 0 heapBase a).mpr
    iexact Habytes
  · iapply (pointsTo_u64_as_bytes 0 (heapBase + 8) b).mpr
    iexact Hbbytes

private theorem func5_index :
    Programs.GcdStdio.module.funcs[5]? = some Programs.GcdStdio.func5Def := by
  rfl

/-- Total correctness of the suffix beginning immediately after the checked
allocator prefix. -/
theorem twp_afterAlloc
    [WasmSmallStepGS hlc Universal.State]
    (a b : UInt64) {s : Stuckness} {E : CoPset}
    {Phi : ObservableOutcome → HeapIProp} :
    iprop(
      RuntimeContext ∗
      StackPointer entryStackLow ∗
      Programs.GcdStdio.Contracts.ByteSlice entryStackLow
        (List.replicate 16 0) ∗
      pointsTo_u32 0 allocatorCursor allocatedFinish ∗
      Programs.GcdStdio.Contracts.ByteSlice heapBase
        (List.replicate 16 0) ∗
      Streams (Programs.GcdStdio.Spec.encodeInput a b) [] false ∗
      (RuntimeContext -∗
        Streams [] (Programs.GcdStdio.Spec.encodeOutput
          (UInt64.ofNat (Nat.gcd a.toNat b.toNat))) false -∗
        Phi (.done []))) ⊢
      WP afterAllocExpr @ s; E [{ Phi }] := by
  iintro ⟨Hruntime, Hsp, Hstack, Hcursor, Hheap, Hstreams, Hfinal⟩
  have hreplicate : List.replicate 16 (0 : UInt8) =
      List.replicate 8 0 ++ List.replicate 8 0 := by decide
  isimp only [hreplicate] at Hstack
  isimp only [Programs.GcdStdio.Contracts.ByteSlice] at Hstack
  icases (Programs.ProofSupport.StreamMemory.ByteSlice_append
      entryStackLow (List.replicate 8 0) (List.replicate 8 0)).mp $$
      Hstack with ⟨HstackLo, HstackOut⟩
  have hzero : Programs.GcdStdio.Spec.codec.encode 0 =
      List.replicate 8 0 := by decide
  ihave HoutWord : pointsTo_u64 0 (entryStackLow + 8) 0 $$ [HstackOut]
  · iapply (ByteSlice_word (entryStackLow + 8) 0 (by decide)).mp
    isimp only [hzero]
    unfold Programs.GcdStdio.Contracts.ByteSlice
    isimp only [List.length_replicate] at HstackOut
    iexact HstackOut
  simp only [afterAllocExpr, successBody]
  iapply twp_localGet rfl
  iapply twp_const
  have Hread := Programs.GcdStdio.HostProof.func7_correct (hlc := hlc)
      (ptr := heapBase) (requested := 16)
      (buffer := List.replicate 16 0)
      (input := Programs.GcdStdio.Spec.encodeInput a b)
      (output := []) (raised := false)
      (callerLocals := ⟨[], [.i32 entryStackLow, .i32 heapBase], []⟩)
      (stack := [])
      (code := successBody.drop 3)
      (arity := 0) (remainder := [])
      (controls := [innerFrame, middleFrame, outerFrame])
      (calls := [wrapperFrame]) (s := s) (E := E) (Phi := Phi)
  unfold CallContract callExpr
    Programs.ProofSupport.StreamMemory.callExpr at Hread
  simp only [successBody, List.drop_succ_cons, List.drop_zero,
    List.cons_append, List.nil_append] at Hread
  iapply Hread
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hstreams]
  · iexact Hstreams
  isplitl [Hheap]
  · iexact Hheap
  isplitl []
  · ipureintro
    simp
  iintro Hruntime Hstreams Hheap %hcount
  have htake : (Programs.GcdStdio.Spec.encodeInput a b).take 16 =
      Programs.GcdStdio.Spec.encodeInput a b := by
    rw [← Programs.GcdStdio.Spec.encodeInput_length a b]
    exact List.take_length
  have hdrop : (Programs.GcdStdio.Spec.encodeInput a b).drop 16 = [] := by
    rw [← Programs.GcdStdio.Spec.encodeInput_length a b]
    exact List.drop_length
  isimp only [UInt32.reduceToNat, Programs.GcdStdio.Spec.encodeInput_length,
    _root_.min_self, hdrop, htake,
    List.drop_replicate, Nat.sub_self, List.replicate_zero,
    List.append_nil] at Hstreams Hheap
  ihave Hwords := ByteSlice_input_words a b $$ Hheap
  icases Hwords with ⟨Ha, Hb⟩
  unfold ResumeWP resumeExpr Programs.ProofSupport.StreamMemory.resumeExpr
  simp only [UInt32.reduceToNat, Programs.GcdStdio.Spec.encodeInput_length,
    _root_.min_self, List.cons_append, List.nil_append]
  iapply twp_const
  iapply twp_ne (result := 0) (by decide)
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Ha0 : pointsTo_u64 0 (heapBase + 0) a $$ [Ha]
  · rw [UInt32.add_zero]
    iexact Ha
  iapply twp_load64 (address := heapBase) (offset := 0) a
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) $$ Ha0
  iintro Ha0
  iapply twp_localGet rfl
  iapply twp_load64 (address := heapBase) (offset := 8) b
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) $$ Hb
  iintro Hb
  let gcd := UInt64.ofNat (Nat.gcd a.toNat b.toNat)
  have Hkernel := Programs.GcdStdio.CallKernelProof.func1_correct (hlc := hlc)
      a b
      (callerLocals := ⟨[], [.i32 entryStackLow, .i32 heapBase], []⟩)
      (stack := [.i32 entryStackLow])
      (code := successBody.drop 12)
      (arity := 0) (remainder := [])
      (controls := [innerFrame, middleFrame, outerFrame])
      (calls := [wrapperFrame]) (s := s) (E := E) (Phi := Phi)
  unfold Func1Spec CallContract callExpr Programs.ProofSupport.StreamMemory.callExpr
    at Hkernel
  simp only [successBody, List.drop_succ_cons, List.drop_zero,
    List.cons_append, List.nil_append] at Hkernel
  iapply Hkernel
  isplitl [Hruntime]
  · iexact Hruntime
  unfold KernelContinuation
  iintro Hruntime
  unfold ResumeWP resumeExpr Programs.ProofSupport.StreamMemory.resumeExpr
  simp only [List.cons_append, List.nil_append]
  iapply twp_store64 0 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) $$ HoutWord
  iintro HoutWord
  ihave HoutSlice : Programs.GcdStdio.Contracts.ByteSlice
      (entryStackLow + 8) (Programs.GcdStdio.Spec.encodeOutput gcd) $$
      [HoutWord]
  · unfold Programs.GcdStdio.Spec.encodeOutput
    simp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
      List.append_nil]
    iapply (ByteSlice_word (entryStackLow + 8) gcd (by decide)).mpr
    iexact HoutWord
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [show (8 : UInt32) + entryStackLow = entryStackLow + 8 by decide]
  iapply twp_const
  have Hwrite := Programs.GcdStdio.HostProof.func8_correct (hlc := hlc)
      (ptr := entryStackLow + 8) (requested := 8)
      (bytes := Programs.GcdStdio.Spec.encodeOutput gcd)
      (input := []) (output := []) (raised := false)
      (callerLocals := ⟨[], [.i32 entryStackLow, .i32 heapBase], []⟩)
      (stack := []) (code := successBody.drop 18)
      (arity := 0) (remainder := [])
      (controls := [innerFrame, middleFrame, outerFrame])
      (calls := [wrapperFrame]) (s := s) (E := E) (Phi := Phi)
  unfold CallContract callExpr
    Programs.ProofSupport.StreamMemory.callExpr at Hwrite
  simp only [successBody, List.drop_succ_cons, List.drop_zero,
    List.cons_append, List.nil_append] at Hwrite
  iapply Hwrite
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hstreams]
  · iexact Hstreams
  isplitl [HoutSlice]
  · iexact HoutSlice
  isplitl []
  · ipureintro
    simp [Programs.GcdStdio.Spec.encodeOutput_length]
  iintro Hruntime Hstreams HoutSlice
  unfold ResumeWP resumeExpr Programs.ProofSupport.StreamMemory.resumeExpr
  simp only [List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_const
  isimp only [RuntimeContext] at Hruntime
  icases Hruntime with ⟨Hmodule, Henv⟩
  iapply Wasm.SmallStep.twp_call Programs.GcdStdio.module 8
      Programs.GcdStdio.func5Def (by decide) func5_index $$ Hmodule
  iintro Hmodule
  simp [Programs.GcdStdio.func5Def, Programs.GcdStdio.func5,
    Function.toLocals, Function.numParams]
  iapply Wasm.SmallStep.twp_returnFromCallFallthrough $$ Hmodule
  iintro Hmodule
  iapply twp_br (depth := 1) (arity := 0) (code := [])
      (targetCode := restoreBody) (targetControl := [outerFrame])
      (targetValues := []) (by rfl)
  simp only [restoreBody]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [show (16 : UInt32) + entryStackLow = entryStackTop by decide]
  isimp only [StackPointer] at Hsp
  iapply twp_globalSet $$ Hsp
  iintro _Hsp
  simp only [wrapperFrame]
  iapply twp_returnFromCallExplicit $$ Hmodule
  iintro Hmodule
  simp only [List.take_zero, List.nil_append]
  iapply (twp_finish (locals := ({} : Locals)) (values := [])
    (arity := 0) (remainder := []))
  simp only [List.take_zero, List.nil_append]
  iapply (twp.value (e := (Expr.done [] : Expr Universal.State))
    (v := ObservableOutcome.done []) rfl)
  ihave Hruntime : RuntimeContext $$ [Hmodule Henv]
  · unfold RuntimeContext
    iframe
  iapply Hfinal $$ Hruntime Hstreams

end Programs.GcdStdio.DriverProof
