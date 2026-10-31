import Bridge.Functions.SerdeActualSink

namespace WNear.Binary.SerdeSyntax
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.Interface WNear.Binary.SerdeErrorWriters WNear.Binary.SerdeActualSink
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

/-- Payload and descriptor ownership retained while formatting a static ErrorCode. -/
def syntaxPayload (n : Nat) (desc e tag : UInt32) (sb : List UInt8) : IProp GF :=
  iprop(n ↦[i32][ desc.toNat ] e ∗ n ↦[i32][ e.toNat ] tag ∗
    n ↦[wms][ (SerdeErrorWriters.syntaxSlice tag).1.toNat ] sb)

/-- String sink state excluding the single global stack-pointer cell lent to each callee. -/
def stringBody (n ta : Nat) (s dd vec ptr cap idx : UInt32)
    (a578 maxP hl F : Nat) (live : List (Nat × Nat)) (bs : List UInt8) : IProp GF :=
  iprop(n ↦[i32][ dd.toNat ] vec ∗ VecFromElem.stk n (s.toNat - 112) 112 ∗
    AllocFirstFit.vt n 1057464 idx ta a578 ∗ n ↦[i32][ vec.toNat ] ptr ∗
    n ↦[i32][ vec.toNat + 4 ] cap ∗ n ↦[i32][ vec.toNat + 8 ] UInt32.ofNat bs.length ∗
    ScratchGrow.sbuf n maxP hl live F ptr cap bs)

/-- Actual String state after appending the selected static ErrorCode payload. -/
def writtenBody (n ta : Nat) (s dd vec idx desc e tag : UInt32)
    (a578 maxP hl F : Nat) (live : List (Nat × Nat)) (sb : List UInt8) : IProp GF :=
  iprop(∃ (p : UInt32) (hl' : Nat),
    ⌜ScratchGrow.hlAfter hl hl' 0 0 (syntaxSlice tag).2⌝ ∗
    stringBody n ta s dd vec p (ScratchGrow.capAfter 0 0 (syntaxSlice tag).2) idx a578 maxP hl'
      (ScratchGrow.fAfter F 0 0 (syntaxSlice tag).2) live sb ∗ syntaxPayload n desc e tag sb)

noncomputable def costArg (cfg : WasmConfig) (F : Nat) (dd tag : UInt32) : Nat :=
  133 * cfg.regularOpCost + activationGas cfg.regularOpCost
    (entryLocals f616 [.i32 dd, .i32 (syntaxSlice tag).1, .i32 (syntaxSlice tag).2]) +
    (36 * cfg.regularOpCost + ScratchGrow.costExt cfg F 0 0 (syntaxSlice tag).2)

noncomputable def costEngine (cfg : WasmConfig) (F : Nat) (dd tag : UInt32) : Nat :=
  100 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals f616 [.i32 0, .i32 0, .i32 0]) +
    (36 * cfg.regularOpCost + ScratchGrow.costExt cfg F 0 0 0) +
    activationGas cfg.regularOpCost (entryLocals f591 [.i32 0, .i32 0]) + costArg cfg F dd tag

/-- The concrete first engine resources besides its global, copied Arguments and owned data word. -/
def engineIn (n ta : Nat) (s vec idx argp desc e tag : UInt32)
    (a578 a591 a616 maxP hl F : Nat) (live : List (Nat × Nat)) (sb : List UInt8) : IProp GF :=
  iprop(VecFromElem.stk n (s.toNat - 160) 160 ∗
    FmtWrite.pieceArg n ta 1057628 1057628 0 argp desc 126 a591 ∗
    n ↦[i32][ (1057784 : UInt32).toNat + 12 ] 130 ∗ ta ↦[wt][ (130 : UInt32).toNat ] Ref.func a616 ∗
    AllocFirstFit.vt n 1057464 idx ta a578 ∗ SerdeDebug.stringCells n vec 1 0 0 ∗
    ScratchGrow.sbuf n maxP hl live F 1 0 [] ∗ syntaxPayload n desc e tag sb)

/-- The same retained engine resources, with the actual allocated String result. -/
def engineOut (n ta : Nat) (s vec idx argp desc e tag : UInt32)
    (a578 a591 a616 maxP hl F : Nat) (live : List (Nat × Nat)) (sb : List UInt8) : IProp GF :=
  iprop(VecFromElem.stk n (s.toNat - 160) 160 ∗
    FmtWrite.pieceArg n ta 1057628 1057628 0 argp desc 126 a591 ∗
    n ↦[i32][ (1057784 : UInt32).toNat + 12 ] 130 ∗ ta ↦[wt][ (130 : UInt32).toNat ] Ref.func a616 ∗
    AllocFirstFit.vt n 1057464 idx ta a578 ∗
    ∃ (p : UInt32) (hl' : Nat), ⌜ScratchGrow.hlAfter hl hl' 0 0 (syntaxSlice tag).2⌝ ∗
    SerdeDebug.stringCells n vec p (ScratchGrow.capAfter 0 0 (syntaxSlice tag).2) (UInt32.ofNat sb.length) ∗
    ScratchGrow.sbuf n maxP hl' live (ScratchGrow.fAfter F 0 0 (syntaxSlice tag).2) p
      (ScratchGrow.capAfter 0 0 (syntaxSlice tag).2) sb ∗ syntaxPayload n desc e tag sb)

/-- Exact retained readonly, error-tag and allocator resources of the static first writer. -/
def codeShared (n ta : Nat) (e tag idx : UInt32) (a578 a591 a616 : Nat) (sb : List UInt8) : IProp GF :=
  iprop(n ↦[i32][ e.toNat ] tag ∗ n ↦[wms][ (syntaxSlice tag).1.toNat ] sb ∗
    n ↦[i32][ 1057628 ] 1057628 ∗ n ↦[i32][ 1057632 ] 0 ∗ ta ↦[wt][ 126 ] Ref.func a591 ∗
    n ↦[i32][ 1057796 ] 130 ∗ ta ↦[wt][ 130 ] Ref.func a616 ∗ AllocFirstFit.vt n 1057464 idx ta a578)

/-- The first writer's actual owned result: unchanged shared cells and String allocation/bytes. -/
def codeResult (n ta : Nat) (e tag idx : UInt32) (a578 a591 a616 maxP hl F : Nat)
    (live : List (Nat × Nat)) (sb : List UInt8) (p c l : UInt32) : IProp GF :=
  iprop(codeShared n ta e tag idx a578 a591 a616 sb ∗ ∃ hl' : Nat,
    ⌜c = ScratchGrow.capAfter 0 0 (syntaxSlice tag).2 ∧ l = UInt32.ofNat sb.length ∧
      ScratchGrow.hlAfter hl hl' 0 0 (syntaxSlice tag).2⌝ ∗
    ScratchGrow.sbuf n maxP hl' live (ScratchGrow.fAfter F 0 0 (syntaxSlice tag).2) p c sb)

noncomputable def costCodeWriter (cfg : WasmConfig) (F : Nat) (sp tag : UInt32) : Nat :=
  60 * cfg.regularOpCost + activationGas cfg.regularOpCost (entryLocals f872 [.i32 0, .i32 0, .i32 0]) +
    costEngine cfg F (sp - 80 - 32 + 4) tag

end WNear.Binary.SerdeSyntax
