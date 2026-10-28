import Binary.AllocateRecordCopy
import Proofs.AllocateRecordState
import Proofs.AllocateRecordCopyReadback

/-! Original resources and sequential states of the real690 wrapper. -/
namespace WNear.Proofs.AllocateRecordCopy
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

structure Layout where
  inner : AllocateRecord.Layout
  out : UInt32
  sp : UInt32
  global : GlobalInst
  address689 : Nat

structure Native (p : Layout) : Prop where
  inner : AllocateRecord.Native p.inner
  innerSP : p.inner.sp=p.sp-16
  innerOut : p.inner.out=p.inner.sp+8
  innerGlobal : p.inner.global={p.global with value:=.i32 p.inner.sp}
  outputBound : p.out.toNat+8≤p.inner.memory.byteSize
  scratchBound : p.inner.sp.toNat+16≤p.inner.memory.byteSize

structure Code (s : Store NearState) (inst : Nat) (p : Layout) : Prop where
  inner : AllocateRecord.Code s inst p.inner
  index689 : p.inner.mi.funcAddrs[689]?=some p.address689
  function689 : s.funcs[p.address689]?=some (.wasm WNear.Binary.AllocateRecord.signature inst WNear.Binary.AllocateRecord.function)

def reserved (s : Store NearState) (op : Nat) (p : Layout) :=
  setGlobal (paid s op 5) p.inner.globalIndex (.i32 p.inner.sp)
def arguments (s : Store NearState) (op : Nat) (p : Layout) := paid (reserved s op p) op 6
def recordEntered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (10*op)
def allocated (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  AllocateRecord.after cfg (recordEntered (arguments s cfg.regularOpCost p) cfg.regularOpCost) p.inner
def allocatedMemory (p : Layout) := AllocateRecord.finalMemory p.inner
def copyDone (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  AllocateRecordCopy.copied (allocated cfg s p) cfg.regularOpCost p.inner.memoryIndex p.out p.inner.sp (allocatedMemory p)
def resultMemory (p : Layout) := finalMemory (allocatedMemory p) p.out p.inner.sp

def after (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  setGlobal (paid (copyDone cfg s p) cfg.regularOpCost 4) p.inner.globalIndex (.i32 p.sp)
def resultFrame (frame : CallFrame) (p : Layout) := {frame with locals:=frame.locals.set! 3 (.i32 p.inner.sp)}
def bodyCost (p : Layout) := AllocateRecord.bodyCost p.inner+34
def bodySteps (p : Layout) := AllocateRecord.bodySteps p.inner+25
def fee (cfg : WasmConfig) (p : Layout) := AllocateRecord.fee cfg p.inner

theorem Code.transport (s t : Store NearState) (inst : Nat) (p : Layout) (h : Code s inst p)
    (hf : t.funcs=s.funcs) (hm : t.modules=s.modules) (ht : t.tables=s.tables) : Code t inst p := by
  refine ⟨h.inner.transport s t inst p.inner hf hm ht,h.index689,?_⟩
  rw [hf];exact h.function689
end WNear.Proofs.AllocateRecordCopy
