import Binary.StateDecodePrefixWrapper
import Proofs.StateDecodePrefixNative
import Proofs.StateDecodePrefixCode
import Proofs.StorePairCallerState

/-! Original315 resources. Its316 child runs on the original memory, with the
actual16-byte stack reservation; no child execution outcome is a premise. -/
namespace WNear.Proofs.StateDecodePrefixWrapper
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
structure Layout extends toPrefix : StateDecodePrefix.Layout where
  wrapperSP : UInt32
  wrapperGlobal : GlobalInst
  wrapperOut : UInt32
  address316 : Nat

def scratch (p : Layout) := p.wrapperSP-16
structure Native (p : Layout) : Prop where
  child : StateDecodePrefix.Native p.toPrefix
  childSP : p.sp=scratch p
  childOut : p.out=scratch p
  childGlobal : p.global={p.wrapperGlobal with value:=.i32 (scratch p)}
  outputBound : p.wrapperOut.toNat+16≤p.memory.byteSize

structure Code (s : Store NearState) (inst : Nat) (p : Layout) : Prop where
  child : StateDecodePrefix.Code s inst p.toPrefix
  childAddress : p.mi.funcAddrs[316]?=some p.address316
  childFunction : s.funcs[p.address316]?=some (.wasm WNear.Binary.StateDecodePrefix.signature inst WNear.Binary.StateDecodePrefix.function)

def reserved (s : Store NearState) (op : Nat) (p : Layout) :=setGlobal (paid s op 5) p.globalIndex (.i32 (scratch p))
def arguments (s : Store NearState) (op : Nat) (p : Layout) :=paid (reserved s op p) op 2

def reservedFrame (frame : CallFrame) (p : Layout) := {frame with locals:=frame.locals.set! 2 (.i32 (scratch p))}
def cacheFrame (frame : CallFrame) (memory : Memory) (pointer : UInt32) :=
  {frame with locals:=(frame.locals.set! 1 (.i32 1)).set! 3 (.i64 (readI64 memory (pointer.toNat+4)))}

theorem child_scratch_bound (p : Layout) (hn : Native p) :
    (scratch p).toNat+16≤p.memory.byteSize := by
  have h:=hn.child.outBound
  simpa only[hn.childOut] using h
end WNear.Proofs.StateDecodePrefixWrapper
