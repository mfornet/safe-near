import Proofs.StateDecodePrefixWrapperControl
import Proofs.StateDecodePrefixOutputSteps

/-! Actual315 accepted result snapshots both fields before either caller write. -/
namespace WNear.Proofs.StateDecodePrefixWrapper.Tail
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
structure Layout where
  memory:Memory
  index:Nat
  globalIndex:Nat
  out:UInt32
  pointer:UInt32
structure Native(p:Layout):Prop where
  wf:p.memory.wf
  width:p.memory.byteSize≤2^32
  pointerBound:p.pointer.toNat+16≤p.memory.byteSize
  outputBound:p.out.toNat+16≤p.memory.byteSize

def lowValue(p:Layout):=readI64 p.memory (p.pointer.toNat+4)
def highValue(p:Layout):=readI32 p.memory (p.pointer+12).toNat
def lowMemory(p:Layout):=writeI64 p.memory (p.out.toNat+4) (lowValue p)
def highMemory(p:Layout):=writeI32 (lowMemory p) (p.out+12).toNat (highValue p)
def finalMemory(p:Layout):=writeI32 (highMemory p) p.out.toNat 0

def copyFrame(frame:CallFrame)(p:Layout):={frame with locals:=frame.locals.set! 1 (.i32 (highValue p))}
def finalFrame(frame:CallFrame)(p:Layout):=
  {(cacheFrame frame p.memory p.pointer) with locals:=(cacheFrame frame p.memory p.pointer).locals.set! 1 (.i32 0)}
def cached(s:Store NearState)(op:Nat):=paid s op 5
def guarded(s:Store NearState)(op:Nat):=paid (cached s op) op 5
def highRead(s:Store NearState)(op:Nat):=paid s op 5
def copiedLow(s:Store NearState)(op:Nat)(p:Layout):=storeI64 (paid (highRead s op) op 3) p.index (p.out.toNat+4) p.memory (lowValue p)
def copiedHigh(s:Store NearState)(op:Nat)(p:Layout):=storeI32 (paid (copiedLow s op p) op 5) p.index (p.out+12).toNat (lowMemory p) (highValue p)
def zeroed(s:Store NearState)(op:Nat)(p:Layout):=paid (copiedHigh s op p) op 2
def copied(s:Store NearState)(op:Nat)(p:Layout):=chargedStore (zeroed s op p) op

def tagged(s:Store NearState)(op:Nat)(p:Layout):=storeI32 (paid s op 3) p.index p.out.toNat (highMemory p) 0
def finished(s:Store NearState)(op:Nat)(p:Layout):=setGlobal (paid (tagged s op p) op 4) p.globalIndex (.i32 (p.pointer+16))
def after(s:Store NearState)(op:Nat)(p:Layout):=finished (copied (guarded s op) op p) op p

theorem add_pointer(p:Layout)(hn:Native p):(p.pointer+12).toNat=p.pointer.toNat+12:=by
  rw[UInt32.toNat_add]
  simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
  have b:=hn.pointerBound;have w:=hn.width;omega
theorem add_output(p:Layout)(hn:Native p):(p.out+12).toNat=p.out.toNat+12:=by
  rw[UInt32.toNat_add]
  simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
  have b:=hn.outputBound;have w:=hn.width;omega

theorem memory_specs(p:Layout)(hn:Native p):
    (lowMemory p).wf ∧(lowMemory p).byteSize=p.memory.byteSize ∧
    (highMemory p).wf ∧(highMemory p).byteSize=p.memory.byteSize:=by
  have lb:p.out.toNat+4+8≤p.memory.byteSize:=by have b:=hn.outputBound;omega
  have l:=writeI64_spec p.memory (p.out.toNat+4) (lowValue p) hn.wf lb
  have hb:(p.out+12).toNat+4≤(lowMemory p).byteSize:=by
    change _≤(writeI64 _ _ _).byteSize
    rw[l.2.1,add_output p hn];exact hn.outputBound
  have h:=writeI32_spec (lowMemory p) (p.out+12).toNat (highValue p) l.1 hb
  exact ⟨l.1,l.2.1,h.1,h.2.1.trans l.2.1⟩
end WNear.Proofs.StateDecodePrefixWrapper.Tail
