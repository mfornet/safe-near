import Proofs.StateDecodeVectorCall
import Proofs.StateDecodeVectorCopySteps
import Proofs.AllocatePositivePayload
import Proofs.UnwrapStateCopyEffects

/-! Actual374 uses the exact post373 heap, then the real sequential951 copy.
Its operational domain permits source/output aliases. -/
namespace WNear.Proofs.StateDecodeVectorCopy
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
structure Layout extends toVector:StateDecodeVector.Layout where
  source:UInt32
  address373:Nat
  address951:Nat
structure Native (p:Layout):Prop where
  vector:StateDecodeVector.Native p.toVector
  sourceBound:p.source.toNat+p.size.toNat≤p.memory.byteSize
structure Code (s:Store NearState)(inst:Nat)(p:Layout)(a581 a236:Nat):Prop where
  vector:StateDecodeVector.Code s inst p.toVector a581 a236
  index373:p.mi.funcAddrs[373]?=some p.address373
  function373:s.funcs[p.address373]?=some (.wasm WNear.Binary.StateDecodeVector.signature inst WNear.Binary.StateDecodeVector.function)
  index951:p.mi.funcAddrs[951]?=some p.address951
  function951:s.funcs[p.address951]?=some (.wasm WNear.Binary.UnwrapState.Copy.signature inst WNear.Binary.UnwrapState.Copy.function)

def pointer (p:Layout):UInt32:=StateDecodeRaw.result p.toVector.toRaw
def vectorBefore (s:Store NearState)(op:Nat):=paid s op 2
def vectorAfter (cfg:WasmConfig)(s:Store NearState)(p:Layout):=StateDecodeVector.callAfter cfg (vectorBefore s cfg.regularOpCost) p.toVector
def copyArguments (cfg:WasmConfig)(s:Store NearState)(p:Layout):=paid (vectorAfter cfg s p) cfg.regularOpCost 4
def copiedMemory (p:Layout):=ForwardCopyMemory.forward (StateDecodeVector.finalMemory p.toVector) (pointer p).toNat p.source.toNat p.size.toNat
def copied (cfg:WasmConfig)(s:Store NearState)(p:Layout):=UnwrapStateCopyEntry.callAfter (copyArguments cfg s p) cfg.regularOpCost p.memoryIndex (pointer p) p.source (StateDecodeVector.finalMemory p.toVector) p.size.toNat
def finalMemory (p:Layout):=writeI32 (copiedMemory p) (p.outVector.toNat+8) p.size
def after (cfg:WasmConfig)(s:Store NearState)(p:Layout):=finishStore (copied cfg s p) cfg.regularOpCost p.memoryIndex (copiedMemory p) p.outVector p.size

def bodyCost (p:Layout):=18*p.size.toNat+647
def bodySteps (p:Layout):=17*p.size.toNat+517

theorem copy_bounds (p:Layout)(hn:Native p):
    (StateDecodeVector.finalMemory p.toVector).wf ∧
    (StateDecodeVector.finalMemory p.toVector).byteSize=p.memory.byteSize ∧
    (StateDecodeVector.finalMemory p.toVector).byteSize≤2^32 ∧
    p.source.toNat+p.size.toNat≤(StateDecodeVector.finalMemory p.toVector).byteSize ∧
    (pointer p).toNat+p.size.toNat≤(StateDecodeVector.finalMemory p.toVector).byteSize ∧
    0<p.size.toNat ∧ p.size.toNat<2^32:=by
  have shape:=StateDecodeVector.finalMemory_shape p.toVector hn.vector
  have actual:=StateDecodeRaw.allocation_native p.toVector.toRaw hn.vector.raw
  have span:=AllocatePositive.result_size_span (StateDecodeRaw.actualPositive p.toVector.toRaw) actual
  have allocationShape:=StateDecodeRaw.allocated_spec p.toVector.toRaw hn.vector.raw
  have pos:0<p.size.toNat:=by
    have ne:p.size.toNat≠0:=by
      intro hz
      apply hn.vector.raw.allocation.positive
      exact UInt32.toNat_inj.mp hz
    omega
  have width:=hn.vector.raw.allocation.width
  refine ⟨shape.1,shape.2.1,?_,?_,?_,pos,?_⟩
  · rw[shape.2.1];exact width
  · rw[shape.2.1];exact hn.sourceBound
  · rw[shape.2.1]
    have ae:(AllocatePositive.finalMemory (StateDecodeRaw.actualPositive p.toVector.toRaw)).byteSize=p.memory.byteSize:=by
      simpa only[StateDecodeRaw.allocatedMemory] using allocationShape.2.1
    rw[ae] at span
    simpa only[pointer,StateDecodeRaw.result,StateDecodeRaw.actualPositive] using span
  · have h:=hn.vector.raw.sizeSigned;omega
end WNear.Proofs.StateDecodeVectorCopy
