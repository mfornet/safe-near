import Proofs.StateReadOuterCode
import Proofs.StateReadOuterCallback

/-! The actual prepared161 code follows original installed descriptors and the
proved allocator-selector frame. No future Code or heap Native is a premise. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
attribute [local irreducible] readI32 readI64 writeI32 writeI64 packedMemory storageMemory copiedMemory decodeCount StateDecodePrefix.payloadPointer

private theorem allocation_code(s:Store NearState)(inst:Nat)(p:Layout)(a581 a236:Nat)
    (hn:Native p)(hc:StateDecodeVectorCopy.Code s inst p.allocationTemplate a581 a236):
    StateDecodeVectorCopy.Code s inst (actualAllocation p) a581 a236:=by
  have original:=hc.vector.raw.record.allocation
  have positive:AllocatePositive.Code s inst (actualAllocation p).toPositive:=by
    refine ⟨?_,original.globalIndex,original.alignIndex,original.alignFunction,
      original.roundIndex,original.roundFunction,original.searchIndex,original.searchFunction⟩
    refine ⟨?_,original.search.sizeIndex,original.search.sizeFunction⟩
    refine ⟨original.search.module,original.search.memoryIndex,original.search.tableIndex,original.search.table,
      ?_,original.search.callbackType,original.search.callbackFunction,original.search.unitsIndex,
      original.search.unitsFunction,original.search.minimumIndex,original.search.minimumFunction⟩
    change p.allocationTemplate.table.elems[(readI32 (AllocatePositive.savedMemory (actualAllocation p).toPositive) 1057480).toNat]?=some (.func p.allocationTemplate.callbackAddress)
    rw[saved_callback_word p hn]
    exact original.search.callbackElement
  have record:StateDecodeRaw.RecordCode s inst (actualAllocation p).toPositive a581 a236 p.allocationTemplate.address310 :=
    ⟨positive,hc.vector.raw.record.index581,hc.vector.raw.record.function581,
      hc.vector.raw.record.index236,hc.vector.raw.record.function236,
      hc.vector.raw.record.index310,hc.vector.raw.record.function310⟩
  have raw:StateDecodeRaw.Code s inst (actualAllocation p).toRaw a581 a236 :=
    ⟨record,hc.vector.raw.index751,hc.vector.raw.function751,hc.vector.raw.index752,hc.vector.raw.function752,
      hc.vector.raw.index769,hc.vector.raw.function769,hc.vector.raw.index770,hc.vector.raw.function770⟩
  have vector:StateDecodeVector.Code s inst (actualAllocation p).toVector a581 a236 :=
    ⟨raw,hc.vector.index767,hc.vector.function767⟩
  exact ⟨vector,hc.index373,hc.function373,hc.index951,hc.function951⟩

theorem Code.decoderActual(s:Store NearState)(inst:Nat)(p:Layout)(extra a581 a236:Nat)
    (hn:Native p)(hc:Code s inst p extra a581 a236):
    StateDecodeBorshRead.Code s inst (actualDecoder p) (actualAllocation p) a581 a236:=by
  have allocation:=allocation_code s inst p a581 a236 hn hc.decoder.child.child.allocation
  have pc:=hc.decoder.child.child.prefixCode.child
  have pref:StateDecodePrefix.Code s inst (actualDecoder p).toPrefix:=
    ⟨pc.module,pc.memoryIndex,pc.globalIndex,pc.takeAddress,pc.takeFunction,
      pc.dropAddress,pc.dropFunction,pc.wordAddress,pc.wordFunction,pc.lengthAddress,
      pc.lengthFunction,pc.copyAddress,pc.copyFunction⟩
  have wrapper:StateDecodePrefixWrapper.Code s inst (actualDecoder p).toPrefixWrapper:=
    ⟨pref,hc.decoder.child.child.prefixCode.childAddress,hc.decoder.child.child.prefixCode.childFunction⟩
  have borsh:StateDecodeBorsh.Code s inst (actualDecoder p).toBorsh (actualAllocation p) a581 a236:=
    ⟨wrapper,allocation,hc.decoder.child.child.index315,hc.decoder.child.child.function315,
      hc.decoder.child.child.index372,hc.decoder.child.child.function372,hc.decoder.child.child.index371,hc.decoder.child.child.function371,
      hc.decoder.child.child.index694,hc.decoder.child.child.function694,hc.decoder.child.child.index710,hc.decoder.child.child.function710⟩
  have entry:StateDecodeBorshWrapper.Code s inst (actualDecoder p).toWrapper (actualAllocation p) a581 a236:=
    ⟨borsh,hc.decoder.child.index425,hc.decoder.child.function425,hc.decoder.child.index951,hc.decoder.child.function951⟩
  exact ⟨entry,hc.decoder.index162,hc.decoder.function162,hc.decoder.index951,hc.decoder.function951⟩
end WNear.Proofs.StateReadOuter
