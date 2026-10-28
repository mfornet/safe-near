import Proofs.StateDecodeBorshReadPhases
import Proofs.StateDecodeBorshReadAllocation

/-! Installed161 code and original-memory to actual162 code transport.
The sole memory-dependent selector is proved preserved by the original domain. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
attribute [local irreducible] readI32 readI64 writeI32 writeI64 setupMemory
structure Code(s:Store NearState)(inst:Nat)(p:Layout)(q:StateDecodeVectorCopy.Layout)(a581 a236:Nat):Prop where
  child:StateDecodeBorshWrapper.Code s inst p.toWrapper q a581 a236
  index162:p.mi.funcAddrs[162]?=some p.address162
  function162:s.funcs[p.address162]?=some (.wasm WNear.Binary.StateDecodeBorshWrapper.signature inst WNear.Binary.StateDecodeBorshWrapper.function)
  index951:p.mi.funcAddrs[951]?=some p.address951
  function951:s.funcs[p.address951]?=some (.wasm WNear.Binary.UnwrapState.Copy.signature inst WNear.Binary.UnwrapState.Copy.function)

theorem allocation_code(s:Store NearState)(inst:Nat)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (a581 a236:Nat)(hn:Native p)(hd:AllocationDomain p q)
    (hc:StateDecodeVectorCopy.Code s inst q a581 a236):
    StateDecodeVectorCopy.Code s inst (actualAllocation p q) a581 a236:=by
  have original:=hc.vector.raw.record.allocation
  have positive:AllocatePositive.Code s inst (actualAllocation p q).toPositive:=by
    refine ⟨?_,original.globalIndex,original.alignIndex,original.alignFunction,
      original.roundIndex,original.roundFunction,original.searchIndex,original.searchFunction⟩
    refine {module:=original.search.module,memoryIndex:=original.search.memoryIndex,tableIndex:=original.search.tableIndex,table:=original.search.table,callbackElement:=?_,callbackType:=original.search.callbackType,callbackFunction:=original.search.callbackFunction,unitsIndex:=original.search.unitsIndex,unitsFunction:=original.search.unitsFunction,minimumIndex:=original.search.minimumIndex,minimumFunction:=original.search.minimumFunction,sizeIndex:=original.search.sizeIndex,sizeFunction:=original.search.sizeFunction}
    change q.table.elems[(readI32 (AllocatePositive.savedMemory (actualAllocation p q).toPositive) 1057480).toNat]?=some (.func q.callbackAddress)
    rw[saved_callback_word p q hn hd]
    exact original.search.callbackElement
  have record:StateDecodeRaw.RecordCode s inst (actualAllocation p q).toPositive a581 a236 q.address310 :=
    ⟨positive,hc.vector.raw.record.index581,hc.vector.raw.record.function581,
      hc.vector.raw.record.index236,hc.vector.raw.record.function236,
      hc.vector.raw.record.index310,hc.vector.raw.record.function310⟩
  have raw:StateDecodeRaw.Code s inst (actualAllocation p q).toRaw a581 a236 :=
    ⟨record,hc.vector.raw.index751,hc.vector.raw.function751,hc.vector.raw.index752,hc.vector.raw.function752,
      hc.vector.raw.index769,hc.vector.raw.function769,hc.vector.raw.index770,hc.vector.raw.function770⟩
  have vector:StateDecodeVector.Code s inst (actualAllocation p q).toVector a581 a236 :=
    ⟨raw,hc.vector.index767,hc.vector.function767⟩
  exact ⟨vector,hc.index373,hc.function373,hc.index951,hc.function951⟩
theorem Code.child_actual(s:Store NearState)(inst:Nat)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (a581 a236:Nat)(hn:Native p)(hd:AllocationDomain p q)(hc:Code s inst p q a581 a236):
    StateDecodeBorshWrapper.Code s inst (actualWrapper p) (actualAllocation p q) a581 a236:=by
  have alloc:=allocation_code s inst p q a581 a236 hn hd hc.child.child.allocation
  have pc:=hc.child.child.prefixCode.child
  have pref:StateDecodePrefix.Code s inst (actualWrapper p).toPrefix:=
    ⟨pc.module,pc.memoryIndex,pc.globalIndex,pc.takeAddress,pc.takeFunction,
      pc.dropAddress,pc.dropFunction,pc.wordAddress,pc.wordFunction,pc.lengthAddress,
      pc.lengthFunction,pc.copyAddress,pc.copyFunction⟩
  have wrapper:StateDecodePrefixWrapper.Code s inst (actualWrapper p).toPrefixWrapper:=
    ⟨pref,hc.child.child.prefixCode.childAddress,hc.child.child.prefixCode.childFunction⟩
  have child:StateDecodeBorsh.Code s inst (actualWrapper p).toBorsh (actualAllocation p q) a581 a236:=
    ⟨wrapper,alloc,hc.child.child.index315,hc.child.child.function315,
      hc.child.child.index372,hc.child.child.function372,hc.child.child.index371,hc.child.child.function371,
      hc.child.child.index694,hc.child.child.function694,hc.child.child.index710,hc.child.child.function710⟩
  exact ⟨child,hc.child.index425,hc.child.function425,hc.child.index951,hc.child.function951⟩
theorem Code.transport(s t:Store NearState)(inst:Nat)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (a581 a236:Nat)(hc:Code s inst p q a581 a236)
    (hf:t.funcs=s.funcs)(hm:t.modules=s.modules)(ht:t.tables=s.tables):Code t inst p q a581 a236:=by
  have child:=hc.child.child.transport s t inst p.toBorsh q a581 a236 hf hm ht
  have wrapper:StateDecodeBorshWrapper.Code t inst p.toWrapper q a581 a236:=by
    refine ⟨child,hc.child.index425,?_,hc.child.index951,?_⟩
    · rw[hf];exact hc.child.function425
    · rw[hf];exact hc.child.function951
  refine ⟨wrapper,hc.index162,?_,hc.index951,?_⟩
  · rw[hf];exact hc.function162
  · rw[hf];exact hc.function951
end WNear.Proofs.StateDecodeBorshRead
