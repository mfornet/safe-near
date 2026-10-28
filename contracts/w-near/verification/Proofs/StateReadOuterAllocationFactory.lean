import Proofs.StateReadOuterDecoderNative
import Proofs.AllocatePositiveOriginalHeap

/-! Intermediate construction of the actual374 allocation domain. Its heap
lemmas are explicit inputs here, to be derived from ORIGINAL548 data by the
public bridge; they are not new Native fields or final execution premises. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
attribute [local irreducible] readI32 readI64 writeI32 writeI64 packedMemory storageMemory

theorem allocation_native_of_heap(p:Layout)(hn:Native p)
    (decoder:StateDecodeBorshRead.Native (actualDecoder p))(one:decodeCount p=1)
    (split:Allocate.SplitNative (packedMemory p) (readI32 (packedMemory p) p.allocator.toNat) 1)
    (endBound:(Allocate.endWord (packedMemory p) (readI32 (packedMemory p) p.allocator.toNat)).toNat+8≤(packedMemory p).byteSize)
    (flags:readI32 (packedMemory p) (readI32 (packedMemory p) p.allocator.toNat).toNat&&&3=0)
    (candidate:readI32 (packedMemory p) ((readI32 (packedMemory p) p.allocator.toNat).toNat+8)&&&1=0)
    (headAbove:p.memory.byteSize≤(readI32 (packedMemory p) p.allocator.toNat).toNat):
    StateDecodeVectorCopy.Native (actualAllocation p):=by
  let q:=(actualAllocation p).toPositive
  have stack:=allocation_stack_numbers p hn
  have nums:=scratch_numbers p hn
  have geo:=actualAllocation_geometry p hn
  have grow:=storage_grows p hn
  have shape:=packed_shape p hn
  have oldBelow:p.memory.byteSize≤(packedMemory p).byteSize:=by rw[shape.2.1];exact grow
  have memory:q.memory=packedMemory p:=rfl
  have root:q.allocator=p.allocator:=hn.allocationRoot
  have size:q.size=1:=by change decodeCount p=1;exact one
  have wf:q.memory.wf:=by rw[memory];exact shape.1
  have width:q.memory.byteSize≤2^32:=by
    rw[memory]
    simpa only[actualDecoder_memory] using decoder.width
  have lower:16≤q.sp.toNat:=by have lo:=hn.spLower;change 16≤(actualAllocation p).sp.toNat;omega
  have stackBound:q.sp.toNat≤q.memory.byteSize:=by rw[memory];have old:=hn.spBound;change (actualAllocation p).sp.toNat≤_;omega
  have allocatorBound:q.allocator.toNat+4≤q.memory.byteSize:=by
    rw[root,hn.allocator,memory]
    have bound:=hn.storage.register.threadBound
    simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have words:AllocatePositive.words q=1:=by unfold AllocatePositive.words;rw[size];decide
  have nonzero:readI32 q.memory q.allocator.toNat≠0:=by
    rw[memory,root]
    intro hz
    rw[hz] at headAbove
    have lo:=hn.spLower;have old:=hn.spBound
    simp only[UInt32.toNat_zero] at headAbove
    omega
  have search:AllocateSearch.Native (AllocatePositive.searchLayout q):=by
    apply AllocatePositive.search_native_original q wf lower stackBound nonzero
    · rw[memory,root,words];exact split
    · rw[memory,root];exact endBound
    · rw[memory,root];exact flags
    · rw[memory,root];exact candidate
    · rw[memory];have cb:=hn.callbackBound;omega
    · rw[memory,root];have old:=hn.spBound;change (actualAllocation p).sp.toNat≤_;omega
  have positive:AllocatePositive.Native q:=
    ⟨by rw[size];decide,by rw[size];decide,wf,width,lower,stackBound,allocatorBound,search⟩
  have raw:StateDecodeRaw.Native (actualAllocation p).toRaw:=by
    refine ⟨positive,geo.allocationSP,geo.allocationGlobal,stack.2.2.2.2.1,?_,?_,geo.flagZero,?_,?_,?_,?_⟩
    · change (actualAllocation p).spRaw.toNat≤q.memory.byteSize
      rw[memory];have old:=hn.spBound;omega
    · change (actualAllocation p).outRaw.toNat+8≤q.memory.byteSize
      rw[memory];have old:=hn.spBound;omega
    · change q.size.toNat<2^31;rw[size];decide
    · change (actualAllocation p).spRaw.toNat≤q.allocator.toNat
      rw[root,hn.allocator]
      simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
      have cb:=hn.callbackAbove;omega
    · change (actualAllocation p).spRaw.toNat≤(AllocateSearch.head (AllocatePositive.searchLayout q)).toNat
      rw[AllocatePositive.saved_head_original q wf lower stackBound,memory,root]
      have old:=hn.spBound;omega
    · have cb:=hn.callbackAbove;omega
  have vector:StateDecodeVector.Native (actualAllocation p).toVector:=by
    refine ⟨raw,geo.rawSP,geo.rawOut,geo.rawGlobal,stack.2.2.2.1,?_,?_⟩
    · change (actualAllocation p).spVector.toNat≤q.memory.byteSize
      rw[memory];have old:=hn.spBound;omega
    · change (actualAllocation p).outVector.toNat+12≤q.memory.byteSize
      rw[memory];have old:=hn.spBound;omega
  refine ⟨vector,?_⟩
  have hb:=decoder.headerBound
  have cb:(actualDecoder p).pointer.toNat+4+(decodeCount p).toNat+24≤(packedMemory p).byteSize:=hb
  have w:(packedMemory p).byteSize≤2^32:=by simpa only[actualDecoder_memory] using decoder.width
  have add:(StateDecodePrefix.payloadPointer (actualDecoder p).toPrefix).toNat=(actualDecoder p).pointer.toNat+4:=by
    unfold StateDecodePrefix.payloadPointer
    rw[UInt32.toNat_add]
    simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    exact Nat.mod_eq_of_lt (by omega)
  change (StateDecodePrefix.payloadPointer (actualDecoder p).toPrefix).toNat+(decodeCount p).toNat≤(packedMemory p).byteSize
  rw[add]
  omega
end WNear.Proofs.StateReadOuter
