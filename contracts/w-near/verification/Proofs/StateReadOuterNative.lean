import Proofs.StateReadOuterState
import Proofs.StateReadOuterStorageHeader

/-! Original219 memory, ABI and stack-template compatibility. Every field is
an original scalar/resource condition; no prepared decoder or release Native
is an assumption. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic

structure DecoderGeometry(d:StateDecodeBorshRead.Layout):Prop where
  slice:d.slice=StateDecodeBorshRead.scratch d+8
  wrapperSP:d.sp162=StateDecodeBorshRead.scratch d
  wrapperOut:d.out162=StateDecodeBorshRead.scratch d+96
  wrapperGlobal:d.global162={d.global161 with value:=.i32 (StateDecodeBorshRead.scratch d)}
  borshSP:d.sp425=StateDecodeBorshWrapper.scratch d.toWrapper
  borshOut:d.out425=StateDecodeBorshWrapper.scratch d.toWrapper+48
  borshGlobal:d.global425={d.global162 with value:=.i32 (StateDecodeBorshWrapper.scratch d.toWrapper)}
  prefixSP:d.wrapperSP=StateDecodeBorsh.scratch d.toBorsh
  prefixOut:d.wrapperOut=StateDecodeBorsh.scratch d.toBorsh+56
  prefixGlobal:d.wrapperGlobal={d.global425 with value:=.i32 (StateDecodeBorsh.scratch d.toBorsh)}
  childSP:d.sp=StateDecodePrefixWrapper.scratch d.toPrefixWrapper
  childOut:d.out=StateDecodePrefixWrapper.scratch d.toPrefixWrapper
  childGlobal:d.global={d.wrapperGlobal with value:=.i32 (StateDecodePrefixWrapper.scratch d.toPrefixWrapper)}

structure AllocationGeometry(d:StateDecodeBorshRead.Layout)(q:StateDecodeVectorCopy.Layout):Prop where
  vectorSP:q.spVector=StateDecodePrefix.scratch d.toPrefix
  vectorOut:q.outVector=StateDecodePrefix.allocatedOut d.toPrefix
  vectorGlobal:q.globalVector={d.global with value:=.i32 (StateDecodePrefix.scratch d.toPrefix)}
  rawSP:q.spRaw=q.spVector-16
  rawOut:q.outRaw=q.spRaw+8
  rawGlobal:q.globalRaw={q.globalVector with value:=.i32 q.spRaw}
  allocationSP:q.sp=q.spRaw-48
  allocationGlobal:q.global={q.globalRaw with value:=.i32 q.sp}
  flagZero:q.flag=0

structure Native(p:Layout):Prop where
  storage:StateReadStorageOuter.Native p.toStorage
  allocator:p.allocator=1074896
  spLower:592≤p.sp219.toNat
  spBound:p.sp219.toNat≤p.memory.byteSize
  aligned:p.sp219.toNat%16=0
  outputBound:p.out219.toNat+40≤p.memory.byteSize
  outputAbove:p.sp219.toNat≤p.out219.toNat
  outputRootSep:p.out219.toNat+40≤p.allocator.toNat ∨p.allocator.toNat+4≤p.out219.toNat
  callbackAbove:p.sp219.toNat≤1057464
  callbackBound:1057484≤p.memory.byteSize
  storageSP:p.sp548=scratch p
  storageOut:p.out548=scratch p+8
  storageGlobal:p.global548={p.global219 with value:=.i32 (scratch p)}
  keyPointer:p.keyPtr=1049788
  keyLength:p.keyLen=5
  decoderMemory:p.decoderTemplate.memory=p.memory
  decoderModule:p.decoderTemplate.mi=p.mi
  decoderMemoryIndex:p.decoderTemplate.memoryIndex=p.memoryIndex
  decoderGlobalIndex:p.decoderTemplate.globalIndex=p.globalIndex
  decoderSP:p.decoderTemplate.sp161=scratch p
  decoderOut:p.decoderTemplate.out161=scratch p+40
  decoderGlobal:p.decoderTemplate.global161=p.global548
  decoderGeometry:DecoderGeometry p.decoderTemplate
  allocationMemory:p.allocationTemplate.memory=p.memory
  allocationModule:p.allocationTemplate.mi=p.mi
  allocationMemoryIndex:p.allocationTemplate.memoryIndex=p.memoryIndex
  allocationGlobalIndex:p.allocationTemplate.globalIndex=p.globalIndex
  allocationRoot:p.allocationTemplate.allocator=p.allocator
  allocationSPBounds:16≤p.allocationTemplate.sp.toNat ∧p.allocationTemplate.sp.toNat≤(scratch p).toNat
  allocationGeometry:AllocationGeometry p.decoderTemplate p.allocationTemplate
  releaseRoot:p.releaseTemplate.allocator=p.allocator

private theorem sub_nat(x:UInt32)(n:Nat)(h:n≤x.toNat)(hn:n<2^32):
    (x-UInt32.ofNat n).toNat=x.toNat-n:=by
  rw[UInt32.toNat_sub,UInt32.toNat_ofNat',Nat.mod_eq_of_lt hn]
  have lt:=x.toNat_lt
  omega

theorem scratch_numbers(p:Layout)(hn:Native p):
    (scratch p).toNat=p.sp219.toNat-96 ∧(scratch p).toNat+96=p.sp219.toNat ∧
    (scratch p).toNat+96≤p.memory.byteSize ∧scratch p+96=p.sp219:=by
  have lo:=hn.spLower
  have eq:(scratch p).toNat=p.sp219.toNat-96:=sub_nat p.sp219 96 (by omega) (by omega)
  exact ⟨eq,by omega,by have b:=hn.spBound;omega,UInt32.sub_add_cancel _ _⟩

theorem scratch_add(p:Layout)(hn:Native p)(offset:Nat)(ho:offset<96):
    (scratch p+UInt32.ofNat offset).toNat=(scratch p).toNat+offset:=by
  have n:=scratch_numbers p hn
  have lt:=p.sp219.toNat_lt
  have off:offset<2^32:=by omega
  rw[UInt32.toNat_add,UInt32.toNat_ofNat',Nat.mod_eq_of_lt off]
  exact Nat.mod_eq_of_lt (by omega)

theorem scratch_aligned(p:Layout)(hn:Native p):(scratch p).toNat%16=0:=by
  have n:=scratch_numbers p hn
  have a:=hn.aligned
  omega

theorem callback_original_bound(p:Layout)(hn:Native p):
    1057480+4≤p.memory.byteSize ∧p.sp548.toNat≤1057480 ∧p.out548.toNat+12≤1057480:=by
  have n:=scratch_numbers p hn
  have a8:(scratch p+8).toNat=(scratch p).toNat+8:=scratch_add p hn 8 (by omega)
  have above:=hn.callbackAbove
  have bound:=hn.callbackBound
  rw[hn.storageSP,hn.storageOut,a8]
  omega
end WNear.Proofs.StateReadOuter
