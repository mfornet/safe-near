import Proofs.DeallocateCoreHead

/-! Original pure domain for582's previous-allocated, next-disabled insertion
branch. The existing previous-free coalescing domain is deliberately separate. -/
namespace WNear.Proofs.DeallocateInsert
open Wasm Wasm.Near MeteredLogic DeallocateCore

structure Native(p:DeallocateCore.Layout):Prop where
  wf:p.memory.wf
  pointerNonzero:p.pointer≠0
  lengthNonzero:p.length≠0
  lengthBound:p.length.toNat+4<2^32
  headerEq:p.pointer+4294967288=p.header
  previousAddressEq:p.pointer+4294967292=p.previousAddress
  allocatorBound:p.allocator.toNat+4≤p.memory.byteSize
  headerBound:p.header.toNat+4≤p.memory.byteSize
  pointerBound:p.pointer.toNat+4≤p.memory.byteSize
  currentSize:p.header.toNat+8≤(DeallocateListSize.endWord (markedMemory p) p.header).toNat
  previousAddressBound:p.previousAddress.toNat+4≤(zeroMemory p).byteSize
  previousRead:Deallocate.previous (zeroMemory p) p.previousAddress=p.previous
  previousNonzero:p.previous≠0
  previousBound:p.previous.toNat+1≤(zeroMemory p).byteSize
  previousAllocated:readByteWord (zeroMemory p) p.previous.toNat &&&1≠0
  nextWordBound:p.header.toNat+4≤(zeroMemory p).byteSize
  nextAddressNonzero:readI32 (zeroMemory p) p.header.toNat &&&4294967292≠0
  nextDisabled:readI32 (zeroMemory p) p.header.toNat &&&2≠0

structure Ready(s:Store NearState)(frame:CallFrame)(p:DeallocateCore.Layout):Prop where
  code:DeallocateCore.Code s frame.inst p
  memory:s.mems[p.memoryIndex]?=some p.memory
  allocator:frame.locals[0]?=some (.i32 p.allocator)
  pointer:frame.locals[1]?=some (.i32 p.pointer)
  length:frame.locals[2]?=some (.i32 p.length)
  alignment:frame.locals[3]?=some (.i32 p.alignment)
  locals:7≤frame.locals.size
  native:Native p
end WNear.Proofs.DeallocateInsert
