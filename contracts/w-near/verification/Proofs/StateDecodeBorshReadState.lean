import Proofs.StateDecodeBorshWrapperNative
import Binary.StateDecodeBorshRead

/-! Original161 byte-slice inputs. Its descriptor is constructed by the actual
length-then-pointer stores; future decoder domains are not assumptions. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
structure Layout extends toWrapper:StateDecodeBorshWrapper.Layout where
  sp161:UInt32
  global161:GlobalInst
  out161:UInt32
  address162:Nat

def scratch(p:Layout):=p.sp161-144
def count(p:Layout):=StateDecodeBorshWrapper.count p.toWrapper

def highSetupMemory(p:Layout):=writeI32 p.memory ((scratch p).toNat+12) p.length
def setupMemory(p:Layout):=writeI32 (highSetupMemory p) ((scratch p).toNat+8) p.pointer

def actualWrapper(p:Layout):StateDecodeBorshWrapper.Layout:=
  {p.toWrapper with toBorsh:={p.toBorsh with toPrefixWrapper:={p.toPrefixWrapper with
    toPrefix:={p.toPrefix with memory:=setupMemory p}}}}
def actualAllocation(p:Layout)(q:StateDecodeVectorCopy.Layout):StateDecodeVectorCopy.Layout:=
  {q with toVector:={q.toVector with toRaw:={q.toRaw with toPositive:={q.toPositive with memory:=setupMemory p}}}}

/-- Bounds and static stack relationships on the original161 input only. -/
structure Native(p:Layout):Prop where
  wf:p.memory.wf
  width:p.memory.byteSize≤2^32
  spLower:496≤p.sp161.toNat
  spBound:p.sp161.toNat≤p.memory.byteSize
  spAligned:p.sp161.toNat%16=0
  outBound:p.out161.toNat+48≤p.memory.byteSize
  sourceAbove:p.sp161.toNat≤p.pointer.toNat
  headerBound:p.pointer.toNat+4+(count p).toNat+24≤p.memory.byteSize
  headerLength:4+(count p).toNat+24≤p.length.toNat
  countPositive:count p≠0
  countSigned:(count p).toNat<2^31
  slice:p.slice=scratch p+8
  wrapperSP:p.sp162=scratch p
  wrapperOut:p.out162=scratch p+96
  wrapperGlobal:p.global162={p.global161 with value:=.i32 (scratch p)}
  borshSP:p.sp425=StateDecodeBorshWrapper.scratch p.toWrapper
  borshOut:p.out425=StateDecodeBorshWrapper.scratch p.toWrapper+48
  borshGlobal:p.global425={p.global162 with value:=.i32 (StateDecodeBorshWrapper.scratch p.toWrapper)}
  prefixSP:p.wrapperSP=StateDecodeBorsh.scratch p.toBorsh
  prefixOut:p.wrapperOut=StateDecodeBorsh.scratch p.toBorsh+56
  prefixGlobal:p.wrapperGlobal={p.global425 with value:=.i32 (StateDecodeBorsh.scratch p.toBorsh)}
  childSP:p.sp=StateDecodePrefixWrapper.scratch p.toPrefixWrapper
  childOut:p.out=StateDecodePrefixWrapper.scratch p.toPrefixWrapper
  childGlobal:p.global={p.wrapperGlobal with value:=.i32 (StateDecodePrefixWrapper.scratch p.toPrefixWrapper)}

/-- The allocated-vector template is valid on the ORIGINAL memory. The setup
transport must prove its future domain, rather than requiring that domain here. -/
structure AllocationDomain(p:Layout)(q:StateDecodeVectorCopy.Layout):Prop where
  original:StateDecodeVectorCopy.Native q
  memory:q.memory=p.memory
  size:q.size=count p
  sp:q.spVector=StateDecodePrefix.scratch p.toPrefix
  out:q.outVector=StateDecodePrefix.allocatedOut p.toPrefix
  source:q.source=StateDecodePrefix.payloadPointer p.toPrefix
  allocatorAbove:p.sp161.toNat≤q.allocator.toNat
  headAbove:p.sp161.toNat≤(AllocateSearch.head (AllocatePositive.searchLayout q.toPositive)).toNat
  callbackAbove:p.sp161.toNat≤1057464
end WNear.Proofs.StateDecodeBorshRead
