import Binary.StateDecodeBorsh
import Proofs.StateDecodePrefixWrapperCall
import Proofs.StateDecodeScalarCall

/-! Original425 resources and exact accepted memory phases. Every saved word
is read at its deployed position in the sequential memory; user-output values
are cached before the first user-output write. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

structure Layout extends toPrefixWrapper:StateDecodePrefixWrapper.Layout where
  sp425:UInt32
  global425:GlobalInst
  out425:UInt32
  address315:Nat
  address372:Nat
  address371:Nat
  address694:Nat
  address710:Nat

def scratch(p:Layout):=p.sp425-96
def count(p:Layout):=StateDecodePrefix.count p.toPrefix

def prefixMemory(p:Layout)(q:StateDecodeVectorCopy.Layout):=StateDecodePrefixWrapper.finalMemory p.toPrefixWrapper q
def prefixPacked(p:Layout)(q:StateDecodeVectorCopy.Layout):=readI64 (prefixMemory p q) ((scratch p).toNat+60)
def prefixLength(p:Layout)(q:StateDecodeVectorCopy.Layout):=readI32 (prefixMemory p q) (scratch p+68).toNat
-- The length word is saved before the cached packed prefix word.
def prefixHighMemory(p:Layout)(q:StateDecodeVectorCopy.Layout):=writeI32 (prefixMemory p q) ((scratch p).toNat+24) (prefixLength p q)
def savedPrefixMemory(p:Layout)(q:StateDecodeVectorCopy.Layout):=writeI64 (prefixHighMemory p q) ((scratch p).toNat+16) (prefixPacked p q)

def wideLayout(p:Layout)(q:StateDecodeVectorCopy.Layout):StateDecodeScalar.Layout:=
  {mi:=p.mi,globalIndex:=p.globalIndex,memoryIndex:=p.memoryIndex,
   global:={p.global425 with value:=.i32 (scratch p)},memory:=savedPrefixMemory p q,sp:=scratch p,out:=scratch p+56,
   slice:=p.slice,pointer:=readI32 (savedPrefixMemory p q) p.slice.toNat,length:=readI32 (savedPrefixMemory p q) (p.slice.toNat+4),
   addressTake:=p.takeAddress,addressWord:=p.address694,addressDrop:=p.dropAddress}
def wideMemory(p:Layout)(q:StateDecodeVectorCopy.Layout):=StateDecodeScalar.finalMemory true (wideLayout p q)
-- Three actual copies, with each source read after the preceding destination write.
def wideFirstMemory(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  writeI64 (wideMemory p q) ((scratch p+32)+8).toNat (readI64 (wideMemory p q) (scratch p+68).toNat)
def wideSecondMemory(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  writeI32 (wideFirstMemory p q) (scratch p+48).toNat (readI32 (wideFirstMemory p q) (scratch p+76).toNat)
def savedWideMemory(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  writeI64 (wideSecondMemory p q) ((scratch p).toNat+32) (readI64 (wideSecondMemory p q) ((scratch p).toNat+60))
def wideHigh(p:Layout)(q:StateDecodeVectorCopy.Layout):=readI64 (savedWideMemory p q) ((scratch p+32)+12).toNat
def wideLow(p:Layout)(q:StateDecodeVectorCopy.Layout):=readI64 (savedWideMemory p q) ((scratch p).toNat+36)

def narrowLayout(p:Layout)(q:StateDecodeVectorCopy.Layout):StateDecodeScalar.Layout:=
  {mi:=p.mi,globalIndex:=p.globalIndex,memoryIndex:=p.memoryIndex,
   global:={p.global425 with value:=.i32 (scratch p)},memory:=savedWideMemory p q,sp:=scratch p,out:=scratch p+56,
   slice:=p.slice,pointer:=readI32 (savedWideMemory p q) p.slice.toNat,length:=readI32 (savedWideMemory p q) (p.slice.toNat+4),
   addressTake:=p.takeAddress,addressWord:=p.address710,addressDrop:=p.dropAddress}
def narrowMemory(p:Layout)(q:StateDecodeVectorCopy.Layout):=StateDecodeScalar.finalMemory false (narrowLayout p q)
def narrowHighMemory(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  writeI32 (narrowMemory p q) ((scratch p+80)+8).toNat (readI32 (narrowMemory p q) ((scratch p+56)+12).toNat)
def savedNarrowMemory(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  writeI64 (narrowHighMemory p q) ((scratch p).toNat+80) (readI64 (narrowHighMemory p q) ((scratch p).toNat+60))

def vectorLength(p:Layout)(q:StateDecodeVectorCopy.Layout):=readI32 (savedNarrowMemory p q) ((scratch p+16)+8).toNat
def vectorHighMemory(p:Layout)(q:StateDecodeVectorCopy.Layout):=writeI32 (savedNarrowMemory p q) (scratch p+8).toNat (vectorLength p q)
def vectorPacked(p:Layout)(q:StateDecodeVectorCopy.Layout):=readI64 (vectorHighMemory p q) ((scratch p).toNat+16)
def cachedMemory(p:Layout)(q:StateDecodeVectorCopy.Layout):=writeI64 (vectorHighMemory p q) (scratch p).toNat (vectorPacked p q)
def usageValue(p:Layout)(q:StateDecodeVectorCopy.Layout):=readI64 (cachedMemory p q) ((scratch p).toNat+84)

-- All five output values are local snapshots before the first write to out425.
def output16Memory(p:Layout)(q:StateDecodeVectorCopy.Layout):=writeI64 (cachedMemory p q) (p.out425+16).toNat (wideHigh p q)
def output8Memory(p:Layout)(q:StateDecodeVectorCopy.Layout):=writeI64 (output16Memory p q) (p.out425+8).toNat (wideLow p q)
def output24Memory(p:Layout)(q:StateDecodeVectorCopy.Layout):=writeI64 (output8Memory p q) (p.out425+24).toNat (usageValue p q)
def output32Memory(p:Layout)(q:StateDecodeVectorCopy.Layout):=writeI64 (output24Memory p q) (p.out425+32).toNat (vectorPacked p q)
def output40Memory(p:Layout)(q:StateDecodeVectorCopy.Layout):=writeI32 (output32Memory p q) (p.out425+40).toNat (vectorLength p q)
def finalMemory(p:Layout)(q:StateDecodeVectorCopy.Layout):=writeI32 (output40Memory p q) p.out425.toNat 0

structure Native(p:Layout):Prop where
  prefixNative:StateDecodePrefixWrapper.Native p.toPrefixWrapper
  childSP:p.wrapperSP=scratch p
  childOut:p.wrapperOut=scratch p+56
  childGlobal:p.wrapperGlobal={p.global425 with value:=.i32 (scratch p)}
  spLower:256≤p.sp425.toNat
  spBound:p.sp425.toNat≤p.memory.byteSize
  descriptorAbove:p.sp425.toNat≤p.slice.toNat
  sourceAbove:p.sp425.toNat≤p.pointer.toNat
  outAbove:p.sp425.toNat≤p.out425.toNat
  outBound:p.out425.toNat+44≤p.memory.byteSize
  headerBound:p.pointer.toNat+4+(count p).toNat+24≤p.memory.byteSize
  headerLength:4+(count p).toNat+24≤p.length.toNat
  descriptorHeaderSep:p.slice.toNat+8≤p.pointer.toNat ∨p.pointer.toNat+4+(count p).toNat+24≤p.slice.toNat

/-- Original allocation compatibility; no future scalar domain is a field. -/
structure AcceptedDomain(p:Layout)(q:StateDecodeVectorCopy.Layout):Prop extends StateDecodePrefix.AcceptedDomain p.toPrefix q where
  tagSeparation:p.out.toNat+4≤p.slice.toNat ∨p.slice.toNat+8≤p.out.toNat

end WNear.Proofs.StateDecodeBorsh
