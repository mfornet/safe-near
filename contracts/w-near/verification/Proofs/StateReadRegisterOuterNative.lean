import Proofs.StateReadRegisterOuterState

/-! Native523 premises describe only original words, spans and the original
allocation domain. Callee-native propositions are derived from these data. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384

structure Native (p : Layout) : Prop where
  allocation : AllocateZeroedRetry.Native p.toRecord.toZeroed
  vectorFlag : p.flag=0
  vectorSP : p.sp687=scratch p
  outerSP : p.outerSP=p.sp523-80
  childSP : p.sp=p.sp523-128
  childOut : p.out=p.sp+8
  vectorOut : p.out687=scratch p+32
  innerOut : p.out686=p.outerSP+8
  vectorGlobal : p.global687={p.global523 with value:=.i32 p.sp687}
  outerGlobal : p.outerGlobal={p.global523 with value:=.i32 p.outerSP}
  childGlobal : p.global={p.global523 with value:=.i32 p.sp}
  spLower : 144≤p.sp523.toNat
  spBound : p.sp523.toNat≤p.memory.byteSize
  aligned : p.sp523.toNat%16=0
  positive : 0<p.bytes.length
  sizeBound : p.bytes.length<2^31
  size : p.size=UInt32.ofNat p.bytes.length
  outputBound : p.out523.toNat+12≤p.memory.byteSize
  heapAbove : p.sp523.toNat≤p.allocator.toNat
  callbackAbove : p.sp523.toNat≤1057464+16
  staticAbove : p.sp523.toNat≤1055020
  interfaceBound : 1055020+4≤p.memory.byteSize
  interfaceRead : readI32 p.memory 1055020=p.lookupElement
  threadBound : 1074900+16≤p.memory.byteSize
  threadStatus : readI32 p.memory 1074900=1
  counterZero : readI32 p.memory 1074904=0
  receiverNonzero : readI32 p.memory 1074908≠0
  vtableRead : readI32 p.memory 1074912=p.dispatchVtable
  vtableAbove : p.sp523.toNat≤p.dispatchVtable.toNat
  vtableBeforeHeap : p.dispatchVtable.toNat+20≤p.allocator.toNat
  vtableBound : p.dispatchVtable.toNat+20≤p.memory.byteSize

theorem stack_numbers (p : Layout) (hn : Native p) :
    (scratch p).toNat=p.sp523.toNat-48 ∧
    (scratch p-16).toNat=p.sp523.toNat-64 ∧
    (scratch p-16-16).toNat=p.sp523.toNat-80 ∧
    (scratch p+8).toNat=p.sp523.toNat-40 ∧
    (scratch p+32).toNat=p.sp523.toNat-16 := by
  have lower := hn.spLower
  have upper := p.sp523.toNat_lt
  have a : (scratch p).toNat=p.sp523.toNat-48 := by
    rw [scratch,UInt32.toNat_sub]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod];omega
  have b : (scratch p-16).toNat=p.sp523.toNat-64 := by
    rw [UInt32.toNat_sub,a]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod];omega
  have c : (scratch p-16-16).toNat=p.sp523.toNat-80 := by
    rw [UInt32.toNat_sub,b]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod];omega
  have d : (scratch p+8).toNat=p.sp523.toNat-40 := by
    rw [UInt32.toNat_add,a]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod];omega
  have e : (scratch p+32).toNat=p.sp523.toNat-16 := by
    rw [UInt32.toNat_add,a]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod];omega
  exact ⟨a,b,c,d,e⟩

theorem Native.vector_original (p : Layout) (hn : Native p) : AllocateVectorOuter.Native p.toVectorOuter := by
  have nums := stack_numbers p hn
  have lower := hn.spLower
  have upper := p.sp523.toNat_lt
  have bound := hn.spBound
  have heap := hn.heapAbove
  have callback := hn.callbackAbove
  have spNat : p.sp687.toNat=p.sp523.toNat-48 := by rw [hn.vectorSP,nums.1]
  have outer : p.outerSP=p.sp687-32 := by
    apply UInt32.toNat_inj.mp
    rw [hn.outerSP,UInt32.toNat_sub,UInt32.toNat_sub,spNat]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod];omega
  have child : p.sp=p.sp687-80 := by
    apply UInt32.toNat_inj.mp
    rw [hn.childSP,UInt32.toNat_sub,UInt32.toNat_sub,spNat]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod];omega
  have outerGlobal : p.outerGlobal={p.global687 with value:=.i32 p.outerSP} := by
    rw [hn.vectorGlobal]
    exact hn.outerGlobal
  have childGlobal : p.global={p.global687 with value:=.i32 p.sp} := by
    rw [hn.vectorGlobal]
    exact hn.childGlobal
  have sizeBound : p.size.toNat<2^31 := by
    rw [hn.size]
    change p.bytes.length%2^32<2^31
    have sb := hn.sizeBound
    omega
  have outputBound : p.out687.toNat+12≤p.memory.byteSize := by rw [hn.vectorOut,nums.2.2.2.2];omega
  exact ⟨hn.allocation,outer,child,hn.childOut,outerGlobal,childGlobal,hn.innerOut,
    by omega,by omega,sizeBound,outputBound,by omega,by omega,by rw [hn.vectorFlag];rfl⟩
end WNear.Proofs.StateReadRegisterOuter
