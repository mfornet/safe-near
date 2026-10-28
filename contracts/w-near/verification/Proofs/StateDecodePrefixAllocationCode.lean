import Proofs.StateDecodePrefixAllocationBridge
import Proofs.StateDecodePrefixEarlyFrame
import Proofs.StateDecodeRawRecordTransport

/-! Actual allocator callback selection survives316's prefix under explicit
original selector/descriptor separation. All installed code addresses are kept. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] readI32 readI64 writeI64 takenPayloadMemory lengthMemory advancedMemory droppedFourMemory takenFourMemory

/-- Derive the actual memory-dependent allocator code from the original code. -/
theorem allocation_positive_code (s : Store NearState) (inst : Nat) (p : Layout)
    (q : StateDecodeVectorCopy.Layout) (a581 a236 : Nat) (hn : Native p) (hd : AllocationDomain p q)
    (hc : StateDecodeVectorCopy.Code s inst q a581 a236)
    (hcallback : p.sp.toNat≤1057464+16)
    (hsep : 1057464+20≤p.slice.toNat ∨p.slice.toNat+8≤1057464+16) :
    AllocatePositive.Code s inst (allocationInput p q).toPositive := by
  have original:=hc.vector.raw.record.allocation
  refine ⟨?_,original.globalIndex,original.alignIndex,original.alignFunction,
    original.roundIndex,original.roundFunction,original.searchIndex,original.searchFunction⟩
  refine {module:=original.search.module,memoryIndex:=original.search.memoryIndex, tableIndex:=original.search.tableIndex,table:=original.search.table,callbackElement:=?_, callbackType:=original.search.callbackType,callbackFunction:=original.search.callbackFunction, unitsIndex:=original.search.unitsIndex,unitsFunction:=original.search.unitsFunction, minimumIndex:=original.search.minimumIndex,minimumFunction:=original.search.minimumFunction, sizeIndex:=original.search.sizeIndex,sizeFunction:=original.search.sizeFunction}
  change q.table.elems[(readI32 (AllocatePositive.savedMemory (allocationInput p q).toPositive) (1057464+16)).toNat]?=some (.func q.callbackAddress)
  rw[allocation_saved_word p q hn hd (1057464+16) hcallback hsep]
  exact original.search.callbackElement

theorem allocation_copy_code (s : Store NearState) (inst : Nat) (p : Layout)
    (q : StateDecodeVectorCopy.Layout) (a581 a236 : Nat) (hn : Native p) (hd : AllocationDomain p q)
    (hc : StateDecodeVectorCopy.Code s inst q a581 a236)
    (hcallback : p.sp.toNat≤1057464+16)
    (hsep : 1057464+20≤p.slice.toNat ∨p.slice.toNat+8≤1057464+16) :
    StateDecodeVectorCopy.Code s inst (allocationInput p q) a581 a236 := by
  have positive:=allocation_positive_code s inst p q a581 a236 hn hd hc hcallback hsep
  have record:StateDecodeRaw.RecordCode s inst (allocationInput p q).toPositive a581 a236 q.address310 :=
    ⟨positive,hc.vector.raw.record.index581,hc.vector.raw.record.function581,
      hc.vector.raw.record.index236,hc.vector.raw.record.function236,
      hc.vector.raw.record.index310,hc.vector.raw.record.function310⟩
  have raw:StateDecodeRaw.Code s inst (allocationInput p q).toRaw a581 a236 :=
    ⟨record,hc.vector.raw.index751,hc.vector.raw.function751,hc.vector.raw.index752,hc.vector.raw.function752,
      hc.vector.raw.index769,hc.vector.raw.function769,hc.vector.raw.index770,hc.vector.raw.function770⟩
  have vector:StateDecodeVector.Code s inst (allocationInput p q).toVector a581 a236 :=
    ⟨raw,hc.vector.index767,hc.vector.function767⟩
  exact ⟨vector,hc.index373,hc.function373,hc.index951,hc.function951⟩

/-- Pure installed-code transport; this changes no memory-domain premise. -/
theorem allocation_copy_code_transport (s t : Store NearState) (inst : Nat)
    (q : StateDecodeVectorCopy.Layout) (a581 a236 : Nat)
    (hc : StateDecodeVectorCopy.Code s inst q a581 a236)
    (hf : t.funcs=s.funcs) (hm : t.modules=s.modules) (ht : t.tables=s.tables) :
    StateDecodeVectorCopy.Code t inst q a581 a236 := by
  have record:=StateDecodeRaw.RecordCode.transport s t inst q.toPositive a581 a236 q.address310
    hc.vector.raw.record hf hm ht
  have raw:StateDecodeRaw.Code t inst q.toRaw a581 a236:=by
    refine {hc.vector.raw with record:=record,function751:=?_,function752:=?_,function769:=?_,function770:=?_}
    · rw[hf];exact hc.vector.raw.function751
    · rw[hf];exact hc.vector.raw.function752
    · rw[hf];exact hc.vector.raw.function769
    · rw[hf];exact hc.vector.raw.function770
  have vector:StateDecodeVector.Code t inst q.toVector a581 a236:=by
    refine {hc.vector with raw:=raw,function767:=?_}
    rw[hf];exact hc.vector.function767
  refine {hc with vector:=vector,function373:=?_,function951:=?_}
  · rw[hf];exact hc.function373
  · rw[hf];exact hc.function951

private theorem paid_funcs (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem paid_modules (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem paid_tables (s : Store NearState) (op n : Nat) : (paid s op n).tables=s.tables := by
  induction n with | zero=>rfl | succ n ih=>exact ih

theorem allocation_copy_code_paid (s : Store NearState) (op n inst : Nat)
    (q : StateDecodeVectorCopy.Layout) (a581 a236 : Nat)
    (hc : StateDecodeVectorCopy.Code s inst q a581 a236) :
    StateDecodeVectorCopy.Code (paid s op n) inst q a581 a236 :=
  allocation_copy_code_transport s (paid s op n) inst q a581 a236 hc
    (paid_funcs s op n) (paid_modules s op n) (paid_tables s op n)

theorem payloadPrefix_allocation_code (cfg : WasmConfig) (s : Store NearState) (inst : Nat) (p : Layout)
    (q : StateDecodeVectorCopy.Layout) (a581 a236 : Nat) (hn : Native p) (hd : AllocationDomain p q)
    (hc : StateDecodeVectorCopy.Code s inst q a581 a236)
    (hcallback : p.sp.toNat≤1057464+16)
    (hsep : 1057464+20≤p.slice.toNat ∨p.slice.toNat+8≤1057464+16) :
    StateDecodeVectorCopy.Code (payloadPrefix cfg s p) inst (allocationInput p q) a581 a236 := by
  have code:=allocation_copy_code s inst p q a581 a236 hn hd hc hcallback hsep
  have fields:=payloadPrefix_fields cfg s p
  exact allocation_copy_code_transport s (payloadPrefix cfg s p) inst (allocationInput p q) a581 a236
    code fields.1 fields.2.1 fields.2.2.1
end WNear.Proofs.StateDecodePrefix
