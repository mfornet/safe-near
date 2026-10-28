import Proofs.StateDecodePrefixEarlyPhases
import Proofs.StateDecodePrefixNative
import Proofs.StateDecodeSlicesResult
import Proofs.StateDecodePrefixLeavesWordResult
import Proofs.StateDecodePrefixLeavesRecordResult

/-! Actual memory snapshots for the accepted316 prefix; payment changes no memory. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem mems_global (s : Store NearState) (i : Nat) (v : Value) : (setGlobal s i v).mems=s.mems := rfl
attribute [local irreducible] paid setGlobal StateDecodeSlices.callAfter StateDecodePrefixLeaves.wordCallAfter StateDecodePrefixLeaves.recordCallAfter storeI64 readI64

theorem guardedPrefix_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (guardedPrefix s cfg.regularOpCost p).mems[p.memoryIndex]?=some p.memory := by
  simpa only[guardedPrefix,reservedPrefix,mems_paid,mems_global] using hm

theorem takenPrefix_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (takenPrefix cfg s p).mems[p.memoryIndex]?=some (takenFourMemory p) := by
  have h:=guardedPrefix_memory cfg s p hm
  have hp:(paid (guardedPrefix s cfg.regularOpCost p) cfg.regularOpCost 8).mems[p.memoryIndex]?=some p.memory:=by rw[mems_paid];exact h
  exact StateDecodeSlices.callAfter_memory false _ _ _ _ _ _ _ _ hp

theorem wordPrefix_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (wordPrefix cfg s p).mems[p.memoryIndex]?=some (takenFourMemory p) := by
  have h:=takenPrefix_memory cfg s p hm
  have hp:(paid (takenPrefix cfg s p) cfg.regularOpCost 4).mems[p.memoryIndex]?=some (takenFourMemory p):=by rw[mems_paid];exact h
  exact StateDecodePrefixLeaves.wordCallAfter_memory cfg _ _ _ hp

theorem statusPrefix_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (statusPrefix cfg s p).mems[p.memoryIndex]?=some (takenFourMemory p) := by
  simpa only[statusPrefix,mems_paid] using wordPrefix_memory cfg s p hm

theorem droppedPrefix_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (droppedPrefix cfg s p).mems[p.memoryIndex]?=some (droppedFourMemory p) := by
  have h:=statusPrefix_memory cfg s p hm
  have hp:(paid (statusPrefix cfg s p) cfg.regularOpCost 9).mems[p.memoryIndex]?=some (takenFourMemory p):=by rw[mems_paid];exact h
  exact StateDecodeSlices.callAfter_memory true _ _ _ _ _ _ _ _ hp

theorem advancedPrefix_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hn : Native p) :
    (advancedPrefix cfg s p).mems[p.memoryIndex]?=some (advancedMemory p) := by
  have h:=droppedPrefix_memory cfg s p hm
  have hp:(paid (droppedPrefix cfg s p) cfg.regularOpCost 4).mems[p.memoryIndex]?=some (droppedFourMemory p):=by rw[mems_paid];exact h
  have result:=storeI64_memory _ p.memoryIndex p.slice.toNat (droppedFourMemory p)
    (readI64 (droppedFourMemory p) ((scratch p).toNat+32)) hp
  have add:(dropFourOut p).toNat=(scratch p).toNat+32:=scratch_add p hn 32 (by omega)
  simpa only[advancedPrefix,advanceAfter,advancedMemory,advancedPacked,add] using result

theorem countedPrefix_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hn : Native p) :
    (countedPrefix cfg s p).mems[p.memoryIndex]?=some (advancedMemory p) := by
  simpa only[countedPrefix,mems_paid] using advancedPrefix_memory cfg s p hm hn

theorem lengthPrefix_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hn : Native p) :
    (lengthPrefix cfg s p).mems[p.memoryIndex]?=some (lengthMemory p) := by
  have h:=countedPrefix_memory cfg s p hm hn
  have hp:(paid (countedPrefix cfg s p) cfg.regularOpCost 4).mems[p.memoryIndex]?=some (advancedMemory p):=by rw[mems_paid];exact h
  exact StateDecodePrefixLeaves.recordCallAfter_memory cfg _ _ _ _ _ hp

theorem lengthCheckedPrefix_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hn : Native p) :
    (lengthCheckedPrefix cfg s p).mems[p.memoryIndex]?=some (lengthMemory p) := by
  simpa only[lengthCheckedPrefix,mems_paid] using lengthPrefix_memory cfg s p hm hn

theorem enoughPrefix_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hn : Native p) :
    (enoughPrefix cfg s p).mems[p.memoryIndex]?=some (lengthMemory p) := by
  simpa only[enoughPrefix,mems_paid] using lengthCheckedPrefix_memory cfg s p hm hn

theorem payloadPrefix_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hn : Native p) :
    (payloadPrefix cfg s p).mems[p.memoryIndex]?=some (takenPayloadMemory p) := by
  have h:=enoughPrefix_memory cfg s p hm hn
  have hp:(paid (enoughPrefix cfg s p) cfg.regularOpCost 8).mems[p.memoryIndex]?=some (lengthMemory p):=by rw[mems_paid];exact h
  exact StateDecodeSlices.callAfter_memory false _ _ _ _ _ _ _ _ hp
end WNear.Proofs.StateDecodePrefix
