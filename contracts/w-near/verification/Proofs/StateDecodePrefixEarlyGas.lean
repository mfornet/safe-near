import Proofs.StateDecodePrefixEarlyPhases
import Proofs.StateDecodeSlicesGas
import Proofs.StateDecodePrefixLeavesRecordResult

/-! Exact gas ledger of the actual316 prefix through its payload slice, before374. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_paid)
set_option maxRecDepth 16384
private theorem global_units (s : Store NearState) (op n i : Nat) (v : Value) :
    GasUnits s (setGlobal (paid s op n) i v) op n := (gasUnits_paid s op n).host_eq rfl
private theorem slice_units (drop : Bool) (s : Store NearState) (op index n : Nat) (m : Memory) (out ptr len split : UInt32) :
    GasUnits s (StateDecodeSlices.callAfter drop (paid s op n) op index m out ptr len split) op
      (n+(WNear.Binary.StateDecodeSlices.bodyCost drop+12)) :=
  (gasUnits_paid s op n).trans (StateDecodeSlices.callAfter_units drop (paid s op n) op index m out ptr len split)
private theorem take_units (cfg : WasmConfig) (s : Store NearState) (i : Nat) (m : Memory) (scratch ptr len : UInt32) :
    GasUnits s (takeAfter cfg s i m scratch ptr len) cfg.regularOpCost 30 := by
  simpa only [takeAfter,WNear.Binary.StateDecodeSlices.bodyCost,Bool.false_eq_true,ite_false,Nat.reduceAdd] using
    slice_units false s cfg.regularOpCost i 8 m (scratch+40) ptr len 4
private theorem word_units (cfg : WasmConfig) (s : Store NearState) :
    GasUnits s (wordAfter cfg s) cfg.regularOpCost 30 := by
  have callee : GasUnits (paid s cfg.regularOpCost 4) (StateDecodePrefixLeaves.wordCallAfter cfg (paid s cfg.regularOpCost 4)) cfg.regularOpCost 26 :=
    fun rest hc=>StateDecodePrefixLeaves.wordCallAfter_gas cfg (paid s cfg.regularOpCost 4) rest hc
  simpa only [wordAfter,Nat.reduceAdd] using (gasUnits_paid s cfg.regularOpCost 4).trans callee
private theorem drop_units (cfg : WasmConfig) (s : Store NearState) (i : Nat) (m : Memory) (scratch ptr len : UInt32) :
    GasUnits s (dropFourAfter cfg s i m scratch ptr len) cfg.regularOpCost 35 := by
  simpa only [dropFourAfter,WNear.Binary.StateDecodeSlices.bodyCost,ite_true,Nat.reduceAdd] using
    slice_units true s cfg.regularOpCost i 9 m (scratch+32) ptr len 4
private theorem advance_units (s : Store NearState) (op i : Nat) (m : Memory) (scratch slice : UInt32) :
    GasUnits s (advanceAfter s op i m scratch slice) op 4 := (gasUnits_paid s op 4).host_eq rfl
private theorem length_units (cfg : WasmConfig) (s : Store NearState) (i : Nat) (m : Memory) (scratch count : UInt32) :
    GasUnits s (lengthAfter cfg s i m scratch count) cfg.regularOpCost 20 := by
  have callee : GasUnits (paid s cfg.regularOpCost 4) (StateDecodePrefixLeaves.recordCallAfter cfg (paid s cfg.regularOpCost 4) i m (scratch+24) count) cfg.regularOpCost 16 :=
    fun rest hc=>StateDecodePrefixLeaves.recordCallAfter_gas cfg (paid s cfg.regularOpCost 4) i rest m (scratch+24) count hc
  simpa only [lengthAfter,Nat.reduceAdd] using (gasUnits_paid s cfg.regularOpCost 4).trans callee
attribute [local irreducible] reservedPrefix guardedPrefix takenPrefix wordPrefix statusPrefix droppedPrefix advancedPrefix
  countedPrefix lengthPrefix lengthCheckedPrefix enoughPrefix payloadPrefix

theorem reservedPrefix_gas (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (reservedPrefix s op p) op 5 := by
  unfold reservedPrefix;exact global_units s op 5 p.globalIndex (.i32 (scratch p))
theorem guardedPrefix_gas (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (guardedPrefix s op p) op 11 := by
  simpa only [guardedPrefix,Nat.reduceAdd] using (reservedPrefix_gas s op p).trans (gasUnits_paid (reservedPrefix s op p) op 6)
theorem takenPrefix_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (takenPrefix cfg s p) cfg.regularOpCost 41 := by
  simpa only [takenPrefix,Nat.reduceAdd,WNear.Binary.StateDecodeSlices.bodyCost,Bool.false_eq_true,ite_false] using
    (guardedPrefix_gas s cfg.regularOpCost p).trans (take_units cfg (guardedPrefix s cfg.regularOpCost p) p.memoryIndex p.memory (scratch p) p.pointer p.length)
theorem wordPrefix_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (wordPrefix cfg s p) cfg.regularOpCost 71 := by
  simpa only [wordPrefix,Nat.reduceAdd,WNear.Binary.StateDecodeSlices.bodyCost,Bool.false_eq_true,ite_false] using
    (takenPrefix_gas cfg s p).trans (word_units cfg (takenPrefix cfg s p))
theorem statusPrefix_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (statusPrefix cfg s p) cfg.regularOpCost 77 := by
  simpa only [statusPrefix,Nat.reduceAdd,WNear.Binary.StateDecodeSlices.bodyCost,Bool.false_eq_true,ite_false] using
    (wordPrefix_gas cfg s p).trans (gasUnits_paid (wordPrefix cfg s p) cfg.regularOpCost 6)
theorem droppedPrefix_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (droppedPrefix cfg s p) cfg.regularOpCost 112 := by
  simpa only [droppedPrefix,Nat.reduceAdd,WNear.Binary.StateDecodeSlices.bodyCost,Bool.false_eq_true,ite_false] using
    (statusPrefix_gas cfg s p).trans (drop_units cfg (statusPrefix cfg s p) p.memoryIndex (takenFourMemory p) (scratch p) p.pointer p.length)
theorem advancedPrefix_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (advancedPrefix cfg s p) cfg.regularOpCost 116 := by
  simpa only [advancedPrefix,Nat.reduceAdd,WNear.Binary.StateDecodeSlices.bodyCost,Bool.false_eq_true,ite_false] using
    (droppedPrefix_gas cfg s p).trans (advance_units (droppedPrefix cfg s p) cfg.regularOpCost p.memoryIndex (droppedFourMemory p) (scratch p) p.slice)
theorem countedPrefix_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (countedPrefix cfg s p) cfg.regularOpCost 122 := by
  simpa only [countedPrefix,Nat.reduceAdd,WNear.Binary.StateDecodeSlices.bodyCost,Bool.false_eq_true,ite_false] using
    (advancedPrefix_gas cfg s p).trans (gasUnits_paid (advancedPrefix cfg s p) cfg.regularOpCost 6)
theorem lengthPrefix_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (lengthPrefix cfg s p) cfg.regularOpCost 142 := by
  simpa only [lengthPrefix,Nat.reduceAdd,WNear.Binary.StateDecodeSlices.bodyCost,Bool.false_eq_true,ite_false] using
    (countedPrefix_gas cfg s p).trans (length_units cfg (countedPrefix cfg s p) p.memoryIndex (advancedMemory p) (scratch p) (count p))
theorem lengthCheckedPrefix_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (lengthCheckedPrefix cfg s p) cfg.regularOpCost 145 := by
  simpa only [lengthCheckedPrefix,Nat.reduceAdd,WNear.Binary.StateDecodeSlices.bodyCost,Bool.false_eq_true,ite_false] using
    (lengthPrefix_gas cfg s p).trans (gasUnits_paid (lengthPrefix cfg s p) cfg.regularOpCost 3)
theorem enoughPrefix_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (enoughPrefix cfg s p) cfg.regularOpCost 153 := by
  simpa only [enoughPrefix,Nat.reduceAdd,WNear.Binary.StateDecodeSlices.bodyCost,Bool.false_eq_true,ite_false] using
    (lengthCheckedPrefix_gas cfg s p).trans (gasUnits_paid (lengthCheckedPrefix cfg s p) cfg.regularOpCost 8)
theorem payloadPrefix_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (payloadPrefix cfg s p) cfg.regularOpCost 183 := by
  simpa only [payloadPrefix,Nat.reduceAdd,WNear.Binary.StateDecodeSlices.bodyCost,Bool.false_eq_true,ite_false] using
    (enoughPrefix_gas cfg s p).trans (slice_units false (enoughPrefix cfg s p) cfg.regularOpCost p.memoryIndex 8 (lengthMemory p) (takePayloadOut p) (payloadPointer p) (remaining p) (count p))
end WNear.Proofs.StateDecodePrefix
