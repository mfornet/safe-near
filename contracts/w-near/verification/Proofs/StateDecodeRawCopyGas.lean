import Proofs.StateDecodeRawCopyState
import Proofs.StateDecodeRawRecordResources

/-! Exact ordinary costs of769's actual allocation and sequential copies. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_paid gasUnits_charge)
set_option maxRecDepth 16384
private theorem global_units (s : Store NearState) (op n i : Nat) (v : Value) :
    GasUnits s (setGlobal (paid s op n) i v) op n := (gasUnits_paid s op n).host_eq rfl
private theorem copy_units (s : Store NearState) (op i a b : Nat) (src dst : UInt32) (m : Memory) :
    GasUnits s (PanicAllocateCopy.copyStore s op i a b src dst m) op 4 := (gasUnits_paid s op 4).host_eq rfl
attribute [local irreducible] reserved769 arguments769 allocated769 lowCopied769 highCopied769 after769

theorem reserved769_gas (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (reserved769 s op p) op 5 := by
  simpa only [reserved769,Nat.reduceAdd] using
    global_units s op 5 p.globalIndex (.i32 (scratch769 p))
theorem arguments769_gas (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (arguments769 s op p) op 11 := by
  simpa only [arguments769,Nat.reduceAdd] using
    (reserved769_gas s op p).trans (gasUnits_paid (reserved769 s op p) op 6)
theorem allocated769_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (allocated769 cfg s p) cfg.regularOpCost 424 := by
  simpa only [allocated769,Nat.reduceAdd] using
    (arguments769_gas s cfg.regularOpCost p).trans
    (recordCallAfter_gas cfg (arguments769 s cfg.regularOpCost p) (actualPositive p) (out770 p))
theorem lowCopied769_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (lowCopied769 cfg s p) cfg.regularOpCost 428 := by
  simpa only [lowCopied769,Nat.reduceAdd] using
    (allocated769_gas cfg s p).trans (copy_units (allocated769 cfg s p) cfg.regularOpCost p.memoryIndex 8 0
    (scratch769 p) (scratch p+16) (memory770 p))
theorem highCopied769_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (highCopied769 cfg s p) cfg.regularOpCost 432 := by
  simpa only [highCopied769,Nat.reduceAdd] using
    (lowCopied769_gas cfg s p).trans (copy_units (lowCopied769 cfg s p) cfg.regularOpCost p.memoryIndex 12 4
    (scratch769 p) (scratch p+16) (lowMemory769 p))
theorem after769_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (after769 cfg s p) cfg.regularOpCost 436 := by
  simpa only [after769,Nat.reduceAdd] using
    (highCopied769_gas cfg s p).trans (global_units (highCopied769 cfg s p) cfg.regularOpCost 4 p.globalIndex (.i32 (scratch p)))
theorem callAfter769_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (callAfter769 cfg s p) cfg.regularOpCost 447 := by
  have one:=gasUnits_charge s cfg.regularOpCost 1
  simp only [Nat.one_mul] at one
  have enter : GasUnits s (entered769 s cfg.regularOpCost) cfg.regularOpCost 11 :=
    one.trans (gasUnits_charge (chargedStore s cfg.regularOpCost) cfg.regularOpCost 10)
  exact enter.trans (after769_gas cfg (entered769 s cfg.regularOpCost) p)
end WNear.Proofs.StateDecodeRaw
