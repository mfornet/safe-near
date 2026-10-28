import Proofs.StateDecodeRawCopyState
import Proofs.StateDecodeRawRecordResources
import Proofs.StateDecodeRawMemory

/-! Real769 resources through allocation and its two sequential word copies. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_globals (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_funcs (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_modules (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_tables (s : Store NearState) (op n : Nat) : (paid s op n).tables=s.tables := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem globals_copy (s : Store NearState) (op i a b : Nat) (src dst : UInt32) (m : Memory) :
    (PanicAllocateCopy.copyStore s op i a b src dst m).globals=s.globals := by
  simp only [PanicAllocateCopy.copyStore,storeI32_globals,paid_globals]
private theorem copy_memory (s : Store NearState) (op i a b : Nat) (src dst : UInt32) (m : Memory)
    (hm : s.mems[i]?=some m) :
    (PanicAllocateCopy.copyStore s op i a b src dst m).mems[i]?=
      some (writeI32 m (dst.toNat+b) (readI32 m (src.toNat+a))) := by
  unfold PanicAllocateCopy.copyStore
  apply storeI32_memory
  rw [paid_mems];exact hm

attribute [local irreducible] recordCallAfter arguments769 reserved769 allocated769 lowCopied769 highCopied769
  memory770 lowMemory769 memory769 laidOutMemory AllocatePositive.finalMemory PanicAllocateCopy.copyStore

theorem arguments769_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (arguments769 s op p).funcs=s.funcs ∧ (arguments769 s op p).modules=s.modules ∧ (arguments769 s op p).tables=s.tables := by
  simp only [arguments769,reserved769,setGlobal,paid_funcs,paid_modules,paid_tables,and_self]

theorem allocated769_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (allocated769 cfg s p).funcs=s.funcs ∧ (allocated769 cfg s p).modules=s.modules ∧ (allocated769 cfg s p).tables=s.tables := by
  have h:=recordCallAfter_fields cfg (arguments769 s cfg.regularOpCost p) (actualPositive p) (out770 p)
  have a:=arguments769_fields s cfg.regularOpCost p
  unfold allocated769
  exact ⟨h.1.trans a.1,h.2.1.trans a.2.1,h.2.2.trans a.2.2⟩

private theorem copy_fields (s : Store NearState) (op i a b : Nat) (src dst : UInt32) (m : Memory) :
    (PanicAllocateCopy.copyStore s op i a b src dst m).funcs=s.funcs ∧
    (PanicAllocateCopy.copyStore s op i a b src dst m).modules=s.modules ∧
    (PanicAllocateCopy.copyStore s op i a b src dst m).tables=s.tables := by
  simp only [PanicAllocateCopy.copyStore,storeI32_funcs,storeI32_modules,storeI32_tables,paid_funcs,paid_modules,paid_tables,and_self]

theorem after769_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (after769 cfg s p).funcs=s.funcs ∧ (after769 cfg s p).modules=s.modules ∧ (after769 cfg s p).tables=s.tables := by
  have a:=allocated769_fields cfg s p
  have l:=copy_fields (allocated769 cfg s p) cfg.regularOpCost p.memoryIndex 8 0 (scratch769 p) (scratch p+16) (memory770 p)
  have h:=copy_fields (lowCopied769 cfg s p) cfg.regularOpCost p.memoryIndex 12 4 (scratch769 p) (scratch p+16) (lowMemory769 p)
  unfold after769
  simp only [setGlobal,paid_funcs,paid_modules,paid_tables]
  unfold highCopied769
  rw [h.1,h.2.1,h.2.2]
  unfold lowCopied769
  exact ⟨l.1.trans a.1,l.2.1.trans a.2.1,l.2.2.trans a.2.2⟩

theorem arguments769_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some (laidOutMemory p)) :
    (arguments769 s op p).mems[p.memoryIndex]?=some (laidOutMemory p) := by
  simp only [arguments769,reserved769,paid_mems,setGlobal]
  exact hm

theorem allocated769_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some (laidOutMemory p)) :
    (allocated769 cfg s p).mems[p.memoryIndex]?=some (memory770 p) := by
  unfold allocated769
  have m:=recordCallAfter_memory cfg (arguments769 s cfg.regularOpCost p) (actualPositive p) (out770 p)
    (arguments769_memory s cfg.regularOpCost p hm)
  simpa only [memory770,highMemory770,allocatedMemory,result,show (actualPositive p).memoryIndex=p.memoryIndex from rfl,show (actualPositive p).size=p.size from rfl] using m

private theorem copy_addresses (p : Layout) (hn : Native p) :
    (scratch769 p).toNat+8=(out770 p).toNat ∧ (scratch769 p).toNat+12=(out770 p).toNat+4 := by
  have n:=stack_numbers p hn
  have r:=record_numbers p hn
  have lo:=hn.spLower
  rw[n.2.1,r.1]
  omega

theorem lowCopied769_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hm : s.mems[p.memoryIndex]?=some (laidOutMemory p)) :
    (lowCopied769 cfg s p).mems[p.memoryIndex]?=some (lowMemory769 p) := by
  have m:=copy_memory (allocated769 cfg s p) cfg.regularOpCost p.memoryIndex 8 0
    (scratch769 p) (scratch p+16) (memory770 p) (allocated769_memory cfg s p hm)
  simpa only [lowCopied769,lowMemory769,Nat.add_zero,(copy_addresses p hn).1] using m

theorem highCopied769_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hm : s.mems[p.memoryIndex]?=some (laidOutMemory p)) :
    (highCopied769 cfg s p).mems[p.memoryIndex]?=some (memory769 p) := by
  have m:=copy_memory (lowCopied769 cfg s p) cfg.regularOpCost p.memoryIndex 12 4
    (scratch769 p) (scratch p+16) (lowMemory769 p) (lowCopied769_memory cfg s p hn hm)
  simpa only [highCopied769,memory769,(copy_addresses p hn).2] using m

theorem after769_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hm : s.mems[p.memoryIndex]?=some (laidOutMemory p)) :
    (after769 cfg s p).mems[p.memoryIndex]?=some (memory769 p) := by
  simpa only [after769,setGlobal,paid_mems] using highCopied769_memory cfg s p hn hm

end WNear.Proofs.StateDecodeRaw
