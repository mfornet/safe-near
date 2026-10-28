import Proofs.StateDecodeRawCopyState
import Proofs.StateDecodeRawRecordResources
import Proofs.StateDecodeRawMemory

/-! Exact shadow-stack restoration through actual769, derived from original globals. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] allocated769 arguments769 reserved769 highCopied769 lowCopied769 after769 recordCallAfter actualPositive
private theorem paid_globals (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem globals_copy (s : Store NearState) (op i a b : Nat) (src dst : UInt32) (m : Memory) :
    (PanicAllocateCopy.copyStore s op i a b src dst m).globals=s.globals := by
  simp only [PanicAllocateCopy.copyStore,storeI32_globals,paid_globals]

theorem child_sp769 (p : Layout) (hn : Native p) : p.sp=scratch769 p := by
  have lo:=hn.spLower
  have hi:=p.spRaw.toNat_lt
  apply UInt32.toNat_inj.mp
  rw [(stack_numbers p hn).2.1,hn.childSP,UInt32.toNat_sub]
  simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
  omega

theorem arguments769_global (s : Store NearState) (op : Nat) (p : Layout) (hn : Native p)
    (hg : s.globals[p.globalIndex]?=some {p.globalRaw with value:=.i32 (scratch p)}) :
    (arguments769 s op p).globals[p.globalIndex]?=some p.global := by
  simp only [arguments769,reserved769,paid_globals,setGlobal,Array.getElem?_modify,hg,Option.map_some,ite_true]
  rw [hn.childGlobal,child_sp769 p hn]

theorem allocated769_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hg : s.globals[p.globalIndex]?=some {p.globalRaw with value:=.i32 (scratch p)}) :
    (allocated769 cfg s p).globals=(arguments769 s cfg.regularOpCost p).globals := by
  have gg : (arguments769 s cfg.regularOpCost p).globals[(actualPositive p).globalIndex]?=some (actualPositive p).global :=
    by
      rw [show (actualPositive p).globalIndex=p.globalIndex from by unfold actualPositive;rfl,show (actualPositive p).global=p.global from by unfold actualPositive;rfl]
      exact arguments769_global s cfg.regularOpCost p hn hg
  have hv : (actualPositive p).global.value=.i32 (actualPositive p).sp := by
    rw [show (actualPositive p).global=p.global from by unfold actualPositive;rfl,show (actualPositive p).sp=p.sp from by unfold actualPositive;rfl,hn.childGlobal]
  have h:=recordCallAfter_globals cfg (arguments769 s cfg.regularOpCost p) (actualPositive p) (out770 p) gg hv
  simpa only [allocated769] using h

theorem after769_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hg : s.globals[p.globalIndex]?=some {p.globalRaw with value:=.i32 (scratch p)}) :
    (after769 cfg s p).globals=s.globals := by
  have restore:=StorePairCaller.setGlobal_restore s p.globalIndex (.i32 (scratch769 p))
    {p.globalRaw with value:=.i32 (scratch p)} hg
  simp only [after769,setGlobal,paid_globals,highCopied769,lowCopied769,globals_copy,
    allocated769_globals cfg s p hn hg,arguments769,reserved769,paid_globals]
  exact restore
end WNear.Proofs.StateDecodeRaw
