import Proofs.StateDecodeVectorCopyCall
import Proofs.StateDecodeVectorResult
import Proofs.UnwrapStateCopyGas

/-! Exact gas for actual374, including each real forward-copy loop iteration. -/
namespace WNear.Proofs.StateDecodeVectorCopy
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_paid gasUnits_charge)
set_option maxRecDepth 16384
private theorem loop_units (s : Store NearState) (op i : Nat) (out src : UInt32) (m : Memory) (n : Nat) :
    GasUnits s (UnwrapStateCopy.loopStore s op i out src m n) op (18*n-1) := by
  intro rest hc
  have gas:=UnwrapStateCopyGas.loopStore_gas s op i out src m n rest hc
  exact ⟨gas.1,gas.2,UnwrapStateCopyState.loopStore_credits s op i out src m n rest hc⟩
private theorem memcpy_units (s : Store NearState) (op i : Nat) (out src : UInt32) (m : Memory) (n : Nat) (hn : 0<n) :
    GasUnits s (UnwrapStateCopyEntry.callAfter s op i out src m n) op (18*n+17) := by
  have one:=gasUnits_charge s op 1
  simp only [Nat.one_mul] at one
  have enter : GasUnits s (UnwrapStateCopyEntry.calledStore s op) op 11 :=
    one.trans (gasUnits_charge (chargedStore s op) op 10)
  have prep : GasUnits (UnwrapStateCopyEntry.calledStore s op) (UnwrapStateCopyEntry.prepared (UnwrapStateCopyEntry.calledStore s op) op) op 6 := by
    simpa only [UnwrapStateCopyEntry.prepared,Nat.reduceAdd,Nat.one_mul] using
      (gasUnits_paid (UnwrapStateCopyEntry.calledStore s op) op 5).trans (gasUnits_charge (paid (UnwrapStateCopyEntry.calledStore s op) op 5) op 1)
  have loop:=loop_units (UnwrapStateCopyEntry.prepared (UnwrapStateCopyEntry.calledStore s op) op) op i out src m n
  have ret:=gasUnits_charge (UnwrapStateCopy.loopStore (UnwrapStateCopyEntry.prepared (UnwrapStateCopyEntry.calledStore s op) op) op i out src m n) op 1
  have ledger : 11+6+(18*n-1)+1=18*n+17 := by omega
  simpa only [UnwrapStateCopyEntry.callAfter,UnwrapStateCopyEntry.finalStore,Nat.one_mul,ledger] using ((enter.trans prep).trans loop).trans ret
private theorem finish_units (s : Store NearState) (op i : Nat) (m : Memory) (out size : UInt32) :
    GasUnits s (finishStore s op i m out size) op 4 := (gasUnits_paid s op 4).host_eq rfl
attribute [local irreducible] vectorBefore vectorAfter copyArguments copied after entered callAfter

theorem vectorAfter_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (vectorAfter cfg s p) cfg.regularOpCost 622 := by
  simpa only [vectorAfter,vectorBefore,Nat.reduceAdd] using (gasUnits_paid s cfg.regularOpCost 2).trans
    (StateDecodeVector.callAfter_gas cfg (paid s cfg.regularOpCost 2) p.toVector)
theorem copied_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p) :
    GasUnits s (copied cfg s p) cfg.regularOpCost (18*p.size.toNat+643) := by
  have args : GasUnits s (copyArguments cfg s p) cfg.regularOpCost 626 := by
    simpa only [copyArguments,Nat.reduceAdd] using (vectorAfter_gas cfg s p).trans (gasUnits_paid (vectorAfter cfg s p) cfg.regularOpCost 4)
  have h:=args.trans (memcpy_units (copyArguments cfg s p) cfg.regularOpCost p.memoryIndex (pointer p) p.source
    (StateDecodeVector.finalMemory p.toVector) p.size.toNat (copy_bounds p hn).2.2.2.2.2.1)
  simpa only [copied,show 626+(18*p.size.toNat+17)=18*p.size.toNat+643 by omega] using h

theorem after_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p) :
    GasUnits s (after cfg s p) cfg.regularOpCost (bodyCost p) := by
  have h:=(copied_gas cfg s p hn).trans
    (finish_units (copied cfg s p) cfg.regularOpCost p.memoryIndex (copiedMemory p) p.outVector p.size)
  simpa only [after,bodyCost,show (18*p.size.toNat+643)+4=18*p.size.toNat+647 by omega] using h

theorem callAfter_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p) :
    GasUnits s (callAfter cfg s p) cfg.regularOpCost (18*p.size.toNat+658) := by
  have one:=gasUnits_charge s cfg.regularOpCost 1
  simp only [Nat.one_mul] at one
  have enter : GasUnits s (entered s cfg.regularOpCost) cfg.regularOpCost 11 := by
    simpa only [entered,Nat.reduceAdd] using one.trans (gasUnits_charge (chargedStore s cfg.regularOpCost) cfg.regularOpCost 10)
  have h:=enter.trans (after_gas cfg (entered s cfg.regularOpCost) p hn)
  simpa only [callAfter,bodyCost,show 11+(18*p.size.toNat+647)=18*p.size.toNat+658 by omega] using h
end WNear.Proofs.StateDecodeVectorCopy
