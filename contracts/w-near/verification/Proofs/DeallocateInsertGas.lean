import Proofs.DeallocateInsertPhases
import Proofs.DeallocateCoreCredits
import Proofs.DeallocateListSizeFrame
import Proofs.AllocateSearchGasCost

/-! Exact ordinary-operation charge and residual credits of582's insertion branch. -/
namespace WNear.Proofs.DeallocateInsert
open Wasm Wasm.Near MeteredLogic DeallocateCore
open StorePairCaller (paid paid_credits)
open AllocateSearch (GasUnits gasUnits_paid gasUnits_charge)
private theorem align_units(s:Store NearState)(op:Nat):GasUnits s (Deallocate.aligned s op) op 43:=by
  have start:=gasUnits_paid s op 1
  have core:GasUnits (paid s op 1) (DeallocateAlign.after570 (paid s op 1) op) op 41:=by
    intro rest hc
    have g:=DeallocateAlign.after570_gas (paid s op 1) op rest hc
    exact ⟨g.1,g.2,DeallocateAlign.after570_credits (paid s op 1) op rest hc⟩
  simpa only[Deallocate.aligned,Nat.reduceAdd] using (start.trans core).trans (gasUnits_paid _ op 1)
private theorem size_units(s:Store NearState)(op:Nat):GasUnits s (Deallocate.sized s op) op 27:=by
  have core:GasUnits (paid s op 1) (DeallocateListSize.after (paid s op 1) op) op 25:=by
    intro rest hc
    exact DeallocateListSize.after_gas (paid s op 1) op rest hc
  simpa only[Deallocate.sized,Nat.reduceAdd] using ((gasUnits_paid s op 1).trans core).trans (gasUnits_paid _ op 1)
private theorem zeroed_units(s:Store NearState)(op:Nat)(p:Layout):GasUnits s (zeroed s op p) op 91:=by
  have guard:GasUnits s (DeallocateCore.guarded s op) op 6:=gasUnits_paid s op 6
  have align:GasUnits s (DeallocateCore.aligned s op) op 49:=by
    simpa only[DeallocateCore.aligned,Nat.reduceAdd] using guard.trans (align_units _ op)
  have save:GasUnits s (DeallocateCore.saved s op) op 52:=by
    simpa only[DeallocateCore.saved,Nat.reduceAdd] using align.trans (gasUnits_paid _ op 3)
  have mark:GasUnits s (DeallocateCore.marked s op p) op 61:=by
    simpa only[DeallocateCore.marked,Nat.reduceAdd] using (save.trans (gasUnits_paid _ op 9)).host_eq (show (storeI32 (paid (DeallocateCore.saved s op) op 9) p.memoryIndex p.header.toNat p.memory (readI32 p.memory p.header.toNat &&&4294967294)).host=(paid (DeallocateCore.saved s op) op 9).host by rfl)
  have size:GasUnits s (DeallocateCore.sized s op p) op 88:=by
    simpa only[DeallocateCore.sized,Nat.reduceAdd] using mark.trans (size_units _ op)
  simpa only[DeallocateCore.zeroed,Nat.reduceAdd] using (size.trans (gasUnits_paid _ op 3)).host_eq (show (zeroed s op p).host=(paid (DeallocateCore.sized s op p) op 3).host by rfl)

theorem neighborAfter_gas(s:Store NearState)(op:Nat)(p:Layout):GasUnits s (neighborAfter s op p) op 38:=by
  have l:GasUnits s (linked s op p) op 35:=by
    simpa only[linked,selected,Nat.reduceAdd] using ((gasUnits_paid s op 32).trans (gasUnits_paid _ op 3)).host_eq (show (linked s op p).host=(paid (selected s op) op 3).host by rfl)
  simpa only[neighborAfter,Nat.reduceAdd] using (l.trans (gasUnits_paid _ op 3)).host_eq (show (neighborAfter s op p).host=(paid (linked s op p) op 3).host by rfl)

theorem after_gas(s:Store NearState)(op:Nat)(p:Layout):GasUnits s (after s op p) op 129:=by
  simpa only[after,Nat.reduceAdd] using (zeroed_units s op p).trans (neighborAfter_gas _ op p)

theorem entered_gas(s:Store NearState)(op:Nat):GasUnits s (entered s op) op 13:=by
  have one:=gasUnits_charge s op 1
  simp only[Nat.one_mul] at one
  simpa only[entered,Nat.reduceAdd] using one.trans (gasUnits_charge _ op 12)

theorem callAfter_gas(s:Store NearState)(op:Nat)(p:Layout):GasUnits s (callAfter s op p) op 142:=by
  simpa only[callAfter,Nat.reduceAdd] using (entered_gas s op).trans (after_gas _ op p)

theorem neighborAfter_credits(s:Store NearState)(op rest:Nat)(p:Layout)(hc:s.host.gas.Credits (38*op+rest)):
    (neighborAfter s op p).host.gas.Credits rest:=(neighborAfter_gas s op p rest hc).2.2

theorem after_credits(s:Store NearState)(op rest:Nat)(p:Layout)(hc:s.host.gas.Credits (129*op+rest)):
    (after s op p).host.gas.Credits rest:=(after_gas s op p rest hc).2.2

theorem entered_credits(s:Store NearState)(op rest:Nat)(hc:s.host.gas.Credits (13*op+rest)):
    (entered s op).host.gas.Credits rest:=(entered_gas s op rest hc).2.2

theorem callAfter_credits(s:Store NearState)(op rest:Nat)(p:Layout)(hc:s.host.gas.Credits (142*op+rest)):
    (callAfter s op p).host.gas.Credits rest:=(callAfter_gas s op p rest hc).2.2
end WNear.Proofs.DeallocateInsert
