import Proofs.AllocateSearchInspect
import Proofs.AllocateSearchInitial

/-! Residual gas and exact deterministic result of the successful search body. -/
namespace WNear.Proofs.AllocateSearch
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] minimumDone initialized linked splitAfter searched candidateAfter

theorem initialized_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (113*op+rest)) : (initialized s op p).host.gas.Credits rest := by
  have cm := minimumDone_credits s op (12*op+rest) (hc.mono (by omega))
  have cl := Allocate.clearedStore_credits (minimumDone s op) op p.memoryIndex (6*op+rest) p.memory (header p) (cm.mono (by omega))
  unfold initialized Allocate.initializedStore Allocate.copiedEndStore
  rw [storeI32_host]
  exact paid_credits _ op 6 rest cl

theorem splitAfter_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (176*op+rest)) : (splitAfter s op p).host.gas.Credits rest := by
  have ci := initialized_credits s op (63*op+rest) p (hc.mono (by omega))
  have cc := controlAfter_credits (initialized s op p) op (10*op+rest) p (ci.mono (by omega))
  unfold splitAfter linked
  exact Allocate.committed_credits _ op p.memoryIndex rest (linkedMemory p) (header p) cc

theorem searched_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (236*op+rest)) : (searched s op p).host.gas.Credits rest := by
  unfold searched
  exact splitAfter_credits _ op rest p (candidateAfter_credits s op _ (hc.mono (by omega)))

def searchAfter (s : Store NearState) (op : Nat) (p : Layout) := paid (searched (paid (initialAfter s op) op 5) op p) op 1
def searchFrame (frame : CallFrame) (p : Layout) := searchedFrame (initialFrame frame p) p

theorem searchAfter_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (258*op+rest)) : (searchAfter s op p).host.gas.Credits rest := by
  unfold searchAfter
  apply paid_credits _ op 1 rest
  apply searched_credits _ op _ p
  exact paid_credits (initialAfter s op) op 5 _ (initialAfter_credits s op _ (hc.mono (by omega)))

theorem searchedFrame_pointer (frame : CallFrame) (p : Layout) (hs : 14≤frame.locals.size) :
    (searchedFrame frame p).locals[5]?=some (.i32 (header p+8)) := by
  simp [searchedFrame,finalFrame,Allocate.resultFrame,controlFrame,backlinkFrame,endReadFrame,endSelectedFrame,
    splitFrame,Allocate.arithmeticFrame,Allocate.callbackFrame,Allocate.fitFrame,candidateFrame,unitsFrame,prepareFrame,
    show 5<frame.locals.size by omega]
end WNear.Proofs.AllocateSearch
