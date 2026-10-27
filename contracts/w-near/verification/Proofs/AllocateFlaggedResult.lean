import Proofs.AllocateFlaggedInspect
import Proofs.AllocateSearchInitial

/-! Residual gas and deterministic result for the actual flags-two search. -/
namespace WNear.Proofs.AllocateFlagged
open Wasm Wasm.Near MeteredLogic
open AllocateSearch
open StorePairCaller (paid paid_credits)
attribute [local irreducible] mutateAfter mutateInitialized splitAfter searched candidateAfter

theorem mutateInitialized_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (12*op+rest)) : (mutateInitialized s op p).host.gas.Credits rest := by
  have cl := Allocate.clearedStore_credits s op p.memoryIndex (6*op+rest) p.memory (header p) (hc.mono (by omega))
  unfold mutateInitialized Allocate.initializedStore Allocate.copiedEndStore
  rw [storeI32_host]
  exact paid_credits _ op 6 rest cl

theorem mutateAfter_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (79*op+rest)) : (mutateAfter s op p).host.gas.Credits rest := by
  have ci := mutateInitialized_credits s op (67*op+rest) p (hc.mono (by omega))
  have cc := controlAfter_credits (mutateInitialized s op p) op (10*op+rest) p (ci.mono (by omega))
  unfold mutateAfter
  exact Allocate.committed_credits _ op p.memoryIndex rest (flaggedMemory p) (header p) cc

theorem splitAfter_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (180*op+rest)) : (splitAfter s op p).host.gas.Credits rest := by
  unfold splitAfter
  exact mutateAfter_credits _ op rest p (minimumDone_credits s op _ (hc.mono (by omega)))

theorem searched_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (240*op+rest)) : (searched s op p).host.gas.Credits rest := by
  unfold searched
  exact splitAfter_credits _ op rest p (candidateAfter_credits s op _ (hc.mono (by omega)))

def searchAfter (s : Store NearState) (op : Nat) (p : Layout) := paid (searched (paid (initialAfter s op) op 5) op p) op 1
def searchFrame (frame : CallFrame) (p : Layout) := searchedFrame (initialFrame frame p) p

theorem searchAfter_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (262*op+rest)) : (searchAfter s op p).host.gas.Credits rest := by
  unfold searchAfter
  apply paid_credits _ op 1 rest
  apply searched_credits _ op _ p
  exact paid_credits (initialAfter s op) op 5 _ (initialAfter_credits s op _ (hc.mono (by omega)))

theorem searchedFrame_pointer (frame : CallFrame) (p : Layout) (hs : 14≤frame.locals.size) :
    (searchedFrame frame p).locals[5]?=some (.i32 (header p+8)) := by
  simp [searchedFrame,finalFrame,mutateFrame,Allocate.resultFrame,controlFrame,backlinkFrame,endReadFrame,AllocateSearch.endSelectedFrame,
    splitFrame,Allocate.arithmeticFrame,Allocate.callbackFrame,Allocate.fitFrame,candidateFrame,unitsFrame,prepareFrame,
    show 5<frame.locals.size by omega]
end WNear.Proofs.AllocateFlagged
