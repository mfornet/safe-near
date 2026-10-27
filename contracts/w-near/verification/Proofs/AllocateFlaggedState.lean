import Proofs.AllocateFlaggedNative
import Proofs.AllocateSearchInitial
import Proofs.AllocateSearchShell

/-! Exact sequential flags-two split memories; the old end backlink is omitted. -/
namespace WNear.Proofs.AllocateFlagged
open Wasm Wasm.Near MeteredLogic
open AllocateSearch (Layout)
open StorePairCaller (paid)

def initializedMemory (p : Layout) := AllocateSearch.initializedMemory p
def previousMemory (p : Layout) := writeI32 (initializedMemory p) ((header p).toNat+4)
  (Allocate.taggedValue (initializedMemory p) (header p) 4 (head p))
def unflaggedMemory (p : Layout) := writeI32 (previousMemory p) ((head p).toNat+8)
  (readI32 (previousMemory p) ((head p).toNat+8) &&& 4294967294)
def linkedWord (p : Layout) := Allocate.taggedValue (unflaggedMemory p) (head p) 0 (header p)
def linkedMemory (p : Layout) := writeI32 (unflaggedMemory p) (head p).toNat (linkedWord p)
def clearedFlagMemory (p : Layout) := writeI32 (linkedMemory p) (head p).toNat (linkedWord p &&& 4294967293)
def flaggedMemory (p : Layout) := writeI32 (clearedFlagMemory p) (header p).toNat
  (readI32 (clearedFlagMemory p) (header p).toNat ||| 2)
def finalMemory (p : Layout) := Allocate.markedMemory (flaggedMemory p) (header p)
end WNear.Proofs.AllocateFlagged
