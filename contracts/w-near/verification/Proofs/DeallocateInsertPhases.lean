import Proofs.DeallocateInsertPrevious

/-! Exact sequential writes and metering phases for the insertion branch.
The next-disabled guard performs32 scalar operations after the zero link. -/
namespace WNear.Proofs.DeallocateInsert
open Wasm Wasm.Near MeteredLogic DeallocateCore
open StorePairCaller (paid)

def linkedMemory(p:Layout):=writeI32 (zeroMemory p) p.pointer.toNat (oldHead p)
def finalMemory(p:Layout):=writeI32 (linkedMemory p) p.allocator.toNat p.header

def selected(s:Store NearState)(op:Nat):=paid s op 32
def linked(s:Store NearState)(op:Nat)(p:Layout):=
  storeI32 (paid (selected s op) op 3) p.memoryIndex p.pointer.toNat (zeroMemory p) (oldHead p)
def neighborAfter(s:Store NearState)(op:Nat)(p:Layout):=
  storeI32 (paid (linked s op p) op 3) p.memoryIndex p.allocator.toNat (linkedMemory p) p.header
def after(s:Store NearState)(op:Nat)(p:Layout):=neighborAfter (zeroed s op p) op p
def entered(s:Store NearState)(op:Nat):=chargedStore (chargedStore s op) (12*op)
def callAfter(s:Store NearState)(op:Nat)(p:Layout):=after (entered s op) op p
end WNear.Proofs.DeallocateInsert
