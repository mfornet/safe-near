import Proofs.AllocateFlaggedCallFrame
import Proofs.AllocateSearchGasCost

/-! Exact ordinary gas and promise frames for actual flags-two allocation. -/
namespace WNear.Proofs.AllocateFlagged
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits paid_gas)
open AllocateSearch (maskStore taggedTeeStore Layout GasUnits gasUnits_paid gasUnits_charge minimumDone arithmeticDone callbackDone endSubtracted candidateAfter unitsFrom sizeFrom initialAfter)
set_option maxRecDepth 16384
attribute [local irreducible] minimumDone arithmeticDone callbackDone endSubtracted candidateAfter searched searchAfter callAfter controlAfter Allocate.committed Allocate.callbackAfter
private theorem units_entered9 (s : Store NearState) (op : Nat) : GasUnits s (AllocateUnits.entered9 s op) op 10 := by
  have first := gasUnits_charge s op 1
  simp only [Nat.one_mul] at first
  have h := first.trans (gasUnits_charge (chargedStore s op) op 9)
  simpa only [AllocateUnits.entered9,Nat.one_mul,Nat.reduceAdd] using h
private theorem units_units (s : Store NearState) (op : Nat) : GasUnits s (AllocateUnits.unitsAfter s op) op 19 := by
  exact (units_entered9 s op).trans (gasUnits_paid (AllocateUnits.entered9 s op) op 9)
private theorem units_quantum (s : Store NearState) (op : Nat) : GasUnits s (AllocateUnits.quantumAfter s op) op 11 := by
  exact (units_entered9 s op).trans (gasUnits_paid (AllocateUnits.entered9 s op) op 1)
private theorem units_callback (s : Store NearState) (op : Nat) : GasUnits s (Allocate.callbackAfter s op) op 35 := by
  have a := (gasUnits_paid s op 4).trans (units_quantum (paid s op 4) op)
  have b := a.trans (units_units (AllocateUnits.quantumAfter (paid s op 4) op) op)
  have c := b.trans (gasUnits_paid (AllocateUnits.unitsAfter (AllocateUnits.quantumAfter (paid s op 4) op) op) op 1)
  simpa only [Allocate.callbackAfter,Nat.reduceAdd] using c
private theorem units_minimum (s : Store NearState) (op : Nat) : GasUnits s (AllocateUnits.minimumAfter s op) op 17 := by
  exact (units_entered9 s op).trans (gasUnits_paid (AllocateUnits.entered9 s op) op 7)
private theorem units_arithmeticDone (s : Store NearState) (op : Nat) : GasUnits s (arithmeticDone s op) op 83 := by
  have a := (gasUnits_paid s op 13).trans (units_callback (paid s op 13) op)
  have b := a.trans (gasUnits_paid (Allocate.callbackAfter (paid s op 13) op) op 35)
  simpa only [arithmeticDone,callbackDone,endSubtracted,Nat.reduceAdd] using b

theorem gasUnits_minimumDone (s : Store NearState) (op : Nat) : GasUnits s (minimumDone s op) op 101 := by
  have a := (units_arithmeticDone s op).trans (gasUnits_paid (arithmeticDone s op) op 1)
  have b := a.trans (units_minimum (paid (arithmeticDone s op) op 1) op)
  simpa only [minimumDone,Nat.reduceAdd] using b

private theorem units_store32 (s : Store NearState) (op n index address : Nat) (memory : Memory) (v : UInt32) :
    GasUnits s (storeI32 (paid s op n) index address memory v) op n :=
  (gasUnits_paid s op n).host_eq rfl
private theorem units_store64 (s : Store NearState) (op n index address : Nat) (memory : Memory) (v : UInt64) :
    GasUnits s (storeI64 (paid s op n) index address memory v) op n :=
  (gasUnits_paid s op n).host_eq rfl
private theorem units_initialize (s : Store NearState) (op index : Nat) (memory : Memory) (head header : UInt32) :
    GasUnits s (Allocate.initializedStore s op index memory head header) op 12 := by
  let first := storeI32 (paid s op 3) index (header.toNat+8) memory 0
  have a := units_store32 s op 3 index (header.toNat+8) memory 0
  have b := a.trans (units_store64 first op 3 index header.toNat (writeI32 memory (header.toNat+8) 0) 0)
  have c := b.trans (units_store32 (Allocate.clearedStore s op index memory header) op 6 index header.toNat
    (Allocate.clearedMemory memory header) (readI32 (Allocate.clearedMemory memory header) head.toNat &&& 4294967292))
  simpa only [Allocate.initializedStore,Allocate.copiedEndStore,Allocate.clearedStore,first,Nat.reduceAdd] using c
private theorem units_links (s : Store NearState) (op : Nat) (p : Layout) :
    GasUnits s (linkedStore s op p) op 23 := by
  have a := units_store32 s op 8 p.memoryIndex ((header p).toNat+4) (initializedMemory p)
    (Allocate.taggedValue (initializedMemory p) (header p) 4 (head p))
  have b := a.trans (units_store32 (previousStore s op p) op 6 p.memoryIndex ((head p).toNat+8)
    (previousMemory p) (readI32 (previousMemory p) ((head p).toNat+8) &&& 4294967294))
  have c := b.trans (units_store32 (unflaggedStore s op p) op 9 p.memoryIndex ((head p).toNat+0)
    (unflaggedMemory p) (Allocate.taggedValue (unflaggedMemory p) (head p) 0 (header p)))
  simpa only [linkedStore,unflaggedStore,previousStore,maskStore,taggedTeeStore,Allocate.taggedStore,Nat.reduceAdd] using c

private theorem units_transfer (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (transferred s op p) op 12 := by
  have a := units_store32 s op 5 p.memoryIndex (head p).toNat (linkedMemory p) (linkedWord p &&& 4294967293)
  have b := a.trans (units_store32 (clearedStore s op p) op 6 p.memoryIndex (header p).toNat (clearedFlagMemory p) (readI32 (clearedFlagMemory p) (header p).toNat ||| 2))
  have c := b.trans (gasUnits_paid (flaggedStore s op p) op 1)
  simpa only [transferred,flaggedStore,flagStore,clearedStore,clearStore,Nat.reduceAdd] using c

theorem gasUnits_controlAfter (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (controlAfter s op p) op 57 := by
  have a := (gasUnits_paid s op 17).trans (units_links (afterBacklink s op) op p)
  have b := a.trans (gasUnits_paid (linkedStore (afterBacklink s op) op p) op 5)
  have c := b.trans (units_transfer (paid (linkedStore (afterBacklink s op) op p) op 5) op p)
  simpa only [controlAfter,afterBacklink,Nat.reduceAdd] using c
private theorem units_commit (s : Store NearState) (op index : Nat) (memory : Memory) (header : UInt32) :
    GasUnits s (Allocate.committed s op index memory header) op 10 := by
  have a := units_store32 s op 6 index header.toNat memory (readI32 memory header.toNat ||| 1)
  have b := a.trans (gasUnits_paid (Allocate.markedStore s op index memory header) op 4)
  simpa only [Allocate.committed,Allocate.markedStore,Nat.reduceAdd] using b

theorem gasUnits_splitAfter (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (splitAfter s op p) op 180 := by
  have a := (gasUnits_minimumDone s op).trans (units_initialize (minimumDone s op) op p.memoryIndex p.memory (head p) (header p))
  have b := a.trans (gasUnits_controlAfter (mutateInitialized (minimumDone s op) op p) op p)
  have c := b.trans (units_commit (controlAfter (mutateInitialized (minimumDone s op) op p) op p) op p.memoryIndex (flaggedMemory p) (header p))
  simpa only [splitAfter,mutateAfter,mutateInitialized,Nat.reduceAdd] using c
private theorem units_size (s : Store NearState) (op : Nat) : GasUnits s (DeallocateListSize.after s op) op 25 := by
  have first := gasUnits_charge s op 1
  simp only [Nat.one_mul] at first
  have a := first.trans (gasUnits_charge (chargedStore s op) op 9)
  have b := a.trans (gasUnits_paid (DeallocateListSize.entered s op) op 15)
  simpa only [DeallocateListSize.after,DeallocateListSize.entered,Nat.reduceAdd] using b
private theorem units_candidate (s : Store NearState) (op : Nat) : GasUnits s (candidateAfter s op) op 60 := by
  have a := (gasUnits_paid s op 10).trans (gasUnits_paid (paid s op 10) op 1)
  have b := a.trans (units_units (paid (paid s op 10) op 1) op)
  have c := b.trans (gasUnits_paid (AllocateUnits.unitsAfter (paid (paid s op 10) op 1) op) op 1)
  have d := c.trans (gasUnits_paid (unitsFrom (paid s op 10) op) op 1)
  have e := d.trans (units_size (paid (unitsFrom (paid s op 10) op) op 1) op)
  have f := e.trans (gasUnits_paid (DeallocateListSize.after (paid (unitsFrom (paid s op 10) op) op 1) op) op 3)
  simpa only [candidateAfter,sizeFrom,unitsFrom,Nat.reduceAdd] using f
 theorem gasUnits_searchAfter (s : Store NearState) (op : Nat) (p : Layout) :
    GasUnits s (searchAfter s op p) op 262 := by
  have a := (gasUnits_paid s op 16).trans (gasUnits_paid (initialAfter s op) op 5)
  have b := a.trans (units_candidate (paid (initialAfter s op) op 5) op)
  have c := b.trans (gasUnits_splitAfter (candidateAfter (paid (initialAfter s op) op 5) op) op p)
  have cc : GasUnits s (searched (paid (initialAfter s op) op 5) op p) op 261 := by simpa only [searched,Nat.reduceAdd] using c
  have d := cc.trans (gasUnits_paid (searched (paid (initialAfter s op) op 5) op p) op 1)
  simpa only [searchAfter,searched,initialAfter,Nat.reduceAdd] using d
 theorem gasUnits_callAfter (s : Store NearState) (op : Nat) (p : Layout) :
    GasUnits s (callAfter s op p) op 278 := by
  have first := gasUnits_charge s op 1
  simp only [Nat.one_mul] at first
  have a := first.trans (gasUnits_charge (chargedStore s op) op 15)
  have b := a.trans (gasUnits_searchAfter (entered s op) op p)
  simpa only [callAfter,entered,Nat.reduceAdd] using b
 theorem callAfter_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (278*op+rest)) :
    (callAfter s op p).host.gas.burnt=s.host.gas.burnt+278*op ∧
    (callAfter s op p).host.gas.promises=s.host.gas.promises ∧ (callAfter s op p).host.gas.Credits rest :=
  gasUnits_callAfter s op p rest hc

end WNear.Proofs.AllocateFlagged
