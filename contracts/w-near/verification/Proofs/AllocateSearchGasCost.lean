import Proofs.AllocateSearchCallGas

/-! Compositional exact burnt gas and promise frames for allocator phases. -/
namespace WNear.Proofs.AllocateSearch
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits paid_gas)
set_option maxRecDepth 16384
attribute [local irreducible] minimumDone arithmeticDone callbackDone endSubtracted initialized linked splitAfter
  candidateAfter searched searchAfter callAfter controlAfter Allocate.committed Allocate.callbackAfter

/-- A successful phase consumes exactly its stated ordinary operation units. -/
def GasUnits (s t : Store NearState) (op count : Nat) : Prop := ∀ rest,
  s.host.gas.Credits (count*op+rest) →
    t.host.gas.burnt=s.host.gas.burnt+count*op ∧
    t.host.gas.promises=s.host.gas.promises ∧ t.host.gas.Credits rest

theorem GasUnits.trans {s t u : Store NearState} {op a b : Nat}
    (h1 : GasUnits s t op a) (h2 : GasUnits t u op b) : GasUnits s u op (a+b) := by
  intro rest hc
  have c : s.host.gas.Credits (a*op+(b*op+rest)) := by simpa only [Nat.add_mul,Nat.add_assoc] using hc
  have first := h1 (b*op+rest) c
  have second := h2 rest first.2.2
  refine ⟨?_,second.2.1.trans first.2.1,second.2.2⟩
  rw [second.1,first.1,Nat.add_mul]
  omega

theorem GasUnits.host_eq {s t u : Store NearState} {op n : Nat}
    (h : GasUnits s t op n) (he : u.host=t.host) : GasUnits s u op n := by
  intro rest hc
  rw [he]
  exact h rest hc

theorem gasUnits_paid (s : Store NearState) (op n : Nat) : GasUnits s (paid s op n) op n := by
  intro rest hc
  have gas := paid_gas s op n rest hc
  exact ⟨gas.1,gas.2,paid_credits s op n rest hc⟩
theorem gasUnits_charge (s : Store NearState) (op n : Nat) : GasUnits s (chargedStore s (n*op)) op n := by
  intro rest hc
  have gas := GasCounter.burn_credits s.host.gas (n*op) rest hc
  exact ⟨gas.2.1,gas.2.2.1,gas.2.2.2⟩

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
private theorem units_initialized (s : Store NearState) (op : Nat) (p : Layout) :
    GasUnits s (initialized s op p) op 113 := by
  have a := (gasUnits_minimumDone s op).trans (units_initialize (minimumDone s op) op p.memoryIndex p.memory (head p) (header p))
  simpa only [initialized,Nat.reduceAdd] using a
private theorem units_backlink (s : Store NearState) (op : Nat) (p : Layout) :
    GasUnits s (afterBacklink s op p) op 25 := by
  have a := (gasUnits_paid s op 17).trans (units_store32 (paid s op 17) op 8 p.memoryIndex
    ((finish p).toNat+4) (initializedMemory p) (Allocate.taggedValue (initializedMemory p) (finish p) 4 (header p)))
  simpa only [afterBacklink,backlinkStore,Allocate.taggedStore,Nat.reduceAdd] using a
private theorem units_links (s : Store NearState) (op : Nat) (p : Layout) :
    GasUnits s (linkedStore s op p) op 23 := by
  have a := units_store32 s op 8 p.memoryIndex ((header p).toNat+4) (backlinkedMemory p)
    (Allocate.taggedValue (backlinkedMemory p) (header p) 4 (head p))
  have b := a.trans (units_store32 (previousStore s op p) op 6 p.memoryIndex ((head p).toNat+8)
    (previousMemory p) (readI32 (previousMemory p) ((head p).toNat+8) &&& 4294967294))
  have c := b.trans (units_store32 (unflaggedStore s op p) op 9 p.memoryIndex ((head p).toNat+0)
    (unflaggedMemory p) (Allocate.taggedValue (unflaggedMemory p) (head p) 0 (header p)))
  simpa only [linkedStore,unflaggedStore,previousStore,maskStore,taggedTeeStore,Allocate.taggedStore,Nat.reduceAdd] using c
 theorem gasUnits_controlAfter (s : Store NearState) (op : Nat) (p : Layout) :
    GasUnits s (controlAfter s op p) op 53 := by
  have a := (units_backlink s op p).trans (units_links (afterBacklink s op p) op p)
  have b := a.trans (gasUnits_paid (linkedStore (afterBacklink s op p) op p) op 5)
  simpa only [controlAfter,Nat.reduceAdd] using b
private theorem units_commit (s : Store NearState) (op index : Nat) (memory : Memory) (header : UInt32) :
    GasUnits s (Allocate.committed s op index memory header) op 10 := by
  have a := units_store32 s op 6 index header.toNat memory (readI32 memory header.toNat ||| 1)
  have b := a.trans (gasUnits_paid (Allocate.markedStore s op index memory header) op 4)
  simpa only [Allocate.committed,Allocate.markedStore,Nat.reduceAdd] using b
 theorem gasUnits_splitAfter (s : Store NearState) (op : Nat) (p : Layout) :
    GasUnits s (splitAfter s op p) op 176 := by
  have a := (units_initialized s op p).trans (gasUnits_controlAfter (initialized s op p) op p)
  have aa : GasUnits s (linked s op p) op 166 := by simpa only [linked,Nat.reduceAdd] using a
  have b := aa.trans (units_commit (linked s op p) op p.memoryIndex (linkedMemory p) (header p))
  simpa only [splitAfter,linked,Nat.reduceAdd] using b
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
    GasUnits s (searchAfter s op p) op 258 := by
  have a := (gasUnits_paid s op 16).trans (gasUnits_paid (initialAfter s op) op 5)
  have b := a.trans (units_candidate (paid (initialAfter s op) op 5) op)
  have c := b.trans (gasUnits_splitAfter (candidateAfter (paid (initialAfter s op) op 5) op) op p)
  have cc : GasUnits s (searched (paid (initialAfter s op) op 5) op p) op 257 := by simpa only [searched,Nat.reduceAdd] using c
  have d := cc.trans (gasUnits_paid (searched (paid (initialAfter s op) op 5) op p) op 1)
  simpa only [searchAfter,searched,initialAfter,Nat.reduceAdd] using d
 theorem gasUnits_callAfter (s : Store NearState) (op : Nat) (p : Layout) :
    GasUnits s (callAfter s op p) op 274 := by
  have first := gasUnits_charge s op 1
  simp only [Nat.one_mul] at first
  have a := first.trans (gasUnits_charge (chargedStore s op) op 15)
  have b := a.trans (gasUnits_searchAfter (entered s op) op p)
  simpa only [callAfter,entered,Nat.reduceAdd] using b
 theorem callAfter_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (274*op+rest)) :
    (callAfter s op p).host.gas.burnt=s.host.gas.burnt+274*op ∧
    (callAfter s op p).host.gas.promises=s.host.gas.promises ∧ (callAfter s op p).host.gas.Credits rest :=
  gasUnits_callAfter s op p rest hc

end WNear.Proofs.AllocateSearch
