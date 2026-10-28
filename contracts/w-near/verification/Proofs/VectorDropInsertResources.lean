import Proofs.VectorDropInsert237State
import Proofs.VectorDropPositiveResources

/-! Original structural/native facts for complete positive vector destruction.
The vector and allocator layouts must describe the same original module and
memory, which follows from their actual lookup equations. -/
namespace WNear.Proofs.VectorDropInsert
open Wasm Wasm.Near MeteredLogic
open VectorDropPositive
open WNear.Proofs.VectorDrop
open WNear.Proofs.StorePairCaller (paid)
set_option maxRecDepth 16384

structure Resources (s : Store NearState) (inst : Nat) (p : Layout) (q : DeallocateCore.Layout)
    (address68 address237 address582 : Nat) : Prop where
  vector : Ready s inst p
  heap : VectorDropInsert237.Ready s inst q address582
  pointer : q.pointer = pointer p
  length : q.length = capacity p
  alignment : q.alignment = 1
  index237 : p.mi.funcAddrs[237]? = some address237
  function237 : s.funcs[address237]? = some (.wasm WNear.Binary.Deallocate.entrySignature inst WNear.Binary.Deallocate.entryFunction)
  index68 : p.mi.funcAddrs[68]? = some address68
  function68 : s.funcs[address68]? = some (.wasm WNear.Binary.VectorDrop.signature inst WNear.Binary.VectorDrop.function68)

theorem Resources.module_eq (s : Store NearState) (inst : Nat) (p : Layout) (q : DeallocateCore.Layout)
    (a b c : Nat) (r : Resources s inst p q a b c) : q.mi = p.mi := by
  have h := r.heap.code.module
  rw [r.vector.module] at h
  exact Option.some.inj h.symm

theorem Resources.memoryIndex_eq (s : Store NearState) (inst : Nat) (p : Layout) (q : DeallocateCore.Layout)
    (a b c : Nat) (r : Resources s inst p q a b c) : q.memoryIndex = p.memoryIndex := by
  have h := r.heap.code.memoryIndex
  rw [r.module_eq s inst p q a b c, r.vector.memoryIndex] at h
  exact Option.some.inj h.symm

theorem Resources.memory_eq (s : Store NearState) (inst : Nat) (p : Layout) (q : DeallocateCore.Layout)
    (a b c : Nat) (r : Resources s inst p q a b c) : q.memory = p.memory := by
  have h := r.heap.memory
  rw [r.memoryIndex_eq s inst p q a b c, r.vector.memory] at h
  exact Option.some.inj h.symm

/-- Gas-only prefix execution retains every original allocator premise. -/
theorem heap_before237 (s : Store NearState) (inst op : Nat) (q : DeallocateCore.Layout) (address : Nat)
    (r : VectorDropInsert237.Ready s inst q address) :
    VectorDropInsert237.Ready (before237 s op) inst q address := by
  have p1 := r.paid s inst op 1 q address
  have p2 := p1.charge (paid s op 1) inst op q address
  have p3 := p2.charge (chargedStore (paid s op 1) op) inst (9 * op) q address
  have p4 := p3.paid (entered (paid s op 1) op) inst op 1 q address
  have p5 := p4.charge (before747 s op) inst op q address
  have p6 := p5.charge (chargedStore (before747 s op) op) inst (9 * op) q address
  have p7 := p6.paid (entered (before747 s op) op) inst op 9 q address
  have p8 := p7.charge (before777 s op) inst op q address
  have p9 := p8.charge (chargedStore (before777 s op) op) inst (10 * op) q address
  have p10 := p9.paid (tripleEntry (before777 s op) op) inst op 6 q address
  have p11 := p10.charge (before311 s op) inst op q address
  have p12 := p11.charge (chargedStore (before311 s op) op) inst (10 * op) q address
  exact p12.paid (tripleEntry (before311 s op) op) inst op 3 q address

theorem Resources.charge (s : Store NearState) (inst cost : Nat) (p : Layout) (q : DeallocateCore.Layout)
    (a b c : Nat) (r : Resources s inst p q a b c) : Resources (chargedStore s cost) inst p q a b c := by
  exact {r with
    vector := r.vector.charge s inst cost p
    heap := r.heap.charge s inst cost q c
    function237 := r.function237
    function68 := r.function68}
end WNear.Proofs.VectorDropInsert
