import Proofs.DeallocateInsertState
import Proofs.VectorDropPositive237Arguments

/-! Original-state interface to the concrete f237 allocator forwarder. -/
namespace WNear.Proofs.VectorDropInsert237
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid)
set_option maxRecDepth 16384

/-- Exact native and installed-code conditions for the previous-allocated insertion branch.
All reads occur in the original or explicitly defined sequential memories. -/
structure Ready (s : Store NearState) (inst : Nat) (p : DeallocateCore.Layout) (address582 : Nat) : Prop where
  code : DeallocateCore.Code s inst p
  memory : s.mems[p.memoryIndex]? = some p.memory
  native : DeallocateInsert.Native p
  allocator : p.allocator = 1074896
  index582 : p.mi.funcAddrs[582]? = some address582
  function582 : s.funcs[address582]? = some (.wasm WNear.Binary.Deallocate.coreSignature inst WNear.Binary.Deallocate.coreFunction)

theorem code_charge (s : Store NearState) (inst cost : Nat) (p : DeallocateCore.Layout)
    (h : DeallocateCore.Code s inst p) : DeallocateCore.Code (chargedStore s cost) inst p := by
  exact {h with
    module := h.module
    function568 := h.function568
    function570 := h.function570
    function575 := h.function575
    function576 := h.function576}

theorem code_paid (s : Store NearState) (inst op count : Nat) (p : DeallocateCore.Layout)
    (h : DeallocateCore.Code s inst p) : DeallocateCore.Code (paid s op count) inst p := by
  induction count with
  | zero => exact h
  | succ n ih => exact code_charge (paid s op n) inst op p ih

theorem Ready.charge (s : Store NearState) (inst cost : Nat) (p : DeallocateCore.Layout) (address : Nat)
    (h : Ready s inst p address) : Ready (chargedStore s cost) inst p address := by
  exact {h with code := code_charge s inst cost p h.code, memory := h.memory, function582 := h.function582}

theorem Ready.paid (s : Store NearState) (inst op count : Nat) (p : DeallocateCore.Layout) (address : Nat)
    (h : Ready s inst p address) : Ready (paid s op count) inst p address := by
  induction count with
  | zero => exact h
  | succ n ih => exact Ready.charge (WNear.Proofs.StorePairCaller.paid s op n) inst op p address ih
end WNear.Proofs.VectorDropInsert237
