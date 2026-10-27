import Proofs.AllocateGrowthState
import Proofs.AllocateGrowthAttempt
import Proofs.AllocateGrowthMiddle
import Proofs.AllocateGrowthPreparation
import Proofs.AllocateGrowthCommitFrame

/-! Exact gas with a symbolic linear fee and original-store frames for577 phases. -/
namespace WNear.Proofs.AllocateGrowth
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_paid gasUnits_charge)
set_option maxRecDepth 16384
attribute [local irreducible] rounded beforeGrowth growthStore growthAfter bytesAfter prepared

/-- Arbitrary-cost accounting, so linear fees are never rounded to opcode units. -/
def GasCost (s t : Store NearState) (cost : Nat) : Prop := ∀ rest,
  s.host.gas.Credits (cost+rest) →
    t.host.gas.burnt=s.host.gas.burnt+cost ∧
    t.host.gas.promises=s.host.gas.promises ∧ t.host.gas.Credits rest

theorem GasCost.trans {s t u : Store NearState} {a b : Nat}
    (h1 : GasCost s t a) (h2 : GasCost t u b) : GasCost s u (a+b) := by
  intro rest hc
  have x := h1 (b+rest) (by simpa only [Nat.add_assoc] using hc)
  have y := h2 rest x.2.2
  exact ⟨by rw [y.1,x.1]; omega,y.2.1.trans x.2.1,y.2.2⟩

theorem GasCost.of_units {s t : Store NearState} {op n : Nat} (h : GasUnits s t op n) :
    GasCost s t (n*op) := h

private theorem entered_units (s : Store NearState) (op count : Nat) :
    GasUnits s (chargedStore (chargedStore s op) (count*op)) op (1+count) := by
  have first := gasUnits_charge s op 1
  simp only [Nat.one_mul] at first
  exact first.trans (gasUnits_charge (chargedStore s op) op count)

private theorem after568_units (s : Store NearState) (op : Nat) : GasUnits s (DeallocateAlign.after568 s op) op 29 :=
  (entered_units s op 10).trans (gasUnits_paid (DeallocateAlign.entered568 s op) op 18)
private theorem after569_units (s : Store NearState) (op : Nat) : GasUnits s (after569 s op) op 41 := by
  have a := entered_units s op 9
  have b := a.trans (gasUnits_paid (entered569 s op) op 2)
  exact b.trans (after568_units (paid (entered569 s op) op 2) op)

theorem rounded_gas (s : Store NearState) (op : Nat) : GasUnits s (rounded s op) op 42 := by
  simpa only [rounded,Nat.reduceAdd] using (gasUnits_paid s op 1).trans (after569_units (paid s op 1) op)

theorem beforeGrowth_gas (s : Store NearState) (op : Nat) : GasUnits s (beforeGrowth s op) op 43 := by
  simpa only [beforeGrowth,Nat.reduceAdd] using (rounded_gas s op).trans (gasUnits_paid (rounded s op) op 1)

theorem growthAfter_gas (cfg : WasmConfig) (s : Store NearState) (index : Nat) (grown : Memory) (bytes : UInt32) :
    GasCost s (growthAfter cfg s index grown bytes)
      (47*cfg.regularOpCost+memoryGrowCost cfg (growPages bytes)) := by
  let op := cfg.regularOpCost
  let fee := memoryGrowCost cfg (growPages bytes)
  have a := GasCost.of_units (beforeGrowth_gas s op)
  have b : GasCost (beforeGrowth s op) (growthStore cfg s index grown bytes) fee := by
    intro rest hc
    have h := grownStore_gas cfg (growPages bytes) (beforeGrowth s op) index rest grown hc
    simpa only [growthStore,op,fee] using And.intro h.1 (And.intro h.2.1 h.2.2.1)
  have c := (a.trans b).trans (GasCost.of_units (gasUnits_paid (growthStore cfg s index grown bytes) op 4))
  have cost : 43*op+fee+4*op=47*cfg.regularOpCost+memoryGrowCost cfg (growPages bytes) := by dsimp [op,fee];omega
  rw [cost] at c
  simpa only [growthAfter,op] using c

private theorem after573_units (s : Store NearState) (op : Nat) : GasUnits s (after573 s op) op 19 :=
  (entered_units s op 9).trans (gasUnits_paid (chargedStore (chargedStore s op) (9*op)) op 9)
private theorem minimum_units (s : Store NearState) (op : Nat) : GasUnits s (AllocateUnits.minimumAfter s op) op 17 :=
  (entered_units s op 9).trans (gasUnits_paid (AllocateUnits.entered9 s op) op 7)

theorem bytesAfter_gas (s : Store NearState) (op : Nat) : GasUnits s (bytesAfter s op) op 38 := by
  have a := (gasUnits_paid s op 1).trans (after573_units (paid s op 1) op)
  have b := a.trans (gasUnits_paid (after573 (paid s op 1) op) op 1)
  simpa only [bytesAfter,Nat.reduceAdd] using b.trans (minimum_units (paid (after573 (paid s op 1) op) op 1) op)

theorem prepared_gas (s : Store NearState) (op : Nat) : GasUnits s (prepared s op) op 21 := by
  have units : GasUnits (paid s op 1) (AllocateUnits.unitsAfter (paid s op 1) op) op 19 :=
    (entered_units (paid s op 1) op 9).trans (gasUnits_paid (AllocateUnits.entered9 (paid s op 1) op) op 9)
  simpa only [prepared,Nat.reduceAdd] using ((gasUnits_paid s op 1).trans units).trans (gasUnits_paid (AllocateUnits.unitsAfter (paid s op 1) op) op 1)

theorem GasCost.credits {s t : Store NearState} {cost rest : Nat}
    (h : GasCost s t cost) (hc : s.host.gas.Credits (cost+rest)) : t.host.gas.Credits rest := (h rest hc).2.2

theorem sized_gas (s : Store NearState) (op : Nat) : GasUnits s (sized s op) op 50 :=
  (prepared_gas s op).trans (gasUnits_paid (prepared s op) op 29)

theorem grownPhase_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (grownPhase cfg s p) (97*cfg.regularOpCost+memoryGrowCost cfg (delta p)) := by
  have h := (GasCost.of_units (sized_gas s cfg.regularOpCost)).trans
    (growthAfter_gas cfg (sized s cfg.regularOpCost) p.memoryIndex p.grown (requested p))
  have cost : 50*cfg.regularOpCost+(47*cfg.regularOpCost+memoryGrowCost cfg (growPages (requested p)))=
      97*cfg.regularOpCost+memoryGrowCost cfg (delta p) := by unfold delta;omega
  rw [cost] at h
  exact h

theorem pageChecked_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (pageChecked cfg s p) (103*cfg.regularOpCost+memoryGrowCost cfg (delta p)) := by
  have h := (grownPhase_gas cfg s p).trans (GasCost.of_units (gasUnits_paid (grownPhase cfg s p) cfg.regularOpCost 6))
  have cost : 97*cfg.regularOpCost+memoryGrowCost cfg (delta p)+6*cfg.regularOpCost=
      103*cfg.regularOpCost+memoryGrowCost cfg (delta p) := by omega
  rw [cost] at h
  exact h

theorem converted_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (converted cfg s p) (141*cfg.regularOpCost+memoryGrowCost cfg (delta p)) := by
  have h := (pageChecked_gas cfg s p).trans (GasCost.of_units (bytesAfter_gas (pageChecked cfg s p) cfg.regularOpCost))
  have cost : 103*cfg.regularOpCost+memoryGrowCost cfg (delta p)+38*cfg.regularOpCost=
      141*cfg.regularOpCost+memoryGrowCost cfg (delta p) := by omega
  rw [cost] at h
  exact h

theorem committed_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (committed cfg s p) (159*cfg.regularOpCost+memoryGrowCost cfg (delta p)) := by
  have h := (converted_gas cfg s p).trans (GasCost.of_units
    (freshStore_gas (converted cfg s p) cfg.regularOpCost p.memoryIndex p.grown (header p) (blockBytes p)))
  have cost : 141*cfg.regularOpCost+memoryGrowCost cfg (delta p)+18*cfg.regularOpCost=
      159*cfg.regularOpCost+memoryGrowCost cfg (delta p) := by omega
  rw [cost] at h
  exact h

theorem after_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (after cfg s p) (166*cfg.regularOpCost+memoryGrowCost cfg (delta p)) := by
  have h := (committed_gas cfg s p).trans (GasCost.of_units
    (recordStore_gas (committed cfg s p) cfg.regularOpCost p.memoryIndex (committedMemory p) p.record (header p)))
  have cost : 159*cfg.regularOpCost+memoryGrowCost cfg (delta p)+7*cfg.regularOpCost=
      166*cfg.regularOpCost+memoryGrowCost cfg (delta p) := by omega
  rw [cost] at h
  exact h

private def pureView (s : Store NearState) := (s.funcs,s.modules,s.mems,s.globals,s.tables)
private theorem pureView_paid (s : Store NearState) (op n : Nat) : pureView (paid s op n)=pureView s := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem pureView_charge (s : Store NearState) (cost : Nat) : pureView (chargedStore s cost)=pureView s := rfl
private theorem pureView_prepared (s : Store NearState) (op : Nat) : pureView (prepared s op)=pureView s := by
  simp only [prepared,AllocateUnits.unitsAfter,AllocateUnits.entered9,pureView_paid,pureView_charge]
private theorem pureView_rounded (s : Store NearState) (op : Nat) : pureView (rounded s op)=pureView s := by
  simp only [rounded,after569,bodyAfter569,entered569,DeallocateAlign.after568,DeallocateAlign.entered568,
    pureView_paid,pureView_charge]
private theorem pureView_bytesAfter (s : Store NearState) (op : Nat) : pureView (bytesAfter s op)=pureView s := by
  simp only [bytesAfter,after573,AllocateUnits.minimumAfter,AllocateUnits.entered9,pureView_paid,pureView_charge]

theorem sized_fields (s : Store NearState) (op : Nat) :
    (sized s op).funcs=s.funcs ∧ (sized s op).modules=s.modules ∧ (sized s op).mems=s.mems ∧
    (sized s op).globals=s.globals ∧ (sized s op).tables=s.tables := by
  have h : pureView (sized s op)=pureView s := by simp only [sized,pureView_paid,pureView_prepared]
  simpa only [pureView,Prod.mk.injEq] using h

theorem beforeGrowth_fields (s : Store NearState) (op : Nat) :
    (beforeGrowth s op).funcs=s.funcs ∧ (beforeGrowth s op).modules=s.modules ∧ (beforeGrowth s op).mems=s.mems ∧
    (beforeGrowth s op).globals=s.globals ∧ (beforeGrowth s op).tables=s.tables := by
  have h : pureView (beforeGrowth s op)=pureView s := by simp only [beforeGrowth,pureView_paid,pureView_rounded]
  simpa only [pureView,Prod.mk.injEq] using h

theorem growthAfter_fields (cfg : WasmConfig) (s : Store NearState) (index : Nat) (grown : Memory) (bytes : UInt32) :
    (growthAfter cfg s index grown bytes).funcs=s.funcs ∧
    (growthAfter cfg s index grown bytes).modules=s.modules ∧
    (growthAfter cfg s index grown bytes).mems=s.mems.set! index grown ∧
    (growthAfter cfg s index grown bytes).globals=s.globals ∧
    (growthAfter cfg s index grown bytes).tables=s.tables := by
  have h := pureView_paid (growthStore cfg s index grown bytes) cfg.regularOpCost 4
  simp only [pureView,Prod.mk.injEq] at h
  have original := beforeGrowth_fields s cfg.regularOpCost
  simpa only [growthAfter,growthStore,grownStore,chargedStore,original.1,original.2.1,original.2.2.1,
    original.2.2.2.1,original.2.2.2.2] using h

theorem grownPhase_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (grownPhase cfg s p).funcs=s.funcs ∧ (grownPhase cfg s p).modules=s.modules ∧
    (grownPhase cfg s p).mems=s.mems.set! p.memoryIndex p.grown ∧
    (grownPhase cfg s p).globals=s.globals ∧ (grownPhase cfg s p).tables=s.tables := by
  have h := growthAfter_fields cfg (sized s cfg.regularOpCost) p.memoryIndex p.grown (requested p)
  have original := sized_fields s cfg.regularOpCost
  simpa only [grownPhase,original.1,original.2.1,original.2.2.1,original.2.2.2.1,original.2.2.2.2] using h

theorem converted_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (converted cfg s p).funcs=s.funcs ∧ (converted cfg s p).modules=s.modules ∧
    (converted cfg s p).mems=s.mems.set! p.memoryIndex p.grown ∧
    (converted cfg s p).globals=s.globals ∧ (converted cfg s p).tables=s.tables := by
  have h := pureView_bytesAfter (pageChecked cfg s p) cfg.regularOpCost
  have paidFields := pureView_paid (grownPhase cfg s p) cfg.regularOpCost 6
  have original := grownPhase_fields cfg s p
  have all : pureView (converted cfg s p)=pureView (grownPhase cfg s p) := h.trans paidFields
  simp only [pureView,Prod.mk.injEq] at all
  exact ⟨all.1.trans original.1,all.2.1.trans original.2.1,all.2.2.1.trans original.2.2.1,
    all.2.2.2.1.trans original.2.2.2.1,all.2.2.2.2.trans original.2.2.2.2⟩

theorem converted_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (converted cfg s p).mems[p.memoryIndex]?=some p.grown := by
  rw [(converted_fields cfg s p).2.2.1]
  have hi := (Array.getElem?_eq_some_iff.mp hm).1
  simp [hi]
end WNear.Proofs.AllocateGrowth
