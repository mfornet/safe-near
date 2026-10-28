import Proofs.StateDecodeRawFrame
import Proofs.StateDecodeRawRecordTransport

/-! Original installed-code facts survive actual raw-wrapper phases. The table
array is framed as well as functions and modules, since the allocator uses it. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384

theorem Code.of_fields (s t : Store NearState) (inst : Nat) (p : Layout) (a581 a236 : Nat)
    (h : Code s inst p a581 a236) (hf : t.funcs=s.funcs) (hm : t.modules=s.modules) (ht : t.tables=s.tables) :
    Code t inst p a581 a236 := by
  refine ⟨h.record.transport s t inst p.toPositive a581 a236 p.address310 hf hm ht,
    h.index751,?_,h.index752,?_,h.index769,?_,h.index770,?_⟩
  · rw[hf];exact h.function751
  · rw[hf];exact h.function752
  · rw[hf];exact h.function769
  · rw[hf];exact h.function770

private theorem paid_funcs (s : Store NearState) (op n : Nat) : (StorePairCaller.paid s op n).funcs=s.funcs := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_modules (s : Store NearState) (op n : Nat) : (StorePairCaller.paid s op n).modules=s.modules := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_tables (s : Store NearState) (op n : Nat) : (StorePairCaller.paid s op n).tables=s.tables := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem global_funcs (s : Store NearState) (i : Nat) (v : Value) : (setGlobal s i v).funcs=s.funcs:=rfl
private theorem global_modules (s : Store NearState) (i : Nat) (v : Value) : (setGlobal s i v).modules=s.modules:=rfl
private theorem global_tables (s : Store NearState) (i : Nat) (v : Value) : (setGlobal s i v).tables=s.tables:=rfl

theorem Code.paid (s : Store NearState) (op n inst : Nat) (p : Layout) (a581 a236 : Nat)
    (hc : Code s inst p a581 a236) : Code (StorePairCaller.paid s op n) inst p a581 a236 :=
  hc.of_fields s (StorePairCaller.paid s op n) inst p a581 a236 (paid_funcs s op n) (paid_modules s op n) (paid_tables s op n)

attribute [local irreducible] laidOutRaw alignedRaw checkedRaw flagCheckedRaw argumentsRaw
  reserved769 actualPositive laidOutMemory AllocatePositive.finalMemory

theorem Code.laidOutRaw (s : Store NearState) (op inst : Nat) (p : Layout) (a581 a236 : Nat)
    (hc : Code s inst p a581 a236) : Code (StateDecodeRaw.laidOutRaw s op p) inst p a581 a236 := by
  have h:=laidOutRaw_fields s op p
  exact hc.of_fields s _ inst p a581 a236 h.1 h.2.1 h.2.2

theorem Code.alignedRaw (s : Store NearState) (op inst : Nat) (p : Layout) (a581 a236 : Nat)
    (hc : Code s inst p a581 a236) : Code (StateDecodeRaw.alignedRaw s op p) inst p a581 a236 := by
  have h:=hc.laidOutRaw s op inst p a581 a236
  simpa only [StateDecodeRaw.alignedRaw] using h.paid (StateDecodeRaw.laidOutRaw s op p) op 5 inst p a581 a236

theorem Code.checkedRaw (s : Store NearState) (op inst : Nat) (p : Layout) (a581 a236 : Nat)
    (hc : Code s inst p a581 a236) : Code (StateDecodeRaw.checkedRaw s op p) inst p a581 a236 := by
  have h:=hc.alignedRaw s op inst p a581 a236
  simpa only [StateDecodeRaw.checkedRaw] using h.paid (StateDecodeRaw.alignedRaw s op p) op 6 inst p a581 a236

theorem Code.flagCheckedRaw (s : Store NearState) (op inst : Nat) (p : Layout) (a581 a236 : Nat)
    (hc : Code s inst p a581 a236) : Code (StateDecodeRaw.flagCheckedRaw s op p) inst p a581 a236 := by
  have h:=hc.checkedRaw s op inst p a581 a236
  simpa only [StateDecodeRaw.flagCheckedRaw] using h.paid (StateDecodeRaw.checkedRaw s op p) op 3 inst p a581 a236

theorem Code.argumentsRaw (s : Store NearState) (op inst : Nat) (p : Layout) (a581 a236 : Nat)
    (hc : Code s inst p a581 a236) : Code (StateDecodeRaw.argumentsRaw s op p) inst p a581 a236 := by
  have h:=argumentsRaw_fields s op p
  exact hc.of_fields s _ inst p a581 a236 h.1 h.2.1 h.2.2

theorem Code.argumentsRawRecord (s : Store NearState) (op inst : Nat) (p : Layout) (a581 a236 : Nat)
    (hn : Native p) (hc : Code s inst p a581 a236) :
    RecordCode (StateDecodeRaw.argumentsRaw s op p) inst (actualPositive p) a581 a236 p.address310 :=
  (hc.argumentsRaw s op inst p a581 a236).recordActual _ inst p a581 a236 hn

/-- The inner769 reservation changes only the stack global and billing fields.
Its actual record allocator installation follows without compound-store rfl. -/
theorem Code.recordReserved769 (s : Store NearState) (op inst : Nat) (p : Layout) (a581 a236 : Nat)
    (hn : Native p) (hc : Code s inst p a581 a236) :
    RecordCode (reserved769 s op p) inst (actualPositive p) a581 a236 p.address310 := by
  have hf : (reserved769 s op p).funcs=s.funcs := by simp only [reserved769,global_funcs,paid_funcs]
  have hm : (reserved769 s op p).modules=s.modules := by simp only [reserved769,global_modules,paid_modules]
  have ht : (reserved769 s op p).tables=s.tables := by simp only [reserved769,global_tables,paid_tables]
  have h:=hc.recordActual s inst p a581 a236 hn
  exact h.transport s (reserved769 s op p) inst (actualPositive p) a581 a236 p.address310 hf hm ht
end WNear.Proofs.StateDecodeRaw
