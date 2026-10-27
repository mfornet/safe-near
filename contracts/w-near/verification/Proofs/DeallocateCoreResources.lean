import Proofs.DeallocateCoreBody
import Proofs.DeallocateListSizeFrame

/-! Functional resource frames and exact gas for the actual coalescing path. -/
namespace WNear.Proofs.DeallocateCore
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits paid_gas)
set_option maxRecDepth 16384

private def Functional (s t : Store NearState) : Prop :=
  {t.host with gas := s.host.gas,gasProfile := s.host.gasProfile} = s.host

private theorem functional_trans (s t u : Store NearState) (ht : Functional s t) (hu : Functional t u) :
    Functional s u := by
  unfold Functional at *
  calc
    {u.host with gas := s.host.gas,gasProfile := s.host.gasProfile} =
        {{u.host with gas := t.host.gas,gasProfile := t.host.gasProfile} with gas := s.host.gas,gasProfile := s.host.gasProfile} := rfl
    _ = {t.host with gas := s.host.gas,gasProfile := s.host.gasProfile} :=
      congrArg (fun h : NearState => {h with gas := s.host.gas,gasProfile := s.host.gasProfile}) hu
    _ = s.host := ht

private structure Effect (s t : Store NearState) (op count : Nat) : Prop where
  fields : t.funcs = s.funcs ∧ t.modules = s.modules ∧ t.tables = s.tables ∧ t.globals = s.globals
  functional : Functional s t
  gas : ∀ rest, s.host.gas.Credits (count * op + rest) →
    t.host.gas.burnt = s.host.gas.burnt + count * op ∧
    t.host.gas.promises = s.host.gas.promises ∧ t.host.gas.Credits rest

private theorem Effect.trans (s t u : Store NearState) (op a b : Nat) (ht : Effect s t op a) (hu : Effect t u op b) :
    Effect s u op (a + b) := by
  refine ⟨⟨hu.fields.1.trans ht.fields.1,hu.fields.2.1.trans ht.fields.2.1,
    hu.fields.2.2.1.trans ht.fields.2.2.1,hu.fields.2.2.2.trans ht.fields.2.2.2⟩,
    functional_trans s t u ht.functional hu.functional,?_⟩
  intro rest hc
  have h1 := ht.gas (b * op + rest) (hc.mono (by simp only [Nat.add_mul]; omega))
  have h2 := hu.gas rest h1.2.2
  refine ⟨?_,h2.2.1.trans h1.2.1,h2.2.2⟩
  rw [h2.1,h1.1,Nat.add_mul]; omega

private theorem effect_paid (s : Store NearState) (op n : Nat) : Effect s (paid s op n) op n := by
  have fields : (paid s op n).funcs = s.funcs ∧ (paid s op n).modules = s.modules ∧
      (paid s op n).tables = s.tables ∧ (paid s op n).globals = s.globals := by
    induction n with
    | zero => exact ⟨rfl,rfl,rfl,rfl⟩
    | succ n ih => exact ih
  have host : Functional s (paid s op n) := by
    clear fields
    induction n with
    | zero => rfl
    | succ n ih => simpa only [Functional,paid,chargedStore,chargeHost] using ih
  refine ⟨fields,host,?_⟩
  intro rest hc
  have h := paid_gas s op n rest hc
  exact ⟨h.1,h.2,paid_credits s op n rest hc⟩

private theorem effect_store (s : Store NearState) (op index address : Nat) (memory : Memory) (value : UInt32) :
    Effect s (storeI32 s index address memory value) op 0 := by
  refine ⟨⟨rfl,rfl,rfl,rfl⟩,rfl,?_⟩
  intro rest hc
  simp only [Nat.zero_mul,Nat.zero_add] at hc
  simpa only [Nat.zero_mul,Nat.zero_add,Nat.add_zero,storeI32_host] using (show s.host.gas.burnt = s.host.gas.burnt ∧ s.host.gas.promises = s.host.gas.promises ∧ s.host.gas.Credits rest from ⟨rfl,rfl,hc⟩)

private theorem effect_570 (s : Store NearState) (op : Nat) : Effect s (DeallocateAlign.after570 s op) op 41 := by
  have hf := congrArg (fun t : Store NearState => (t.funcs,t.modules,t.tables,t.globals)) (DeallocateAlign.after570_resources s op)
  simp only at hf
  have f1 := congrArg (fun t => t.1) hf
  have f2 := congrArg (fun t => t.2.1) hf
  have f3 := congrArg (fun t => t.2.2.1) hf
  have f4 := congrArg (fun t => t.2.2.2) hf
  simp only at f1 f2 f3 f4
  refine ⟨⟨f1,f2,f3,f4⟩,DeallocateAlign.after570_functional_host s op,?_⟩
  intro rest hc
  have h := DeallocateAlign.after570_gas s op rest hc
  exact ⟨h.1,h.2,DeallocateAlign.after570_credits s op rest hc⟩

private theorem effect_size (s : Store NearState) (op : Nat) : Effect s (DeallocateListSize.after s op) op 25 := by
  have hf := congrArg (fun t : Store NearState => (t.funcs,t.modules,t.tables,t.globals)) (DeallocateListSize.after_resources s op)
  simp only at hf
  have f1 := congrArg (fun t => t.1) hf
  have f2 := congrArg (fun t => t.2.1) hf
  have f3 := congrArg (fun t => t.2.2.1) hf
  have f4 := congrArg (fun t => t.2.2.2) hf
  simp only at f1 f2 f3 f4
  refine ⟨⟨f1,f2,f3,f4⟩,DeallocateListSize.after_host s op,?_⟩
  exact DeallocateListSize.after_gas s op

private theorem effect_align (s : Store NearState) (op : Nat) : Effect s (Deallocate.aligned s op) op 43 := by
  exact (effect_paid s op 1).trans _ _ _ op _ _
    ((effect_570 (paid s op 1) op).trans _ _ _ op _ _ (effect_paid (DeallocateAlign.after570 (paid s op 1) op) op 1))
private theorem effect_sized (s : Store NearState) (op : Nat) : Effect s (Deallocate.sized s op) op 27 := by
  exact (effect_paid s op 1).trans _ _ _ op _ _
    ((effect_size (paid s op 1) op).trans _ _ _ op _ _ (effect_paid (DeallocateListSize.after (paid s op 1) op) op 1))

private theorem effect_unlink (s : Store NearState) (op : Nat) (p : Layout) :
    Effect s (DeallocateCoreUnlink.unlinkFrom s op p) op 73 := by
  have host := DeallocateListCall.called_host (paid s op 1) op (unlinkLayout p)
  have hp := (effect_paid s op 1).functional
  have hu : Functional (paid s op 1) (DeallocateCoreUnlink.unlinkFrom s op p) := by
    simpa only [Functional,DeallocateCoreUnlink.unlinkFrom,DeallocateListCall.called,DeallocateListCall.entered,unlinkEntered] using host
  exact ⟨DeallocateCoreUnlink.unlinkFrom_fields s op p,functional_trans s (paid s op 1) _ hp hu,
    fun rest hc => DeallocateCoreUnlink.unlinkFrom_gas s op rest p hc⟩

private theorem effect_after (s : Store NearState) (op : Nat) (p : Layout) : Effect s (after s op p) op 218 := by
  have g0 : Effect s (guarded s op) op 6 := effect_paid s op 6
  have g1 : Effect s (aligned s op) op 49 := g0.trans _ _ _ op _ _ (effect_align (guarded s op) op)
  have g2 : Effect s (saved s op) op 52 := g1.trans _ _ _ op _ _ (effect_paid (aligned s op) op 3)
  have mark := (effect_paid (saved s op) op 9).trans _ _ _ op _ _
    (effect_store (paid (saved s op) op 9) op p.memoryIndex p.header.toNat p.memory (readI32 p.memory p.header.toNat &&& 4294967294))
  have g3 : Effect s (marked s op p) op 61 := g2.trans _ _ _ op _ _ mark
  have g4 : Effect s (sized s op p) op 88 := g3.trans _ _ _ op _ _ (effect_sized (marked s op p) op)
  have zero := (effect_paid (sized s op p) op 3).trans _ _ _ op _ _
    (effect_store (paid (sized s op p) op 3) op p.memoryIndex p.pointer.toNat (markedMemory p) 0)
  have g5 : Effect s (zeroed s op p) op 91 := g4.trans _ _ _ op _ _ zero
  have g6 : Effect s (previousSelected s op p) op 106 := g5.trans _ _ _ op _ _ (effect_paid (zeroed s op p) op 15)
  have g7 : Effect s (unlinked s op p) op 179 := g6.trans _ _ _ op _ _ (effect_unlink (previousSelected s op p) op p)
  have g8 : Effect s (flagChecked s op p) op 185 := g7.trans _ _ _ op _ _ (effect_paid (unlinked s op p) op 6)
  have g9 : Effect s (previousSized s op p) op 212 := g8.trans _ _ _ op _ _ (effect_sized (flagChecked s op p) op)
  have g10 : Effect s (restored s op p) op 215 := g9.trans _ _ _ op _ _ (effect_paid (previousSized s op p) op 3)
  have finish := (effect_paid (restored s op p) op 3).trans _ _ _ op _ _
    (effect_store (paid (restored s op p) op 3) op p.memoryIndex p.allocator.toNat (unlinkedMemory p) (oldHead p))
  exact g10.trans _ _ _ op _ _ finish

/-- Functions, module instances, tables and globals are unchanged. -/
theorem after_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (after s op p).funcs = s.funcs ∧ (after s op p).modules = s.modules ∧
    (after s op p).tables = s.tables ∧ (after s op p).globals = s.globals := (effect_after s op p).fields

/-- All functional host fields are retained apart from gas and its profile. -/
theorem after_functional_host (s : Store NearState) (op : Nat) (p : Layout) :
    {(after s op p).host with gas := s.host.gas,gasProfile := s.host.gasProfile} = s.host := (effect_after s op p).functional

/-- Exact paid opcode cost, reserved-gas frame, and residual credit. -/
theorem after_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (218 * op + rest)) :
    (after s op p).host.gas.burnt = s.host.gas.burnt + 218 * op ∧
    (after s op p).host.gas.promises = s.host.gas.promises ∧ (after s op p).host.gas.Credits rest :=
  (effect_after s op p).gas rest hc

private theorem effect_charge (s : Store NearState) (op count : Nat) :
    Effect s (chargedStore s (count * op)) op count := by
  refine ⟨⟨rfl,rfl,rfl,rfl⟩,?_,?_⟩
  · simp only [Functional,chargedStore,chargeHost]
  · intro rest hc
    have h := GasCounter.burn_credits s.host.gas (count * op) rest hc
    exact ⟨h.2.1,h.2.2.1,h.2.2.2⟩

private theorem effect_callAfter (s : Store NearState) (op : Nat) (p : Layout) : Effect s (callAfter s op p) op 231 := by
  have e1 : Effect s (chargedStore s op) op 1 := by simpa only [Nat.one_mul] using effect_charge s op 1
  have entry : Effect s (entered s op) op 13 := e1.trans _ _ _ op _ _ (effect_charge (chargedStore s op) op 12)
  exact entry.trans _ _ _ op _ _ (effect_after (entered s op) op p)

/-- The complete local call also frames every immutable guest resource. -/
theorem callAfter_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (callAfter s op p).funcs = s.funcs ∧ (callAfter s op p).modules = s.modules ∧
    (callAfter s op p).tables = s.tables ∧ (callAfter s op p).globals = s.globals := (effect_callAfter s op p).fields

theorem callAfter_functional_host (s : Store NearState) (op : Nat) (p : Layout) :
    {(callAfter s op p).host with gas := s.host.gas,gasProfile := s.host.gasProfile} = s.host := (effect_callAfter s op p).functional

/-- Entry activation, caller opcode, and all body charges sum to231units. -/
theorem callAfter_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (231 * op + rest)) :
    (callAfter s op p).host.gas.burnt = s.host.gas.burnt + 231 * op ∧
    (callAfter s op p).host.gas.promises = s.host.gas.promises ∧ (callAfter s op p).host.gas.Credits rest :=
  (effect_callAfter s op p).gas rest hc

end WNear.Proofs.DeallocateCore
