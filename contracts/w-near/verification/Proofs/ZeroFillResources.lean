import Proofs.ZeroFillCall
import Proofs.ZeroFillMemory

/-! Full symbolic f952 resource frames, exact gas, and interval byte semantics. -/
namespace WNear.Proofs.ZeroFill
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits paid_gas)
set_option maxRecDepth 16384
attribute [local irreducible] loopAfter iterationStore written

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


private theorem effect_charge (s : Store NearState) (op n : Nat) :
    Effect s (chargedStore s (n*op)) op n := by
  refine ⟨⟨rfl,rfl,rfl,rfl⟩,?_,?_⟩
  · simp only [Functional,chargedStore,chargeHost]
  · intro rest hc
    have h := GasCounter.burn_credits s.host.gas (n*op) rest hc
    exact ⟨h.2.1,h.2.2.1,h.2.2.2⟩

private theorem effect_byte (s : Store NearState) (op index : Nat) (memory : Memory) (ptr value : UInt32) :
    Effect s (storeByte s index ptr.toNat memory value) op 0 := by
  refine ⟨⟨rfl,rfl,rfl,rfl⟩,rfl,?_⟩
  intro rest hc
  simp only [Nat.zero_mul,Nat.zero_add] at hc
  simpa only [Nat.zero_mul,Nat.zero_add,Nat.add_zero,storeByte_host] using
    (show s.host.gas.burnt=s.host.gas.burnt ∧ s.host.gas.promises=s.host.gas.promises ∧ s.host.gas.Credits rest from ⟨rfl,rfl,hc⟩)

private theorem effect_iteration (s : Store NearState) (op index : Nat) (memory : Memory) (ptr value : UInt32) :
    Effect s (iterationStore s op index memory ptr value) op 11 := by
  have a := (effect_paid s op 3).trans _ _ _ op _ _ (effect_byte (paid s op 3) op index memory ptr value)
  have aa : Effect s (written s op index memory ptr value) op 3 := by
    simpa only [written,Nat.add_zero] using a
  have b := aa.trans _ _ _ op _ _ (effect_paid (written s op index memory ptr value) op 8)
  simpa only [Nat.add_zero,Nat.reduceAdd,iterationStore,written] using b

private theorem effect_loop (s : Store NearState) (op index : Nat) (memory : Memory)
    (ptr value count : UInt32) (n : Nat) :
    Effect s (loopAfter s op index memory ptr value count n) op (loopCost n) := by
  induction n generalizing s memory ptr count with
  | zero =>
    simpa only [loopAfter,loopCost,ite_true,paid] using effect_paid s op 0
  | succ n ih =>
    have a := (effect_iteration s op index memory ptr value).trans _ _ _ op _ _
      (effect_charge (iterationStore s op index memory ptr value) op (if n=0 then 1 else 2))
    simp only [ite_mul,Nat.one_mul] at a
    have b := a.trans _ _ _ op _ _ (ih (chargedStore (iterationStore s op index memory ptr value) (if n=0 then op else 2*op))
      (writeByte memory ptr.toNat value) (ptr+1) (nextCount count))
    simpa only [loopAfter,loopCost_succ,ite_mul,Nat.one_mul,Nat.add_assoc] using b

private theorem effect_after (s : Store NearState) (op index : Nat) (memory : Memory) (ptr value len : UInt32) :
    Effect s (after s op index memory ptr value len) op (bodyCost len) := by
  by_cases hz : len=0
  · simpa only [after,bodyCost,ite_eq_left hz] using effect_paid s op 4
  · have a := (effect_paid s op 5).trans _ _ _ op _ _ (effect_charge (paid s op 5) op 1)
    have aa : Effect s (positiveStart s op) op 6 := by
      simpa only [positiveStart,Nat.one_mul,Nat.reduceAdd] using a
    have b := aa.trans _ _ _ op _ _ (effect_loop (positiveStart s op) op index memory ptr value len len.toNat)
    have c := b.trans _ _ _ op _ _ (effect_paid (loopAfter (positiveStart s op) op index memory ptr value len len.toNat) op 1)
    have nz : len.toNat≠0 := by intro h;apply hz;exact UInt32.toNat_inj.mp h
    have cost : 6+loopCost len.toNat+1=13*len.toNat+6 := by simp only [loopCost,ite_eq_right nz];omega
    simpa only [cost,after,bodyCost,ite_eq_right hz,positiveAfter,positiveStart,Nat.one_mul] using c

private theorem effect_call (s : Store NearState) (op index : Nat) (memory : Memory) (ptr value len : UInt32) :
    Effect s (callAfter s op index memory ptr value len) op (bodyCost len+11) := by
  have one := effect_charge s op 1
  simp only [Nat.one_mul] at one
  have a := one.trans _ _ _ op _ _ (effect_charge (chargedStore s op) op 10)
  have aa : Effect s (entered s op) op 11 := by simpa only [entered,Nat.reduceAdd] using a
  have b := aa.trans _ _ _ op _ _ (effect_after (entered s op) op index memory ptr value len)
  have eq : 11+bodyCost len=bodyCost len+11 := by omega
  simpa only [eq,callAfter,entered,Nat.one_mul] using b

theorem after_fields (s : Store NearState) (op index : Nat) (memory : Memory) (ptr value len : UInt32) :
    (after s op index memory ptr value len).funcs=s.funcs ∧
    (after s op index memory ptr value len).modules=s.modules ∧
    (after s op index memory ptr value len).tables=s.tables ∧
    (after s op index memory ptr value len).globals=s.globals :=
  (effect_after s op index memory ptr value len).fields

theorem callAfter_fields (s : Store NearState) (op index : Nat) (memory : Memory) (ptr value len : UInt32) :
    (callAfter s op index memory ptr value len).funcs=s.funcs ∧
    (callAfter s op index memory ptr value len).modules=s.modules ∧
    (callAfter s op index memory ptr value len).tables=s.tables ∧
    (callAfter s op index memory ptr value len).globals=s.globals :=
  (effect_call s op index memory ptr value len).fields

theorem after_host (s : Store NearState) (op index : Nat) (memory : Memory) (ptr value len : UInt32) :
    {(after s op index memory ptr value len).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host :=
  (effect_after s op index memory ptr value len).functional

theorem callAfter_host (s : Store NearState) (op index : Nat) (memory : Memory) (ptr value len : UInt32) :
    {(callAfter s op index memory ptr value len).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host :=
  (effect_call s op index memory ptr value len).functional

theorem after_gas (s : Store NearState) (op index rest : Nat) (memory : Memory) (ptr value len : UInt32)
    (hc : s.host.gas.Credits (bodyCost len*op+rest)) :
    (after s op index memory ptr value len).host.gas.burnt=s.host.gas.burnt+bodyCost len*op ∧
    (after s op index memory ptr value len).host.gas.promises=s.host.gas.promises ∧
    (after s op index memory ptr value len).host.gas.Credits rest :=
  (effect_after s op index memory ptr value len).gas rest hc

theorem callAfter_gas (s : Store NearState) (op index rest : Nat) (memory : Memory) (ptr value len : UInt32)
    (hc : s.host.gas.Credits ((bodyCost len+11)*op+rest)) :
    (callAfter s op index memory ptr value len).host.gas.burnt=s.host.gas.burnt+(bodyCost len+11)*op ∧
    (callAfter s op index memory ptr value len).host.gas.promises=s.host.gas.promises ∧
    (callAfter s op index memory ptr value len).host.gas.Credits rest :=
  (effect_call s op index memory ptr value len).gas rest hc

theorem after_memory (s : Store NearState) (op index : Nat) (memory : Memory) (ptr value len : UInt32)
    (hm : s.mems[index]?=some memory) :
    (after s op index memory ptr value len).mems[index]?=some (filledMemory memory ptr value len.toNat) := by
  by_cases hz : len=0
  · subst len
    simpa only [after,ite_true,UInt32.toNat_zero,filledMemory,paid,chargedStore] using hm
  · unfold after
    rw [ite_eq_right hz]
    unfold positiveAfter
    have h := loopAfter_memory (positiveStart s op) op index memory ptr value len len.toNat
      (by simpa only [positiveStart,paid,chargedStore] using hm)
    simpa only [paid,chargedStore] using h

theorem callAfter_memory (s : Store NearState) (op index : Nat) (memory : Memory) (ptr value len : UInt32)
    (hm : s.mems[index]?=some memory) :
    (callAfter s op index memory ptr value len).mems[index]?=some (filledMemory memory ptr value len.toNat) := by
  apply after_memory
  simpa only [entered,chargedStore] using hm


private theorem loopAfter_other_memory (s : Store NearState) (op index other : Nat) (memory : Memory)
    (ptr value count : UInt32) (n : Nat) (hne : other≠index) :
    (loopAfter s op index memory ptr value count n).mems[other]?=s.mems[other]? := by
  induction n generalizing s memory ptr count with
  | zero => simp only [loopAfter]
  | succ n ih =>
    rw [loopAfter,ih]
    simp only [chargedStore,iterationStore,written,paid,storeByte_other_memory _ _ _ _ _ _ hne]

theorem callAfter_other_memory (s : Store NearState) (op index other : Nat) (memory : Memory)
    (ptr value len : UInt32) (hne : other≠index) :
    (callAfter s op index memory ptr value len).mems[other]?=s.mems[other]? := by
  unfold callAfter after
  split
  · simp only [paid,entered,chargedStore]
  · unfold positiveAfter
    simpa only [paid,positiveStart,entered,chargedStore] using
      loopAfter_other_memory (positiveStart (entered s op) op) op index other memory ptr value len len.toNat hne

/-- Exact installed bytes and full memory frame, derived from original span bounds. -/
theorem callAfter_memory_spec (s : Store NearState) (op index : Nat) (memory : Memory) (ptr value len : UInt32)
    (hm : s.mems[index]?=some memory) (hw : memory.wf)
    (hb : ptr.toNat+len.toNat≤memory.byteSize) (hwidth : ptr.toNat+len.toNat≤2^32) :
    ∃ result, (callAfter s op index memory ptr value len).mems[index]?=some result ∧ result.wf ∧
      result.byteSize=memory.byteSize ∧ result.max=memory.max ∧
      ∀ j, result.read8 j=if ptr.toNat≤j ∧ j<ptr.toNat+len.toNat then UInt8.ofNat value.toNat else memory.read8 j := by
  exact ⟨filledMemory memory ptr value len.toNat,callAfter_memory s op index memory ptr value len hm,
    filledMemory_spec memory ptr value len.toNat hw hb hwidth⟩
end WNear.Proofs.ZeroFill
