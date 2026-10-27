import Proofs.AllocateSkipNative

/-! Exact resources and residual credits of the skipped-candidate root update. -/
namespace WNear.Proofs.AllocateSkip
open Wasm Wasm.Near MeteredLogic
open AllocateSearch
open StorePairCaller (paid paid_credits)
attribute [local irreducible] candidateAfter advanced hopped resumed

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih
 theorem candidate_mems (s : Store NearState) (op : Nat) : (candidateAfter s op).mems=s.mems :=
  congrArg (fun t=>t.mems) (candidateAfter_resources s op)
 theorem hopped_memory (s : Store NearState) (op : Nat) (p : Layout) (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (hopped s op p).mems[p.memoryIndex]?=some (nextMemory p) := by
  unfold hopped
  change (advanced s op p).mems[p.memoryIndex]?=_
  unfold advanced nextMemory
  apply storeI32_memory
  rw [mems_paid,candidate_mems]
  exact hm
 theorem resumed_memory (s : Store NearState) (op : Nat) (p : Layout) (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (resumed s op p).mems[p.memoryIndex]?=some (nextMemory p) := by
  rw [resumed,mems_paid]
  exact hopped_memory s op p hm
 theorem hopped_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (67*op+rest)) :
    (hopped s op p).host.gas.Credits rest := by
  have a := candidateAfter_credits s op (7*op+rest) (hc.mono (by omega))
  have b := paid_credits (candidateAfter s op) op 5 (2*op+rest) (a.mono (by omega))
  unfold hopped advanced
  exact StorePair.charged_credits _ (2*op) rest b
 theorem resumed_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (71*op+rest)) :
    (resumed s op p).host.gas.Credits rest := by
  unfold resumed
  exact paid_credits (hopped s op p) op 4 rest (hopped_credits s op (4*op+rest) p (hc.mono (by omega)))

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n)=fields s := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem fields_candidate (s : Store NearState) (op : Nat) : fields (candidateAfter s op)=fields s := by
  have h := congrArg fields (candidateAfter_resources s op)
  simpa only [fields] using h
private theorem fields_store (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt32) : fields (storeI32 s i a m v)=fields s := rfl
private theorem fields_charge (s : Store NearState) (n : Nat) : fields (chargedStore s n)=fields s := rfl
private theorem fields_project (s t : Store NearState) (h : fields t=fields s) :
    t.funcs=s.funcs ∧ t.modules=s.modules ∧ t.tables=s.tables :=
  ⟨congrArg (fun x=>x.1) h,congrArg (fun x=>x.2.1) h,congrArg (fun x=>x.2.2) h⟩
 theorem candidate_fields (s : Store NearState) (op : Nat) :
    (candidateAfter s op).funcs=s.funcs ∧ (candidateAfter s op).modules=s.modules ∧ (candidateAfter s op).tables=s.tables :=
  fields_project s _ (fields_candidate s op)
 theorem resumed_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (resumed s op p).funcs=s.funcs ∧ (resumed s op p).modules=s.modules ∧ (resumed s op p).tables=s.tables := by
  apply fields_project
  rw [resumed,fields_paid,hopped,fields_charge,advanced,fields_store,fields_paid,fields_candidate]
 theorem resumed_code (s : Store NearState) (op : Nat) (p : Layout) (inst : Nat) (hc : SearchCode s p inst) (hn : Native p) :
    SearchCode (resumed s op p) (nextLayout p) inst := by
  have nextCode := code_next s p inst hc hn
  have fs := resumed_fields s op p
  exact {nextCode.toCode.transport s _ (nextLayout p) inst fs.1 fs.2.1 fs.2.2 with
    sizeIndex:=nextCode.sizeIndex,sizeFunction:=by rw [fs.1];exact nextCode.sizeFunction}
end WNear.Proofs.AllocateSkip
