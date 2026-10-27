import Proofs.AllocateZeroedCall

/-! Exact native effects of selected f153, including zeroing relative to its
actual allocated memory rather than the original allocator metadata. -/
namespace WNear.Proofs.AllocateZeroed
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_charge)
set_option maxRecDepth 16384
attribute [local irreducible] arguments allocated checked fillArguments filled after callAfter readI32 writeI32

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with | zero=>rfl | succ n ih=>exact ih

 theorem allocated_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (allocated s op p).mems[p.memoryIndex]?=some (allocatedMemory p) := by
  unfold allocated
  apply AllocatePositive.callAfter_memory
  rw [arguments,mems_paid]
  exact hm
 theorem fillArguments_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (fillArguments s op p).mems[p.memoryIndex]?=some (allocatedMemory p) := by
  rw [fillArguments,mems_paid,checked,mems_paid]
  exact allocated_memory s op p hm
 theorem after_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (after s op p).mems[p.memoryIndex]?=some (finalMemory p) := by
  rw [after,mems_paid,filled]
  apply ZeroFill.callAfter_memory
  exact fillArguments_memory s op p hm
 theorem callAfter_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (callAfter s op p).mems[p.memoryIndex]?=some (finalMemory p) := by
  unfold callAfter
  exact after_memory (entered s op) op p hm

 theorem finalMemory_spec (p : Layout) (hn : Native p) :
    (finalMemory p).wf ∧ (finalMemory p).byteSize=p.memory.byteSize ∧ (finalMemory p).max=p.memory.max ∧
    ∀ j, (finalMemory p).read8 j=if (result p).toNat≤j ∧ j<(result p).toNat+p.size.toNat then 0 else (allocatedMemory p).read8 j := by
  have a := AllocatePositive.finalMemory_spec p.toLayout hn
  have h := ZeroFill.filledMemory_spec (allocatedMemory p) (result p) 0 p.size.toNat a.1
    (AllocatePositive.result_size_span p.toLayout hn) (AllocatePositive.result_width p.toLayout hn)
  exact ⟨h.1,h.2.1.trans a.2.1,h.2.2.1.trans a.2.2,h.2.2.2⟩

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n)=fields s := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem fields_pack (s t : Store NearState) (hf : t.funcs=s.funcs) (hm : t.modules=s.modules) (ht : t.tables=s.tables) :
    fields t=fields s := Prod.ext hf (Prod.ext hm ht)
private theorem fields_project (s t : Store NearState) (h : fields t=fields s) :
    t.funcs=s.funcs ∧ t.modules=s.modules ∧ t.tables=s.tables :=
  ⟨congrArg (fun x=>x.1) h,congrArg (fun x=>x.2.1) h,congrArg (fun x=>x.2.2) h⟩
private theorem fields_positive (s : Store NearState) (op : Nat) (p : AllocatePositive.Layout) : fields (AllocatePositive.callAfter s op p)=fields s := by
  have h := AllocatePositive.callAfter_fields s op p
  exact fields_pack s _ h.1 h.2.1 h.2.2
private theorem fields_fill (s : Store NearState) (op index : Nat) (memory : Memory) (ptr value len : UInt32) :
    fields (ZeroFill.callAfter s op index memory ptr value len)=fields s := by
  have h := ZeroFill.callAfter_fields s op index memory ptr value len
  exact fields_pack s _ h.1 h.2.1 h.2.2.1
private theorem fields_allocated (s : Store NearState) (op : Nat) (p : Layout) : fields (allocated s op p)=fields s := by
  rw [allocated,fields_positive,arguments,fields_paid]
private theorem fields_fillArguments (s : Store NearState) (op : Nat) (p : Layout) : fields (fillArguments s op p)=fields s := by
  rw [fillArguments,fields_paid,checked,fields_paid,fields_allocated]
 theorem after_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (after s op p).funcs=s.funcs ∧ (after s op p).modules=s.modules ∧ (after s op p).tables=s.tables := by
  apply fields_project
  rw [after,fields_paid,filled,fields_fill,fields_fillArguments]
 theorem callAfter_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (callAfter s op p).funcs=s.funcs ∧ (callAfter s op p).modules=s.modules ∧ (callAfter s op p).tables=s.tables := by
  unfold callAfter
  exact after_fields (entered s op) op p

 theorem after_globals (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (after s op p).globals=s.globals := by
  have a := AllocatePositive.callAfter_globals (arguments s op) op p.toLayout
    (by rw [arguments,globals_paid];exact hg) hv
  rw [after,globals_paid,filled,(ZeroFill.callAfter_fields _ _ _ _ _ _ _).2.2.2,fillArguments,globals_paid,checked,globals_paid,allocated,a,arguments,globals_paid]
 theorem callAfter_globals (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (callAfter s op p).globals=s.globals := by
  unfold callAfter
  exact after_globals (entered s op) op p hg hv

private def view (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_charge (seed : NearState) (s : Store NearState) (n : Nat) : view seed (chargedStore s n).host=view seed s.host := rfl
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) : view seed (paid s op n).host=view seed s.host := by
  induction n with | zero=>rfl | succ n ih=>exact (view_charge seed (paid s op n) op).trans ih
private theorem view_positive (seed : NearState) (s : Store NearState) (op : Nat) (p : AllocatePositive.Layout) :
    view seed (AllocatePositive.callAfter s op p).host=view seed s.host := by
  have h := congrArg (view seed) (AllocatePositive.callAfter_functional_host s op p)
  simpa only [view] using h
private theorem view_fill (seed : NearState) (s : Store NearState) (op index : Nat) (memory : Memory) (ptr value len : UInt32) :
    view seed (ZeroFill.callAfter s op index memory ptr value len).host=view seed s.host := by
  have h := congrArg (view seed) (ZeroFill.callAfter_host s op index memory ptr value len)
  simpa only [view] using h
private theorem view_allocated (seed : NearState) (s : Store NearState) (op : Nat) (p : Layout) : view seed (allocated s op p).host=view seed s.host := by
  rw [allocated,view_positive,arguments,view_paid]
private theorem view_fillArguments (seed : NearState) (s : Store NearState) (op : Nat) (p : Layout) : view seed (fillArguments s op p).host=view seed s.host := by
  rw [fillArguments,view_paid,checked,view_paid,view_allocated]
 theorem after_functional_host (s : Store NearState) (op : Nat) (p : Layout) :
    {(after s op p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (after s op p).host=s.host
  rw [after,view_paid,filled,view_fill,view_fillArguments]
  rfl
 theorem callAfter_functional_host (s : Store NearState) (op : Nat) (p : Layout) :
    {(callAfter s op p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  have h := congrArg (view s.host) (after_functional_host (entered s op) op p)
  simpa only [view,callAfter,entered,chargedStore,chargeHost] using h

 theorem gasUnits_entered (s : Store NearState) (op : Nat) : GasUnits s (entered s op) op 11 := by
  have first := gasUnits_charge s op 1
  simp only [Nat.one_mul] at first
  have h := first.trans (gasUnits_charge (chargedStore s op) op 10)
  simpa only [entered,Nat.reduceAdd] using h
 theorem gasUnits_callAfter (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (callAfter s op p) op (bodyCost p+11) := by
  have h := (gasUnits_entered s op).trans (gasUnits_after (entered s op) op p)
  simpa only [callAfter,Nat.add_comm] using h
 theorem callAfter_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits ((bodyCost p+11)*op+rest)) :
    (callAfter s op p).host.gas.burnt=s.host.gas.burnt+(bodyCost p+11)*op ∧
    (callAfter s op p).host.gas.promises=s.host.gas.promises ∧ (callAfter s op p).host.gas.Credits rest :=
  gasUnits_callAfter s op p rest hc
 theorem positive_counts (p : Layout) (hn : Native p) :
    bodyCost p+11=13*p.size.toNat+397 ∧ bodySteps p+2=12*p.size.toNat+326 := by
  simp only [bodyCost,bodySteps,ZeroFill.bodyCost,ZeroFill.bodySteps,ite_eq_right hn.positive]
  omega
end WNear.Proofs.AllocateZeroed
