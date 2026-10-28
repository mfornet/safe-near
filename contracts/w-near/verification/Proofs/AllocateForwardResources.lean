import Proofs.AllocateForwardOuterCall

/-! Exact memory, original code/SP, functional-host and gas effects of239/313. -/
namespace WNear.Proofs.AllocateForward
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_charge gasUnits_paid)
set_option maxRecDepth 16384
attribute [local irreducible] AllocateZeroed.callAfter callAfter239 after239 callAfter313 after313

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with | zero=>rfl | succ n ih=>exact ih

theorem after239_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (after239 s op p).mems[p.memoryIndex]?=some (AllocateZeroed.finalMemory p) := by
  unfold after239
  apply AllocateZeroed.callAfter_memory
  rw [mems_paid];exact hm
 theorem callAfter239_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (callAfter239 s op p).mems[p.memoryIndex]?=some (AllocateZeroed.finalMemory p) := by
  unfold callAfter239
  exact after239_memory (entered239 s op) op p hm
 theorem callAfter313_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (callAfter313 s op p).mems[p.memoryIndex]?=some (AllocateZeroed.finalMemory p) := by
  unfold callAfter313 after313 called239
  rw [mems_paid]
  apply callAfter239_memory
  rw [mems_paid]
  exact hm

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n)=fields s := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem fields_zeroed (s : Store NearState) (op : Nat) (p : Layout) :
    fields (AllocateZeroed.callAfter s op p)=fields s := by
  have h := AllocateZeroed.callAfter_fields s op p
  exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)
private theorem fields239 (s : Store NearState) (op : Nat) (p : Layout) : fields (callAfter239 s op p)=fields s := by
  rw [callAfter239,after239,fields_zeroed,fields_paid]
  rfl
 theorem callAfter239_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (callAfter239 s op p).funcs=s.funcs ∧ (callAfter239 s op p).modules=s.modules ∧ (callAfter239 s op p).tables=s.tables := by
  have h := fields239 s op p
  exact ⟨congrArg (fun x=>x.1) h,congrArg (fun x=>x.2.1) h,congrArg (fun x=>x.2.2) h⟩
 theorem callAfter313_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (callAfter313 s op p).funcs=s.funcs ∧ (callAfter313 s op p).modules=s.modules ∧ (callAfter313 s op p).tables=s.tables := by
  have h : fields (callAfter313 s op p)=fields s := by
    rw [callAfter313,after313,fields_paid,called239,fields239,fields_paid]
    rfl
  exact ⟨congrArg (fun x=>x.1) h,congrArg (fun x=>x.2.1) h,congrArg (fun x=>x.2.2) h⟩

 theorem callAfter239_globals (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (callAfter239 s op p).globals=s.globals := by
  have gh : (paid (entered239 s op) op 3).globals[p.globalIndex]?=some p.global := by rw [globals_paid];exact hg
  have h := AllocateZeroed.callAfter_globals (paid (entered239 s op) op 3) op p gh hv
  simpa only [callAfter239,after239,globals_paid,entered239,chargedStore] using h
 theorem callAfter313_globals (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (callAfter313 s op p).globals=s.globals := by
  have gh : (paid (entered313 s op) op 2).globals[p.globalIndex]?=some p.global := by rw [globals_paid];exact hg
  rw [callAfter313,after313,globals_paid,called239,callAfter239_globals _ _ _ gh hv,globals_paid]
  rfl

private def view (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) : view seed (paid s op n).host=view seed s.host := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem view_zeroed (seed : NearState) (s : Store NearState) (op : Nat) (p : Layout) :
    view seed (AllocateZeroed.callAfter s op p).host=view seed s.host := by
  have h := congrArg (view seed) (AllocateZeroed.callAfter_functional_host s op p)
  simpa only [view] using h
private theorem view239 (seed : NearState) (s : Store NearState) (op : Nat) (p : Layout) :
    view seed (callAfter239 s op p).host=view seed s.host := by
  rw [callAfter239,after239,view_zeroed,view_paid]
  rfl
 theorem callAfter239_functional_host (s : Store NearState) (op : Nat) (p : Layout) :
    {(callAfter239 s op p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  exact view239 s.host s op p
 theorem callAfter313_functional_host (s : Store NearState) (op : Nat) (p : Layout) :
    {(callAfter313 s op p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (callAfter313 s op p).host=s.host
  rw [callAfter313,after313,view_paid,called239,view239,view_paid]
  rfl

 theorem gasUnits239 (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (callAfter239 s op p) op (cost239 p+10) := by
  have a := gasUnits_charge s op 1
  simp only [Nat.one_mul] at a
  have b := a.trans (gasUnits_charge (chargedStore s op) op 9)
  have c := b.trans (gasUnits_paid (entered239 s op) op 3)
  have d := c.trans (AllocateZeroed.gasUnits_callAfter (paid (entered239 s op) op 3) op p)
  have ce : ((1+9)+3)+(AllocateZeroed.bodyCost p+11)=cost239 p+10 := by simp only [cost239];omega
  simpa only [callAfter239,after239,ce] using d
 theorem gasUnits313 (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (callAfter313 s op p) op (cost313 p+11) := by
  have a := gasUnits_charge s op 1
  simp only [Nat.one_mul] at a
  have b := a.trans (gasUnits_charge (chargedStore s op) op 10)
  have c := b.trans (gasUnits_paid (entered313 s op) op 2)
  have d := c.trans (gasUnits239 (paid (entered313 s op) op 2) op p)
  have e := d.trans (gasUnits_paid (called239 (entered313 s op) op p) op 3)
  have ce : (((1+10)+2)+(cost239 p+10))+3=cost313 p+11 := by simp only [cost313];omega
  simpa only [callAfter313,after313,called239,ce] using e
 theorem callAfter239_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits ((cost239 p+10)*op+rest)) :
    (callAfter239 s op p).host.gas.burnt=s.host.gas.burnt+(cost239 p+10)*op ∧
    (callAfter239 s op p).host.gas.promises=s.host.gas.promises ∧ (callAfter239 s op p).host.gas.Credits rest := gasUnits239 s op p rest hc
 theorem callAfter313_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits ((cost313 p+11)*op+rest)) :
    (callAfter313 s op p).host.gas.burnt=s.host.gas.burnt+(cost313 p+11)*op ∧
    (callAfter313 s op p).host.gas.promises=s.host.gas.promises ∧ (callAfter313 s op p).host.gas.Credits rest := gasUnits313 s op p rest hc
end WNear.Proofs.AllocateForward
