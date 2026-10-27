import Proofs.SerializeMultiplyCall
import Proofs.StorePairReadback

/-! Readback, footprint, resources and exact billing of the actual f954 stores. -/
namespace WNear.Proofs.SerializeMultiply
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits paid_gas)
attribute [local irreducible] readI64 writeI64

theorem finalMemory_spec (memory : Memory) (w : Words) (hw : memory.wf) (hb : w.out.toNat+16 ≤ memory.byteSize) :
    (finalMemory memory w).wf ∧ (finalMemory memory w).byteSize=memory.byteSize ∧ (finalMemory memory w).max=memory.max ∧
    readI64 (finalMemory memory w) w.out.toNat=lowWord w ∧
    readI64 (finalMemory memory w) (w.out.toNat+8)=highWord w ∧
    ∀ j, j<w.out.toNat ∨ w.out.toNat+16≤j → (finalMemory memory w).read8 j=memory.read8 j := by
  have lo := writeI64_spec memory w.out.toNat (lowWord w) hw (by omega)
  have highBound : w.out.toNat+8+8 ≤ (lowMemory memory w).byteSize := by rw [show (lowMemory memory w).byteSize=memory.byteSize from lo.2.1]; omega
  have hi := writeI64_spec (lowMemory memory w) (w.out.toNat+8) (highWord w) lo.1 highBound
  have lowRead : readI64 (finalMemory memory w) w.out.toNat=lowWord w := by
    apply StorePairReadback.readI64_of_bytes
    intro i h
    rw [show (finalMemory memory w).read8 (w.out.toNat+i)=_ from hi.2.2.2 _]
    rw [ite_eq_right (show ¬(w.out.toNat+8≤w.out.toNat+i ∧ w.out.toNat+i<w.out.toNat+8+8) by omega)]
    rw [show (lowMemory memory w).read8 (w.out.toNat+i)=_ from lo.2.2.2 _]
    rw [ite_eq_left (show w.out.toNat≤w.out.toNat+i ∧ w.out.toNat+i<w.out.toNat+8 by omega)]
    simp only [Nat.add_sub_cancel_left]
  have highRead : readI64 (finalMemory memory w) (w.out.toNat+8)=highWord w := by
    apply StorePairReadback.readI64_of_bytes
    intro i h
    rw [show (finalMemory memory w).read8 (w.out.toNat+8+i)=_ from hi.2.2.2 _]
    rw [ite_eq_left (show w.out.toNat+8≤w.out.toNat+8+i ∧ w.out.toNat+8+i<w.out.toNat+8+8 by omega)]
    simp only [Nat.add_sub_cancel_left]
  refine ⟨hi.1,hi.2.1.trans lo.2.1,hi.2.2.1.trans lo.2.2.1,lowRead,highRead,?_⟩
  intro j hj
  rw [show (finalMemory memory w).read8 j=_ from hi.2.2.2 j]
  rw [ite_eq_right (show ¬(w.out.toNat+8≤j ∧ j<w.out.toNat+8+8) by omega)]
  rw [show (lowMemory memory w).read8 j=_ from lo.2.2.2 j]
  rw [ite_eq_right (show ¬(w.out.toNat≤j ∧ j<w.out.toNat+8) by omega)]

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero => rfl | succ n ih => exact ih

theorem after_memory (s : Store NearState) (op index : Nat) (memory : Memory) (w : Words)
    (hm : s.mems[index]?=some memory) : (after s op index memory w).mems[index]?=some (finalMemory memory w) := by
  have low : (lowStore s op index memory w).mems[index]?=some (lowMemory memory w) := by
    unfold lowStore lowMemory
    apply storeI64_memory
    rw [mems_paid]
    exact hm
  unfold after finalMemory
  apply storeI64_memory
  rw [mems_paid]
  exact low

theorem callAfter_memory (s : Store NearState) (op index : Nat) (memory : Memory) (w : Words)
    (hm : s.mems[index]?=some memory) : (callAfter s op index memory w).mems[index]?=some (finalMemory memory w) :=
  after_memory (entered s op) op index memory w hm

private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with | zero => rfl | succ n ih => exact ih

theorem after_globals (s : Store NearState) (op index : Nat) (memory : Memory) (w : Words) :
    (after s op index memory w).globals=s.globals := by
  simp only [after,lowStore,storeI64_globals,globals_paid]

theorem callAfter_globals (s : Store NearState) (op index : Nat) (memory : Memory) (w : Words) :
    (callAfter s op index memory w).globals=s.globals := after_globals (entered s op) op index memory w

private theorem paid_host_congr (s t : Store NearState) (op n : Nat) (h : s.host=t.host) :
    (paid s op n).host=(paid t op n).host := by
  induction n with
  | zero => exact h
  | succ n ih => exact congrArg (fun host => (chargeHost host op).1) ih

private theorem paid_combine (s : Store NearState) (op a b : Nat) : paid (paid s op a) op b=paid s op (a+b) := by
  induction b with
  | zero => rfl
  | succ b ih => simp only [paid,ih]; rfl

theorem after_host_eq (s : Store NearState) (op index : Nat) (memory : Memory) (w : Words) :
    (after s op index memory w).host=(paid s op 60).host := by
  have lo : (lowStore s op index memory w).host=(paid s op 31).host := rfl
  have hi := paid_host_congr (lowStore s op index memory w) (paid s op 31) op 29 lo
  simpa only [after,storeI64_host,paid_combine,Nat.reduceAdd] using hi

theorem after_gas (s : Store NearState) (op index rest : Nat) (memory : Memory) (w : Words)
    (hc : s.host.gas.Credits (60*op+rest)) :
    (after s op index memory w).host.gas.burnt=s.host.gas.burnt+60*op ∧
    (after s op index memory w).host.gas.promises=s.host.gas.promises ∧
    (after s op index memory w).host.gas.Credits rest := by
  rw [after_host_eq]
  exact ⟨(paid_gas s op 60 rest hc).1,(paid_gas s op 60 rest hc).2,paid_credits s op 60 rest hc⟩

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n)=fields s := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem fields_store (s : Store NearState) (index address : Nat) (memory : Memory) (v : UInt64) : fields (storeI64 s index address memory v)=fields s := rfl
private theorem fields_project (s t : Store NearState) (h : fields t=fields s) :
    t.funcs=s.funcs ∧ t.modules=s.modules ∧ t.tables=s.tables :=
  ⟨congrArg (fun x=>x.1) h,congrArg (fun x=>x.2.1) h,congrArg (fun x=>x.2.2) h⟩
theorem after_fields (s : Store NearState) (op index : Nat) (memory : Memory) (w : Words) :
    (after s op index memory w).funcs=s.funcs ∧ (after s op index memory w).modules=s.modules ∧ (after s op index memory w).tables=s.tables := by
  have h : fields (after s op index memory w)=fields s := by simp only [after,lowStore,fields_store,fields_paid]
  exact fields_project s _ h

theorem callAfter_fields (s : Store NearState) (op index : Nat) (memory : Memory) (w : Words) :
    (callAfter s op index memory w).funcs=s.funcs ∧ (callAfter s op index memory w).modules=s.modules ∧ (callAfter s op index memory w).tables=s.tables :=
  after_fields (entered s op) op index memory w

private def hostView (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_charge (seed : NearState) (s : Store NearState) (cost : Nat) :
    hostView seed (chargedStore s cost).host=hostView seed s.host := by simp only [hostView,chargedStore,chargeHost]
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) :
    hostView seed (paid s op n).host=hostView seed s.host := by
  induction n with | zero => rfl | succ n ih => exact (view_charge seed (paid s op n) op).trans ih

theorem after_host (s : Store NearState) (op index : Nat) (memory : Memory) (w : Words) :
    {(after s op index memory w).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  rw [after_host_eq]
  exact view_paid s.host s op 60

theorem callAfter_host (s : Store NearState) (op index : Nat) (memory : Memory) (w : Words) :
    {(callAfter s op index memory w).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change hostView s.host (callAfter s op index memory w).host=s.host
  rw [callAfter,after_host_eq,view_paid,entered,view_charge,view_charge]
  rfl

theorem callAfter_gas (s : Store NearState) (op index rest : Nat) (memory : Memory) (w : Words)
    (hc : s.host.gas.Credits (81*op+rest)) :
    (callAfter s op index memory w).host.gas.burnt=s.host.gas.burnt+81*op ∧
    (callAfter s op index memory w).host.gas.promises=s.host.gas.promises ∧
    (callAfter s op index memory w).host.gas.Credits rest := by
  have cut : op+(20*op+(60*op+rest)) ≤ 81*op+rest := by omega
  have c0 := GasCounter.burn_credits s.host.gas op _ (hc.mono cut)
  have c1 := GasCounter.burn_credits (chargedStore s op).host.gas (20*op) _ c0.2.2.2
  have c2 := after_gas (entered s op) op index rest memory w c1.2.2.2
  refine ⟨?_,c2.2.1.trans (c1.2.2.1.trans c0.2.2.1),c2.2.2⟩
  change (after (entered s op) op index memory w).host.gas.burnt=_
  rw [c2.1]
  change ((chargedStore s op).host.gas.burn (20*op)).1.burnt+60*op=_
  rw [c1.2.1]
  change (s.host.gas.burn op).1.burnt+20*op+60*op=_
  rw [c0.2.1]
  omega

end WNear.Proofs.SerializeMultiply
