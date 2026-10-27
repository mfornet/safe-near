import Proofs.AllocateLayoutWrapperCall

/-! Full stack restoration, exact gas, and resources of the accepted layout wrappers. -/
namespace WNear.Proofs.AllocateLayoutWrapper
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits paid_gas)
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32

private theorem paid_globals (s : Store NearState) (op n : Nat) : (paid s op n).globals = s.globals := by
  induction n with | zero => rfl | succ n ih => exact ih

theorem after_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (after s op p).funcs = s.funcs ∧ (after s op p).modules = s.modules ∧ (after s op p).tables = s.tables := by
  simpa only [after,setGlobal,paid,chargedStore] using copied_fields s op p

theorem after_globals (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) (hsp : p.global.value = .i32 p.sp) :
    (after s op p).globals = s.globals := by
  have h := StorePairCaller.setGlobal_restore s p.globalIndex (.i32 (scratch p)) p.global hg
  simp only [after,setGlobal,copied,copyStore,storeI64_globals,paid_globals,laidOut_globals s op p hg]
  simpa only [arguments,setupStore,InterfaceSetBody.storeWord,alignmentStore,constantStore,storeI32_globals,paid_globals,
    reserved,setGlobal,scratch,UInt32.sub_add_cancel,hsp] using h

theorem laidOut_gas (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (59 * op + rest)) :
    (laidOut s op p).host.gas.burnt = s.host.gas.burnt + 59 * op ∧
    (laidOut s op p).host.gas.promises = s.host.gas.promises ∧ (laidOut s op p).host.gas.Credits rest := by
  have ca := arguments_credits s op (44 * op + rest) p (hc.mono (by omega))
  have a := paid_gas s op 15 (44 * op + rest) (hc.mono (by omega))
  have b := AllocateLayout.called_gas (arguments s op p) op rest (leafLayout p) ca
  have ab : (arguments s op p).host.gas.burnt = s.host.gas.burnt + 15 * op := by rw [arguments_host]; exact a.1
  have ap : (arguments s op p).host.gas.promises = s.host.gas.promises := by rw [arguments_host]; exact a.2
  refine ⟨?_,b.2.1.trans ap,b.2.2⟩
  change (AllocateLayout.called (arguments s op p) op (leafLayout p)).host.gas.burnt = _
  rw [b.1,ab]; omega

theorem after_gas (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (67 * op + rest)) :
    (after s op p).host.gas.burnt = s.host.gas.burnt + 67 * op ∧
    (after s op p).host.gas.promises = s.host.gas.promises ∧ (after s op p).host.gas.Credits rest := by
  have l := laidOut_gas s op (8 * op + rest) p (hc.mono (by omega))
  have c := paid_gas (laidOut s op p) op 4 (4 * op + rest) (l.2.2.mono (by omega))
  have cc := copied_credits s op (4 * op + rest) p (hc.mono (by omega))
  have r := paid_gas (copied s op p) op 4 rest cc
  have cb : (copied s op p).host.gas.burnt = (laidOut s op p).host.gas.burnt + 4 * op := c.1
  have cp : (copied s op p).host.gas.promises = (laidOut s op p).host.gas.promises := c.2
  refine ⟨?_,r.2.trans (cp.trans l.2.1),after_credits s op rest p hc⟩
  change (paid (copied s op p) op 4).host.gas.burnt = _
  rw [r.1,cb,l.1]; omega

theorem called_gas (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (78 * op + rest)) :
    (called s op p).host.gas.burnt = s.host.gas.burnt + 78 * op ∧
    (called s op p).host.gas.promises = s.host.gas.promises ∧ (called s op p).host.gas.Credits rest := by
  have c0 := GasCounter.burn_credits s.host.gas op (77 * op + rest) (hc.mono (by omega))
  have c1 := GasCounter.burn_credits (chargedStore s op).host.gas (10 * op) (67 * op + rest) (c0.2.2.2.mono (by omega))
  have c2 := after_gas (entered s op) op rest p c1.2.2.2
  refine ⟨?_,c2.2.1.trans (c1.2.2.1.trans c0.2.2.1),c2.2.2⟩
  change (after (entered s op) op p).host.gas.burnt = _
  rw [c2.1]
  change ((chargedStore s op).host.gas.burn (10 * op)).1.burnt + 67 * op = _
  rw [c1.2.1]
  change (s.host.gas.burn op).1.burnt + 10 * op + 67 * op = _
  rw [c0.2.1]; omega

theorem called_memory (s : Store NearState) (op : Nat) (p : Layout) (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (called s op p).mems[p.memoryIndex]? = some (finalMemory p) := after_memory (entered s op) op p hm

theorem called_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (called s op p).funcs = s.funcs ∧ (called s op p).modules = s.modules ∧ (called s op p).tables = s.tables := by
  simpa only [called,entered,chargedStore] using after_fields (entered s op) op p

theorem called_globals (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) (hsp : p.global.value = .i32 p.sp) :
    (called s op p).globals = s.globals := after_globals (entered s op) op p hg hsp

end WNear.Proofs.AllocateLayoutWrapper
