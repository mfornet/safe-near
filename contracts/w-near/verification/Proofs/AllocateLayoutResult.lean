import Proofs.AllocateLayoutCall
import Proofs.PanicAllocateReadback

/-! Exact layout words, footprint, stack restoration and local-call gas. -/
namespace WNear.Proofs.AllocateLayout
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32

/-- Both original input words are loaded before either output write. Output
readback and the eight-byte footprint need no input/output separation. -/
theorem final_spec (p : Layout) (hw : p.memory.wf) (hb : p.out.toNat + 8 ≤ p.memory.byteSize) :
    (finalMemory p).wf ∧ (finalMemory p).byteSize = p.memory.byteSize ∧ (finalMemory p).max = p.memory.max ∧
    readI32 (finalMemory p) p.out.toNat = size p ∧ readI32 (finalMemory p) (p.out.toNat + 4) = 1 ∧
    ∀ j, j < p.out.toNat ∨ p.out.toNat + 8 ≤ j → (finalMemory p).read8 j = p.memory.read8 j := by
  have high := writeI32_spec p.memory (p.out.toNat + 4) 1 hw (by omega)
  have bound : p.out.toNat + 4 ≤ (highMemory p).byteSize := by rw [show (highMemory p).byteSize = p.memory.byteSize from high.2.1]; omega
  have low := writeI32_spec (highMemory p) p.out.toNat (size p) high.1 bound
  have lo := PanicAllocateReadback.read_write_self (highMemory p) p.out.toNat (size p) high.1 bound
  have hi := PanicAllocateReadback.read_write_frame (highMemory p) (p.out.toNat + 4) p.out.toNat (size p) high.1 bound (by omega)
  have hi0 := PanicAllocateReadback.read_write_self p.memory (p.out.toNat + 4) 1 hw (by omega)
  refine ⟨low.1,low.2.1.trans high.2.1,low.2.2.1.trans high.2.2.1,lo,hi.trans hi0,?_⟩
  intro j hj
  unfold finalMemory
  rw [low.2.2.2]
  rw [ite_eq_right (show ¬(p.out.toNat ≤ j ∧ j < p.out.toNat + 4) by omega)]
  unfold highMemory
  rw [high.2.2.2]
  rw [ite_eq_right (show ¬(p.out.toNat + 4 ≤ j ∧ j < p.out.toNat + 4 + 4) by omega)]

private theorem paid_globals (s : Store NearState) (op n : Nat) : (paid s op n).globals = s.globals := by
  induction n with | zero => rfl | succ n ih => exact ih

theorem after_globals (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) (hsp : p.global.value = .i32 p.sp) :
    (after s op p).globals = s.globals := by
  have h := StorePairCaller.setGlobal_restore s p.globalIndex (.i32 (scratch p)) p.global hg
  simpa only [after,low,roundedStore,high,loaded,guarded,reserved,storeI32_globals,paid_globals,setGlobal,scratch,UInt32.sub_add_cancel,hsp] using h

theorem called_memory (s : Store NearState) (op : Nat) (p : Layout) (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (called s op p).mems[p.memoryIndex]? = some (finalMemory p) := after_memory (entered s op) op p hm

theorem called_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (called s op p).funcs = s.funcs ∧ (called s op p).modules = s.modules ∧ (called s op p).tables = s.tables := by
  simpa only [called,entered,chargedStore] using after_fields (entered s op) op p

theorem called_globals (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) (hsp : p.global.value = .i32 p.sp) :
    (called s op p).globals = s.globals := after_globals (entered s op) op p hg hsp

theorem called_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (44 * op + rest)) :
    (called s op p).host.gas.burnt = s.host.gas.burnt + 44 * op ∧
    (called s op p).host.gas.promises = s.host.gas.promises ∧ (called s op p).host.gas.Credits rest := by
  have c0 := GasCounter.burn_credits s.host.gas op (43 * op + rest) (hc.mono (by omega))
  have c1 := GasCounter.burn_credits (chargedStore s op).host.gas (10 * op) (33 * op + rest) (c0.2.2.2.mono (by omega))
  have c2 := after_gas (entered s op) op rest p c1.2.2.2
  refine ⟨?_,c2.2.1.trans (c1.2.2.1.trans c0.2.2.1),c2.2.2⟩
  change (after (entered s op) op p).host.gas.burnt = _
  rw [c2.1]
  change ((chargedStore s op).host.gas.burn (10 * op)).1.burnt + 33 * op = _
  rw [c1.2.1]
  change (s.host.gas.burn op).1.burnt + 10 * op + 33 * op = _
  rw [c0.2.1]; omega

end WNear.Proofs.AllocateLayout
