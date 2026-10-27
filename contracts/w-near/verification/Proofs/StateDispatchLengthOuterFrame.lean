import Proofs.StateDispatchLengthOuterBody
import Proofs.StateDispatchLengthOuterTailFrame

/-! Exact installed-code preservation and stack-global restoration of f524. -/
namespace WNear.Proofs.StateDispatchLengthOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] arguments reserved inputStore looked

private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with | zero => rfl | succ n ih => exact ih

private theorem arguments_globals (s : Store NearState) (op : Nat) (p : Layout) :
    (arguments s op p).globals=(setGlobal s p.inner.globalIndex (.i32 (scratch p))).globals := by
  simp only [arguments,globals_paid,inputStore,storeI64_globals,reserved,setGlobal]

theorem finalStore_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (finalStore cfg s p).funcs=s.funcs ∧ (finalStore cfg s p).modules=s.modules ∧
    (finalStore cfg s p).tables=s.tables := by
  have args := arguments_fields s cfg.regularOpCost p
  have inner := StateDispatchLength.callAfter_fields cfg (arguments s cfg.regularOpCost p) p.inner
  have tail := StateDispatchLengthOuterTail.after_fields (looked cfg s p) cfg.regularOpCost
    p.inner.memoryIndex p.inner.globalIndex (StateDispatchLength.finalMemory p.inner)
    p.out (scratch p) (resultValue s p)
  simp only [looked] at tail
  simp only [finalStore,looked]
  exact ⟨tail.1.trans (inner.1.trans args.1),tail.2.1.trans (inner.2.1.trans args.2.1),
    tail.2.2.trans (inner.2.2.trans args.2.2)⟩

theorem finalStore_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hg : s.globals[p.inner.globalIndex]?=some p.global)
    (hv : p.global.value=.i32 p.sp) (hn : Native p) :
    (finalStore cfg s p).globals=s.globals := by
  have ag := arguments_global s cfg.regularOpCost p hg hn
  have av : p.inner.global.value=.i32 p.inner.sp := by rw [hn.global_eq,hn.sp_eq]
  have inner := StateDispatchLength.callAfter_globals cfg (arguments s cfg.regularOpCost p) p.inner ag av
  have look : (looked cfg s p).globals=(setGlobal s p.inner.globalIndex (.i32 (scratch p))).globals := by
    unfold looked
    exact inner.trans (arguments_globals s cfg.regularOpCost p)
  have restore := StorePairCaller.setGlobal_restore s p.inner.globalIndex (.i32 (scratch p)) p.global hg
  have pointer : scratch p+16=p.sp := UInt32.sub_add_cancel _ _
  unfold finalStore
  rw [StateDispatchLengthOuterTail.after_globals,pointer]
  simp only [setGlobal] at look restore ⊢
  rw [look]
  simpa only [hv] using restore

end WNear.Proofs.StateDispatchLengthOuter
