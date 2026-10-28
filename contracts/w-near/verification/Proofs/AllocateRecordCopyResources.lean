import Proofs.AllocateRecordCopyFrame
import Proofs.AllocateRecordResult

/-! Original SP and functional-host frames across690's actual nested call. -/
namespace WNear.Proofs.AllocateRecordCopy
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] allocated copyDone after AllocateRecord.after

private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem globals_recordEntered (s : Store NearState) (op : Nat) : (recordEntered s op).globals=s.globals := rfl
private theorem globals_store (s : Store NearState) (index address : Nat) (memory : Memory) (v : UInt32) : (storeI32 s index address memory v).globals=s.globals := rfl

theorem arguments_global (s : Store NearState) (op : Nat) (p : Layout) (hn : Native p)
    (hg : s.globals[p.inner.globalIndex]?=some p.global) :
    (arguments s op p).globals[p.inner.globalIndex]?=some p.inner.global := by
  rw [arguments,globals_paid,reserved]
  simp only [setGlobal,globals_paid,Array.getElem?_modify,hg,Option.map_some]
  rw [hn.innerGlobal]
  simp only [ite_true]

theorem allocated_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hg : s.globals[p.inner.globalIndex]?=some p.global) :
    (allocated cfg s p).globals=(setGlobal s p.inner.globalIndex (.i32 p.inner.sp)).globals := by
  have gh : (recordEntered (arguments s cfg.regularOpCost p) cfg.regularOpCost).globals[p.inner.globalIndex]?=some p.inner.global :=
    by rw [globals_recordEntered];exact arguments_global s cfg.regularOpCost p hn hg
  have hv : p.inner.global.value=.i32 p.inner.sp := by rw [hn.innerGlobal]
  have frame := AllocateRecord.after_globals cfg (recordEntered (arguments s cfg.regularOpCost p) cfg.regularOpCost) p.inner gh hv
  simpa only [allocated,globals_recordEntered,arguments,globals_paid,reserved,setGlobal] using frame

theorem copyDone_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hg : s.globals[p.inner.globalIndex]?=some p.global) :
    (copyDone cfg s p).globals=(setGlobal s p.inner.globalIndex (.i32 p.inner.sp)).globals := by
  rw [copyDone,copied,copyWord,globals_store,globals_paid,copyWord,globals_store,globals_paid]
  exact allocated_globals cfg s p hn hg

theorem after_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hg : s.globals[p.inner.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (after cfg s p).globals=s.globals := by
  have restore := StorePairCaller.setGlobal_restore s p.inner.globalIndex (.i32 p.inner.sp) p.global hg
  rw [after]
  simp only [setGlobal,globals_paid]
  rw [copyDone_globals cfg s p hn hg]
  simpa only [setGlobal,hv] using restore

private def view (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) : view seed (paid s op n).host=view seed s.host := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem view_global (seed : NearState) (s : Store NearState) (i : Nat) (v : Value) : view seed (setGlobal s i v).host=view seed s.host := rfl
private theorem view_charge (seed : NearState) (s : Store NearState) (n : Nat) : view seed (chargedStore s n).host=view seed s.host := rfl
private theorem view_store (seed : NearState) (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt32) : view seed (storeI32 s i a m v).host=view seed s.host := rfl
private theorem view_record (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : AllocateRecord.Layout) :
    view seed (AllocateRecord.after cfg s p).host=view seed s.host := by
  have h := congrArg (view seed) (AllocateRecord.after_functional_host cfg s p)
  exact h

theorem after_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(after cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (after cfg s p).host=s.host
  rw [after,view_global,view_paid,copyDone,copied,copyWord,view_store,view_paid,copyWord,view_store,view_paid,
    allocated,view_record,recordEntered,view_charge,view_charge,arguments,view_paid,reserved,view_global,view_paid]
  rfl
end WNear.Proofs.AllocateRecordCopy
