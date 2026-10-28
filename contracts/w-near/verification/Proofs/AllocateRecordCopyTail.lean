import Proofs.AllocateRecordCopyResources
import Proofs.AllocateRecordCopyGas

/-! Actual690's two sequential copies and final SP restoration. -/
namespace WNear.Proofs.AllocateRecordCopy
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode allocated copyDone after

theorem wp_tail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : Code s frame.inst p)
    (h0 : frame.locals[0]?=some (.i32 p.out)) (h3 : frame.locals[3]?=some (.i32 p.inner.sp))
    (hm : s.mems[p.inner.memoryIndex]?=some p.inner.memory)
    (hg : s.globals[p.inner.globalIndex]?=some p.global)
    (hc : s.host.gas.Credits (bodyCost p*cfg.regularOpCost+fee cfg p+rest))
    (hnext : WP cfg fuel (.next (atCode (after cfg s p) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+12) (.next (atCode (allocated cfg s p) limits base.toArray frame callers
      (WNear.Binary.AllocateRecordCopy.copy++WNear.Binary.AllocateRecordCopy.restore++code)))
      (12*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have ca : (allocated cfg s p).host.gas.Credits (12*op+rest) :=
    (allocated_gas cfg s p).credits (hc.mono (by simp only [bodyCost,op,Nat.add_mul];omega))
  have cc : (copyDone cfg s p).host.gas.Credits (4*op+rest) :=
    (copyDone_gas cfg s p).credits (hc.mono (by simp only [bodyCost,op,Nat.add_mul];omega))
  have fieldsC := copyDone_fields cfg s p
  have moduleC : (copyDone cfg s p).modules[frame.inst]?=some p.inner.mi := by
    rw [fieldsC.2.1];exact hcode.inner.allocation.retry.originalCode.search.module
  have globalC : (copyDone cfg s p).globals[p.inner.globalIndex]?=some p.inner.global := by
    rw [copyDone_globals cfg s p hn hg,hn.innerGlobal]
    simp only [setGlobal,Array.getElem?_modify,hg,Option.map_some,ite_true]
  have sp : p.inner.sp+16=p.sp := by rw [hn.innerSP];exact UInt32.sub_add_cancel p.sp 16
  have restoreNext : WP cfg fuel (.next (atCode (setGlobal (StorePairCaller.paid (copyDone cfg s p) cfg.regularOpCost 4) p.inner.globalIndex (.i32 (p.inner.sp+16)))
      limits base.toArray frame callers code)) rest post := by simpa only [sp,after] using hnext
  have restore := ValueReturnBorrow.wp_restore cfg fuel rest (copyDone cfg s p) limits base.toArray frame callers code p.inner.mi p.inner.globalIndex
    p.inner.global p.inner.sp 3 post h3 moduleC hcode.inner.allocation.retry.originalCode.globalIndex globalC cc restoreNext
  have fieldsA := allocated_fields cfg s p
  have moduleA : (allocated cfg s p).modules[frame.inst]?=some p.inner.mi := by
    rw [fieldsA.2.1];exact hcode.inner.allocation.retry.originalCode.search.module
  have shape := allocated_spec p hn
  have next : WP cfg (fuel+4) (.next (atCode (copied (allocated cfg s p) op p.inner.memoryIndex p.out p.inner.sp (allocatedMemory p)) limits base.toArray frame callers
      (WNear.Binary.AllocateRecordCopy.restore++code))) (4*op+rest) post := by
    simpa only [copyDone,WNear.Binary.AllocateRecordCopy.restore,op,Nat.add_assoc,Nat.reduceAdd] using restore
  have copy := wp_copy cfg (fuel+4) (4*op+rest) (allocated cfg s p) limits base.toArray frame callers
    (WNear.Binary.AllocateRecordCopy.restore++code) p.out p.inner.sp p.inner.mi p.inner.memoryIndex (allocatedMemory p) post h0 h3 moduleA
    hcode.inner.allocation.retry.originalCode.search.memoryIndex (allocated_memory cfg s p hm) shape.1
    (hn.scratchBound.trans shape.2.1) (hn.outputBound.trans shape.2.1) (ca.mono (by simp only [op];omega)) next
  have ce : 8*cfg.regularOpCost+(4*op+rest)=12*cfg.regularOpCost+rest := by simp only [op];omega
  rw [ce] at copy
  simpa only [WNear.Binary.AllocateRecordCopy.copy,List.append_assoc,Nat.add_assoc,Nat.reduceAdd] using copy
end WNear.Proofs.AllocateRecordCopy
