import Proofs.ValueReturnOuterPrefix
import Proofs.ValueReturnDispatchGas

/-! Isolate dispatch and cleanup over an arbitrary store, keeping the kernel
from normalizing the preceding acquisition store while composing the proof. -/
namespace WNear.Proofs.ValueReturnOuterDispatchTail
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.ValueReturnOuterBody WNear.Proofs.ValueReturnOuter
set_option maxRecDepth 16384
set_option maxHeartbeats 800000

/-- Actual dispatch, release, nested-block exit, status check and restoration. -/
theorem wp_tail (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (cell counter : UInt32) (memory : Memory) (global : GlobalInst) (post : Post)
    (hcoded : Code s p frame.inst extra)
    (hzero : frame.locals[0]? = some (.i32 0)) (hslice : frame.locals[1]? = some (.i32 p.slice))
    (hscratch : frame.locals[2]? = some (.i32 (scratch p))) (hsize : 4 ≤ frame.locals.size)
    (hmem : s.mems[p.memoryIndex]? = some memory) (hglobal : s.globals[p.globalIndex]? = some global)
    (hsp : global.value = .i32 (scratch p))
    (hcell : cell.toNat + 8 ≤ memory.byteSize) (hspan : p.slice.toNat + 8 ≤ memory.byteSize)
    (hvtable : p.vtable.toNat + 96 ≤ memory.byteSize)
    (hreceiver : readI32 memory cell.toNat = p.receiver)
    (hvtableRead : readI32 memory (cell.toNat + 4) = p.vtable)
    (helement : readI32 memory (p.vtable.toNat + 92) = p.returnElement)
    (hlen : ValueReturnDispatch.packed32 memory (p.slice.toNat + 4) = p.len)
    (hptr : ValueReturnDispatch.packed32 memory p.slice.toNat = p.ptr)
    (hfixed : p.len ≠ u64Max) (hbound : p.ptr.toNat + p.len.toNat ≤ memory.byteSize)
    (hlimit : withinLimit s.host.config.maxReturnLen p.len.toNat = true)
    (hcounter : readI32 memory (((scratch p + 8) ||| 4).toNat) = counter)
    (hrecordBound : ((scratch p + 8) ||| 4).toNat + 4 ≤ memory.byteSize)
    (hcounterBound : counter.toNat + 4 ≤ memory.byteSize)
    (hdepth : callers.length + 2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (93 * cfg.regularOpCost + ValueReturnHost.cost s.host p.len.toNat + rest))
    (hnext : WP cfg fuel (.next (atCode
      (cleanupAfter (ValueReturnDispatch.fragmentAfter cfg s p.mi p.len p.ptr) cfg.regularOpCost
        p.globalIndex p.memoryIndex (scratch p) counter memory) limits base.toArray
      (ValueReturnDispatch.dispatchFrame frame cell) callers code)) rest post) :
    WP cfg (fuel + 59) (.next (atCode s limits (base.toArray.push (.i32 cell))
      (ValueReturnOuterPrefix.nested frame base.toArray.size code) callers
      (WNear.Binary.ValueReturnDispatch.dispatch ++ WNear.Binary.ValueReturnOuter.cleanup)))
      (93 * cfg.regularOpCost + ValueReturnHost.cost s.host p.len.toNat + rest) post := by
  let after := ValueReturnDispatch.fragmentAfter cfg s p.mi p.len p.ptr
  let nextFrame := ValueReturnDispatch.dispatchFrame frame cell
  let nested := ValueReturnOuterPrefix.nested frame base.toArray.size code
  have resource := ValueReturnDispatchGas.fragmentAfter_resources cfg s p.mi p.len p.ptr
  have hf := congrArg (fun t : Store NearState => t.funcs) resource
  change after.funcs = s.funcs at hf
  have hm := congrArg (fun t : Store NearState => t.modules) resource
  change after.modules = s.modules at hm
  have ht := congrArg (fun t : Store NearState => t.tables) resource
  change after.tables = s.tables at ht
  have hg : after.globals[p.globalIndex]? = some global :=
    (congrArg (fun t : Store NearState => t.globals[p.globalIndex]?) resource).trans hglobal
  have c := hcoded.transport s after p frame.inst extra hf hm ht
  have c' : Code after p nextFrame.inst extra := c
  have mframe := ValueReturnDispatchGas.fragmentAfter_mems cfg s p.mi p.memoryIndex memory p.len p.ptr hcoded.memoryIndex hmem
  have hmAfter : after.mems[p.memoryIndex]? = some memory := by rw [show after.mems = s.mems from mframe]; exact hmem
  have hzero' : nextFrame.locals[0]? = some (.i32 0) := by simpa [nextFrame, ValueReturnDispatch.dispatchFrame] using hzero
  have hscratch' : nextFrame.locals[2]? = some (.i32 (scratch p)) := by simpa [nextFrame, ValueReturnDispatch.dispatchFrame] using hscratch
  have cd : after.host.gas.Credits (69 * cfg.regularOpCost + rest) :=
    ValueReturnDispatchGas.fragmentAfter_credits cfg extra (69 * cfg.regularOpCost + rest) s p.mi p.memoryIndex memory p.len p.ptr
      hcoded.memoryIndex hmem hfixed hbound hlimit (hc.mono (by omega))
  have clean := wp_normal_cleanup cfg fuel rest after limits base nextFrame callers code (scratch p) counter p.mi
    431 672 433 p.globalIndex p.memoryIndex global memory post hzero' hscratch' c'.module c'.memoryIndex hmAfter
    c'.releaseIndex c'.releaseFunction c'.swapIndex c'.swapFunction c'.checkIndex c'.checkFunction c'.globalIndex
    hg hsp hcounter hrecordBound hcounterBound hdepth cd hnext
  have hn : WP cfg (fuel + 45) (.next (atCode after limits base.toArray
      (ValueReturnDispatch.dispatchFrame nested cell) callers WNear.Binary.ValueReturnOuter.cleanup))
      (69 * cfg.regularOpCost + rest) post := clean
  have cn : Code s p nested.inst extra := hcoded
  have rule := ValueReturnDispatch.wp_fragment cfg extra (fuel + 45) (69 * cfg.regularOpCost + rest) s limits base nested callers
    WNear.Binary.ValueReturnOuter.cleanup cell p.slice p.receiver p.vtable p.returnElement p.len p.ptr p.mi p.mi
    p.tableAddress 260 frame.inst 20 p.memoryIndex p.table memory post hslice hsize cn.module cn.tableIndex cn.table
    cn.returnElement cn.returnType hcoded.returnFunction hcoded.module cn.hostIndex cn.hostFunction cn.memoryIndex
    cn.memoryIndex hmem hcell hspan hvtable hreceiver hvtableRead helement hlen hptr (by omega) hfixed hbound hlimit
  have credit : s.host.gas.Credits (24 * cfg.regularOpCost + ValueReturnHost.cost s.host p.len.toNat + (69 * cfg.regularOpCost + rest)) := hc.mono (by omega)
  have paid := rule credit
  have result := paid hn
  have budget : 24 * cfg.regularOpCost + ValueReturnHost.cost s.host p.len.toNat + (69 * cfg.regularOpCost + rest) =
      93 * cfg.regularOpCost + ValueReturnHost.cost s.host p.len.toNat + rest := by omega
  rw [budget] at result
  simpa only [Nat.add_assoc, Nat.reduceAdd] using result

end WNear.Proofs.ValueReturnOuterDispatchTail
