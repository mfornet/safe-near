import Proofs.StateDecodeVectorFrame
import Proofs.StateDecodeVectorTailFrame

/-! Cached generic suffix frames specialize to the actual373 allocated store. -/
namespace WNear.Proofs.StateDecodeVector
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
attribute [local irreducible] StateDecodeRaw.callAfterRaw StateDecodeRaw.finalMemory readI64 writeI64 writeI32

theorem after_eq (cfg:WasmConfig)(s:Store NearState)(p:Layout):
    after cfg s p=tailAfter (allocated cfg s p) cfg.regularOpCost p.memoryIndex p.globalIndex (memoryAllocated p) p.outVector (scratch p):=by
  simp only[after,tailAfter,copied,zeroed,cached,outputStore,zeroStore,StateDecodeScalar.store64Local,zeroMemory,packed]

theorem after_memory (cfg:WasmConfig)(s:Store NearState)(p:Layout)(hn:Native p)
    (hm:s.mems[p.memoryIndex]?=some p.memory):
    (after cfg s p).mems[p.memoryIndex]?=some (finalMemory p):=by
  have h:=tailAfter_memory (allocated cfg s p) cfg.regularOpCost p.memoryIndex p.globalIndex (memoryAllocated p) p.outVector (scratch p)
    (allocated_memory cfg s p hn hm)
  rw[after_eq]
  simpa only[tailMemory,finalMemory,packed,zeroMemory] using h

private theorem globals_paid (s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

theorem after_globals (cfg:WasmConfig)(s:Store NearState)(p:Layout)(hn:Native p)
    (hg:s.globals[p.globalIndex]?=some p.globalVector)(hv:p.globalVector.value=.i32 p.spVector):
    (after cfg s p).globals=s.globals:=by
  have ag:=allocated_globals cfg s p hn hg
  have restore:=StorePairCaller.setGlobal_restore s p.globalIndex (.i32 (scratch p)) p.globalVector hg
  have endSP:scratch p+16=p.spVector:=UInt32.sub_add_cancel _ _
  rw[after_eq,tailAfter_globals,ag]
  simpa only[reserved,setGlobal,globals_paid,hv,endSP] using restore
end WNear.Proofs.StateDecodeVector
