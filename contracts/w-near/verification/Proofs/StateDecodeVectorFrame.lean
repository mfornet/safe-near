import Proofs.StateDecodeVectorCode
import Proofs.StateDecodeRawResult

/-! Actual373 phase projections from original arrays and shadow-stack state. -/
namespace WNear.Proofs.StateDecodeVector
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
attribute [local irreducible] StateDecodeRaw.callAfterRaw StateDecodeRaw.finalMemory
private theorem mems_paid (s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_global (s:Store NearState)(i:Nat)(v:Value):(setGlobal s i v).mems=s.mems:=rfl
private theorem globals_paid (s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

theorem arguments_memory (s:Store NearState)(op:Nat)(p:Layout)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (arguments s op p).mems[p.memoryIndex]?=some p.memory:=by
  simp only[arguments,reserved,mems_paid,mems_global];exact hm

theorem arguments_global (s:Store NearState)(op:Nat)(p:Layout)(hn:Native p)
    (hg:s.globals[p.globalIndex]?=some p.globalVector):
    (arguments s op p).globals[p.globalIndex]?=some p.globalRaw:=by
  rw[hn.childGlobal,hn.childSP]
  simp only[arguments,reserved,setGlobal,globals_paid,Array.getElem?_modify,hg,Option.map_some,ite_true,scratch]

theorem allocated_memory (cfg:WasmConfig)(s:Store NearState)(p:Layout)(hn:Native p)
    (hm:s.mems[p.memoryIndex]?=some p.memory):
    (allocated cfg s p).mems[p.memoryIndex]?=some (memoryAllocated p):=
  StateDecodeRaw.callAfterRaw_memory cfg (arguments s cfg.regularOpCost p) p.toRaw hn.raw
    (arguments_memory s cfg.regularOpCost p hm)

theorem allocated_globals (cfg:WasmConfig)(s:Store NearState)(p:Layout)(hn:Native p)
    (hg:s.globals[p.globalIndex]?=some p.globalVector):
    (allocated cfg s p).globals=(reserved s cfg.regularOpCost p).globals:=by
  have arg:=arguments_global s cfg.regularOpCost p hn hg
  have hv:p.globalRaw.value=.i32 p.spRaw:=by rw[hn.childGlobal]
  have h:=StateDecodeRaw.callAfterRaw_globals cfg (arguments s cfg.regularOpCost p) p.toRaw hn.raw arg hv
  simpa only[allocated,arguments,globals_paid] using h

end WNear.Proofs.StateDecodeVector
