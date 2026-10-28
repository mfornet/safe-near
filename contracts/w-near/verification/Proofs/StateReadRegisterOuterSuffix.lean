import Proofs.StateReadRegisterOuterTail
import Proofs.StateReadRegisterOuterArguments
import Proofs.StateReadRegisterOuterCopyBounds
import Proofs.StateReadRegisterOuterCredits
import Proofs.StateReadRegisterOuterReadBridge
import Proofs.StateReadRegisterOuterReadResult
import Proofs.StateDispatchReadCallFrame

/-! Actual523 postallocation read435, sequentialcopy, branch exit and SP restoration. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid)
set_option maxRecDepth 16384
set_option maxHeartbeats 600000
attribute [local irreducible] WP atCode allocated readArguments readDone after lengthMemory registerMemory readLayout readFinalMemory actualVector

def resultCode : Expr := WNear.Binary.StateReadRegisterOuter.copyHigh++WNear.Binary.StateReadRegisterOuter.copyLow++[.br 1]
def suffixFrame (frame : CallFrame) (height : Nat) (code : Expr) :=
  emptyBlockFrame (emptyBlockFrame frame height (WNear.Binary.StateReadRegisterOuter.restore++code)) height WNear.Binary.StateReadRegisterOuter.absent

theorem wp_suffix (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : Code s frame.inst p extra)
    (haRoot : p.allocator=1074896) (h0 : frame.locals[0]?=some (.i32 p.out523))
    (h2 : frame.locals[2]?=some (.i32 (scratch p)))
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global523)
    (hr : s.host.registers p.register.toNat=some p.bytes) (hd : callers.length+5<limits.maxCallDepth)
    (hc : s.host.gas.Credits (bodyCost p*cfg.regularOpCost+fee cfg s p+rest))
    (hnext : WP cfg fuel (.next (atCode (after cfg s p) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+187) (.next (atCode (allocated cfg s p) limits base.toArray (suffixFrame frame base.toArray.size code) callers
      (WNear.Binary.StateReadRegisterOuter.readArguments++[.call 435]++resultCode)))
      (275*cfg.regularOpCost+RegisterRead.readCost s.host p.bytes.length+rest) post := by
  let op := cfg.regularOpCost
  let nf := suffixFrame frame base.toArray.size code
  have shape := readFinalMemory_spec p hn haRoot
  have bounds := copy_bounds p hn
  have fieldsA := readArguments_fields cfg s p
  have fieldsR := StateDispatchRead.callAfter_fields cfg (readArguments cfg s p) (readLayout p) p.bytes
  have rm : (readDone cfg s p).modules[frame.inst]?=some p.mi := by
    rw [readDone,fieldsR.2.1,fieldsA.2.1]
    simpa only [actualLength,lengthOn] using hcode.prefixCode.module
  have mem := readDone_memory cfg s limits frame.inst base.length callers p extra hn haRoot hcode hm hg hr (by omega)
  have gr := readArguments_global cfg s p hn haRoot hg
  have callGlobal := StateDispatchRead.callAfter_globals cfg (readArguments cfg s p) (readLayout p) p.bytes
    (by simpa only [readLayout,readOn] using gr) (by simp only [readLayout,readOn])
  have rg : (readDone cfg s p).globals[p.globalIndex]?=some {p.global523 with value:=.i32 (scratch p)} := by
    rw [readDone,callGlobal];exact gr
  have nn : WP cfg fuel (.next (atCode (finished (readDone cfg s p) op p.memoryIndex p.globalIndex (readFinalMemory p) p.out523 (scratch p))
      limits base.toArray frame callers code)) rest post := by
    simpa only [finished,after,branched,copyDone,scratch,UInt32.sub_add_cancel,op] using hnext
  have tc := readDone_credits cfg s p (19*op+rest) (hc.mono (by simp only [bodyCost,Nat.add_mul,op];omega))
  have tail := wp_tail cfg fuel rest (readDone cfg s p) limits base.toArray frame callers code WNear.Binary.StateReadRegisterOuter.absent
    p.out523 (scratch p) p.mi p.memoryIndex p.globalIndex {p.global523 with value:=.i32 (scratch p)} (readFinalMemory p) post h0 h2 rm
    hcode.prefixCode.memoryIndex mem hcode.prefixCode.globalIndex rg shape.1 (bounds.2.2.1.trans shape.2.1)
    (bounds.2.2.2.1.trans shape.2.1) (bounds.2.2.2.2.1.trans shape.2.1) (bounds.2.2.2.2.2.trans shape.2.1) tc nn
  have cn : WP cfg (fuel+19) (.next (atCode (StateDispatchRead.callAfter cfg (readArguments cfg s p) (readLayout p) p.bytes)
      limits base.toArray nf callers resultCode)) (19*op+rest) post := by
    simpa only [readDone,nf,suffixFrame,resultCode,op] using tail
  have rc : Code s nf.inst p extra := by simpa only [nf,suffixFrame,emptyBlockFrame] using hcode
  have ready := rc.read_ready cfg s limits nf.inst base.length ({nf with code:=resultCode}::callers) p extra hn haRoot hm hg hr
    (by simp only [List.length_cons];omega)
  have hf : (readArguments cfg s p).funcs[p.address435]?=some (.wasm WNear.Binary.StateDispatchRead.signature nf.inst WNear.Binary.StateDispatchRead.function) := by
    rw [fieldsA.1];simpa only [nf,suffixFrame,emptyBlockFrame] using hcode.function435
  have rcost : (readArguments cfg s p).host.gas.Credits (249*op+RegisterRead.readCost (readArguments cfg s p).host p.bytes.length+(19*op+rest)) := by
    have c := readArguments_credits cfg s p (268*op+RegisterRead.readCost s.host p.bytes.length+rest)
      (hc.mono (by simp only [bodyCost,fee,Nat.add_mul,op];omega))
    have ce : 268*op+RegisterRead.readCost s.host p.bytes.length+rest=
        249*op+RegisterRead.readCost s.host p.bytes.length+(19*op+rest) := by omega
    rw [ce] at c
    simpa only [RegisterRead.readCost,readArguments_costs] using c
  have call := StateDispatchRead.wp_call cfg extra (fuel+19) (19*op+rest) (readArguments cfg s p) limits base nf callers resultCode
    (readLayout p) p.bytes p.address435 post ready (by simpa only [readLayout,readOn] using hcode.index435) hf rcost cn
  have an : WP cfg ((fuel+19)+161) (.next (atCode (paid (allocated cfg s p) op 7) limits
      (((base.toArray.push (.i32 1055020)).push (.i32 (scratch p+24))).push (.i32 (scratch p+32))) nf callers (.call 435::resultCode)))
      (249*op+RegisterRead.readCost s.host p.bytes.length+(19*op+rest)) post := by
    have arr : (base++[Value.i32 (readLayout p).interface,.i32 (readLayout p).inputRegister,.i32 (readLayout p).inputPointer]).toArray=
      ((base.toArray.push (.i32 (readLayout p).interface)).push (.i32 (readLayout p).inputRegister)).push (.i32 (readLayout p).inputPointer) := by
      apply Array.toList_inj.mp;simp
    have feeR : RegisterRead.readCost (readArguments cfg s p).host p.bytes.length=RegisterRead.readCost s.host p.bytes.length := by
      simp only [RegisterRead.readCost,readArguments_costs]
    rw [arr,feeR] at call
    simpa only [readArguments,readLayout,readOn,RegisterRead.readCost,readArguments_costs,op] using call
  have args := wp_read_arguments cfg ((fuel+19)+161) (249*op+RegisterRead.readCost s.host p.bytes.length+(19*op+rest)) (allocated cfg s p) limits base.toArray nf callers
    (.call 435::resultCode) (scratch p) post h2
    (allocated_credits cfg s p _ (hc.mono (by simp only [bodyCost,fee,Nat.add_mul,op];omega))) an
  have ce : 7*cfg.regularOpCost+(249*op+RegisterRead.readCost s.host p.bytes.length+(19*op+rest))=
      275*cfg.regularOpCost+RegisterRead.readCost s.host p.bytes.length+rest := by dsimp [op];omega
  rw [ce] at args
  simpa only [List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using args
end WNear.Proofs.StateReadRegisterOuter
