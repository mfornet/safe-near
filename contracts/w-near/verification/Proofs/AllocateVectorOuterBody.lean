import Proofs.AllocateVectorOuterPrefix
import Proofs.AllocateVectorOuterFrame
import Proofs.AllocateVectorOuterGas
import Proofs.AllocateVectorOuterMemory
import Proofs.AllocateVectorCall

/-! Full actual687 low-byte-zero path, using the closed actual686 allocation. -/
namespace WNear.Proofs.AllocateVectorOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode allocated arguments after AllocateVector.callAfter

private theorem allocated_budget (body op fee rest : Nat) :
    (body+26)*op+fee+(14*op+rest)≤(body+40)*op+fee+rest := by
  simp only [Nat.add_mul];omega
private theorem arguments_budget (body op fee rest : Nat) :
    14*op+((body+12)*op+fee+(14*op+rest))≤(body+40)*op+fee+rest := by
  simp only [Nat.add_mul];omega
private theorem prefix_budget (body op fee rest : Nat) :
    14*op+((body+26)*op+fee+rest)≤(body+40)*op+fee+rest := by
  simp only [Nat.add_mul];omega
private theorem call_cost (body op fee rest : Nat) :
    (body+12)*op+fee+(14*op+rest)=(body+26)*op+fee+rest := by
  simp only [Nat.add_mul];omega
private theorem prefix_cost (body op fee rest : Nat) :
    14*op+((body+26)*op+fee+rest)=(body+40)*op+fee+rest := by
  simp only [Nat.add_mul];omega
private theorem scratch_span (original scratch size : Nat) (h : scratch=original-32)
    (hl : 96≤original) (hb : original≤size) : scratch+16≤size := by omega

theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : Code s frame.inst p)
    (ha : p.allocator=1074896)
    (h0 : frame.locals[0]?=some (.i32 p.out687)) (h1 : frame.locals[1]?=some (.i32 p.flag))
    (h2 : frame.locals[2]?=some (.i32 p.size)) (hs : 5≤frame.locals.size)
    (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hg : s.globals[p.globalIndex]?=some p.global687) (hv : p.global687.value=.i32 p.sp687)
    (hd : callers.length+10<limits.maxCallDepth)
    (hc : s.host.gas.Credits (bodyCost p*cfg.regularOpCost+fee cfg p+rest))
    (hnext : WP cfg fuel (.next (atCode (after cfg s p) limits base.toArray (finalFrame frame p) callers code)) rest post) :
    WP cfg (fuel+bodySteps p) (.next (atCode s limits base.toArray frame callers (WNear.Binary.AllocateVectorOuter.body++code)))
      (bodyCost p*cfg.regularOpCost+fee cfg p+rest) post := by
  let op := cfg.regularOpCost
  let rf := reservedFrame frame p
  let inner := nestedFrame rf base.toArray.size code
  have f0 : rf.locals[0]?=some (.i32 p.out687) := by simp [rf,reservedFrame,h0]
  have f2 : rf.locals[2]?=some (.i32 p.size) := by simp [rf,reservedFrame,h2]
  have f3 : rf.locals[3]?=some (.i32 p.outerSP) := by simp [rf,reservedFrame,show 3<frame.locals.size by omega]
  have fs : 5≤rf.locals.size := by simpa only [rf,reservedFrame,Array.size_set!] using hs
  have ac := allocated_code cfg s frame.inst p hcode
  have moduleA : (allocated cfg s p).modules[rf.inst]?=some p.mi := ac.vector.allocation.allocation.retry.originalCode.search.module
  have memoryA := allocated_memory cfg s p hm
  have globalA := allocated_global cfg s p hn hg
  have shape := allocated_spec p hn
  have outBound : p.out687.toNat+12≤(allocatedMemory p).byteSize := hn.outputBound.trans shape.2.1
  have nums := stack_numbers p hn
  have scratchBound : p.outerSP.toNat+16≤(allocatedMemory p).byteSize :=
    (scratch_span p.sp687.toNat p.outerSP.toNat p.memory.byteSize nums.1 hn.spLower hn.spBound).trans shape.2.1
  have allocatedCredit := allocated_credits cfg s p (14*op+rest)
    (hc.mono (by simpa only [bodyCost,op] using allocated_budget (AllocateVector.bodyCost p.toVector) cfg.regularOpCost (fee cfg p) rest))
  have tailNext : WP cfg fuel (.next (atCode (tailAfter (allocated cfg s p) cfg.regularOpCost p.memoryIndex p.globalIndex
      (allocatedMemory p) p.out687 p.size p.outerSP) limits base.toArray (cachedFrame rf (allocatedMemory p) p.outerSP) callers code)) rest post := by
    simpa only [after,finalFrame,rf] using hnext
  have tail := wp_tail cfg fuel rest (allocated cfg s p) limits base.toArray rf callers code p.mi p.memoryIndex p.globalIndex
    (allocatedMemory p) p.outerGlobal p.out687 p.size p.outerSP post f0 f2 f3 fs moduleA
    ac.vector.allocation.allocation.retry.originalCode.search.memoryIndex
    ac.vector.allocation.allocation.retry.originalCode.globalIndex memoryA globalA shape.1 outBound scratchBound allocatedCredit tailNext
  have ca := arguments_code s op frame.inst p hcode
  have mm := arguments_memory s op p hm
  have gg := arguments_global s op p hn hg
  have vg : p.outerGlobal.value=.i32 p.outerSP := by rw [hn.outerGlobal]
  have original := hn.vector p
  have callNext : WP cfg (fuel+14) (.next (atCode (AllocateVector.callAfter cfg (arguments s op p) p.toVector) limits
      base.toArray inner callers tailCode)) (14*op+rest) post := by
    simpa only [allocated,AllocateVector.callAfter,AllocateVector.entered,vectorEntered,inner,op] using tail
  have cArgs : (arguments s op p).host.gas.Credits ((AllocateVector.bodyCost p.toVector+12)*op+fee cfg p+(14*op+rest)) :=
    (arguments_gas s op p) _ (hc.mono (by simpa only [bodyCost,op] using arguments_budget (AllocateVector.bodyCost p.toVector) cfg.regularOpCost (fee cfg p) rest)) |>.2.2
  have call := AllocateVector.wp_call cfg (fuel+14) (14*op+rest) (arguments s op p) limits base inner callers tailCode
    p.toVector p.address686 post original ca.vector ha mm gg vg ca.index686 ca.function686 hd cArgs callNext
  have prefixNext : WP cfg (fuel+AllocateVector.bodySteps p.toVector+15) (.next (atCode (arguments s op p) limits
      (((base.toArray.push (.i32 p.out686)).push (.i32 p.size)).push (.i32 1)) inner callers (.call 686::tailCode)))
      ((AllocateVector.bodyCost p.toVector+26)*op+fee cfg p+rest) post := by
    have ce : (AllocateVector.bodyCost p.toVector+12)*cfg.regularOpCost+AllocateVector.fee cfg p.toVector+(14*op+rest)=
        (AllocateVector.bodyCost p.toVector+26)*op+fee cfg p+rest := by
      simpa only [fee,op] using call_cost (AllocateVector.bodyCost p.toVector) cfg.regularOpCost (fee cfg p) rest
    rw [ce] at call
    have fe : fuel+14+AllocateVector.bodySteps p.toVector+1=fuel+AllocateVector.bodySteps p.toVector+15 := by omega
    have arr : (base++[Value.i32 p.out686,.i32 p.size,.i32 1]).toArray=
        (((base.toArray.push (.i32 p.out686)).push (.i32 p.size)).push (.i32 1)) := by apply Array.toList_inj.mp;simp
    simpa only [fe,arr] using call
  have head :=  wp_prefix cfg (fuel+AllocateVector.bodySteps p.toVector+15)
    ((AllocateVector.bodyCost p.toVector+26)*op+fee cfg p+rest) s limits base.toArray frame callers code p post hn hcode h1 h2
    (by omega) hg hv (hc.mono (by simpa only [bodyCost,op] using prefix_budget (AllocateVector.bodyCost p.toVector) cfg.regularOpCost (fee cfg p) rest)) prefixNext
  have ce : 14*cfg.regularOpCost+((AllocateVector.bodyCost p.toVector+26)*op+fee cfg p+rest)=bodyCost p*cfg.regularOpCost+fee cfg p+rest := by
    simpa only [bodyCost,op] using prefix_cost (AllocateVector.bodyCost p.toVector) cfg.regularOpCost (fee cfg p) rest
  rw [ce] at head
  have fe : fuel+AllocateVector.bodySteps p.toVector+15+16=fuel+bodySteps p := by simp only [bodySteps];omega
  simpa only [fe] using head
end WNear.Proofs.AllocateVectorOuter
