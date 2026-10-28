import Proofs.StateReadRegisterOuterVectorCall
import Proofs.StateReadRegisterOuterGuardArguments
import Proofs.StateReadRegisterOuterArguments
import Proofs.StateReadRegisterOuterGuard
import Proofs.StateReadRegisterOuterCredits
import Proofs.StateReadRegisterOuterVectorCode
import Proofs.StateReadRegisterOuterFrame
import Proofs.StateReadRegisterOuterLengthWords

/-! The523 present branch invokes the complete real687 allocator from original data. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid)
set_option maxRecDepth 16384
set_option maxHeartbeats 600000
attribute [local irreducible] WP atCode looked guarded vectorArguments allocated lengthMemory actualVector actualLength vectorMemoryTemplate vectorGrown registerMemory readI64 AllocateVectorOuter.bodyCost AllocateVectorOuter.bodySteps AllocateVectorOuter.fee

private theorem paid_add (s : Store NearState) (op a b : Nat) : paid (paid s op a) op b=paid s op (a+b) := by
  induction b with |zero=>rfl |succ b ih=>simp only [paid,ih];rfl
private theorem vectorArguments_paid (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    paid (looked cfg s p) cfg.regularOpCost 12=vectorArguments cfg s p := by
  unfold vectorArguments guarded
  rw [paid_add]

theorem wp_allocate (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : Code s frame.inst p extra)
    (haRoot : p.allocator=1074896) (h2 : frame.locals[2]?=some (.i32 (scratch p)))
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global523)
    (hr : s.host.registers p.register.toNat=some p.bytes) (hd : callers.length+11<limits.maxCallDepth)
    (hc : s.host.gas.Credits ((AllocateVectorOuter.bodyCost (actualVector p)+326)*cfg.regularOpCost+
      AllocateVectorOuter.fee cfg (actualVector p)+s.host.extCosts.cost "base"+rest))
    (hnext : WP cfg fuel (.next (atCode (allocated cfg s p) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+AllocateVectorOuter.bodySteps (actualVector p)+14) (.next (atCode (looked cfg s p) limits base.toArray frame callers
      (WNear.Binary.StateReadRegisterOuter.presentGuard++WNear.Binary.StateReadRegisterOuter.vectorArguments++[.call 687]++code)))
      ((AllocateVectorOuter.bodyCost (actualVector p)+24)*cfg.regularOpCost+AllocateVectorOuter.fee cfg (actualVector p)+rest) post := by
  let op := cfg.regularOpCost
  let q := actualVector p
  have call := wp_vector_call cfg extra fuel rest s limits base frame callers code p post hn hcode haRoot hm hg hr hd hc hnext
  have arr : (base++[Value.i32 (scratch p+32),.i32 0,.i32 p.size]).toArray=
      ((base.toArray.push (.i32 (scratch p+32))).push (.i32 0)).push (.i32 p.size) := by apply Array.toList_inj.mp;simp
  rw [arr] at call
  have words := length_words p hn
  have wrapped : (readI64 (lengthMemory p) ((scratch p).toNat+16)).toUInt32=p.size :=
    (congrArg UInt64.toUInt32 words.2).trans (length_wrap p hn)
  have moduleL : (looked cfg s p).modules[frame.inst]?=some p.mi := by
    rw [(looked_fields cfg s p).2.1]
    simpa only [actualLength,lengthOn] using hcode.prefixCode.module
  have lm := looked_memory cfg s limits frame.inst base.length callers p extra hn haRoot hcode hm hg hr (by omega)
  have span : (scratch p).toNat+24≤(lengthMemory p).byteSize := by
    rw [(lengthMemory_footprint p hn).2.1,(stack_numbers p hn).1]
    have lo := hn.spLower;have bound := hn.spBound;omega
  have mi0 : p.mi.memAddrs[0]?=some p.memoryIndex := by simpa only [actualLength,lengthOn] using hcode.prefixCode.memoryIndex
  have an : WP cfg (fuel+AllocateVectorOuter.bodySteps q+2) (.next (atCode (paid (looked cfg s p) op 12) limits
      (((base.toArray.push (.i32 (scratch p+32))).push (.i32 0)).push (.i32 (readI64 (lengthMemory p) ((scratch p).toNat+16)).toUInt32)) frame callers (.call 687::code)))
      ((AllocateVectorOuter.bodyCost q+12)*op+AllocateVectorOuter.fee cfg q+rest) post := by
    rw [wrapped]
    rw [vectorArguments_paid]
    exact call
  have both := wp_guard_arguments cfg (fuel+AllocateVectorOuter.bodySteps q+2)
    ((AllocateVectorOuter.bodyCost q+12)*op+AllocateVectorOuter.fee cfg q+rest)
    (looked cfg s p) limits base.toArray frame callers (.call 687::code)
    (scratch p) p.mi p.memoryIndex (lengthMemory p) post h2 moduleL mi0 lm span
    (by rw [words.1];decide)
    (looked_credits cfg s p _ (hc.mono (by simp only [Nat.add_mul,q,op];omega))) an
  have ce : 12*cfg.regularOpCost+((AllocateVectorOuter.bodyCost q+12)*op+AllocateVectorOuter.fee cfg q+rest)=
      (AllocateVectorOuter.bodyCost q+24)*cfg.regularOpCost+AllocateVectorOuter.fee cfg q+rest := by simp only [Nat.add_mul,op];omega
  rw [ce] at both
  simpa only [q,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using both
end WNear.Proofs.StateReadRegisterOuter
