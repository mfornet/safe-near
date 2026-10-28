import Proofs.StateReadRegisterOuterVectorResources
import Proofs.StateReadRegisterOuterArguments
import Proofs.StateReadRegisterOuterGuard
import Proofs.StateReadRegisterOuterCredits
import Proofs.StateReadRegisterOuterVectorCode
import Proofs.StateReadRegisterOuterFrame

/-! Concrete real687 call from the exact523 allocation-argument state. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid)
set_option maxRecDepth 16384
set_option maxHeartbeats 600000
attribute [local irreducible] WP atCode looked guarded vectorArguments allocated lengthMemory actualVector actualLength vectorMemoryTemplate vectorGrown registerMemory readI64 AllocateVectorOuter.bodyCost AllocateVectorOuter.bodySteps AllocateVectorOuter.fee

theorem wp_vector_call (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : Code s frame.inst p extra)
    (haRoot : p.allocator=1074896)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global523)
    (hr : s.host.registers p.register.toNat=some p.bytes) (hd : callers.length+11<limits.maxCallDepth)
    (hc : s.host.gas.Credits ((AllocateVectorOuter.bodyCost (actualVector p)+326)*cfg.regularOpCost+
      AllocateVectorOuter.fee cfg (actualVector p)+s.host.extCosts.cost "base"+rest))
    (hnext : WP cfg fuel (.next (atCode (allocated cfg s p) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+AllocateVectorOuter.bodySteps (actualVector p)+2) (.next (atCode (vectorArguments cfg s p) limits
      (base++[Value.i32 (scratch p+32),.i32 0,.i32 p.size]).toArray frame callers (.call 687::code)))
      ((AllocateVectorOuter.bodyCost (actualVector p)+12)*cfg.regularOpCost+AllocateVectorOuter.fee cfg (actualVector p)+rest) post := by
  let q := actualVector p
  have resources := vector_call_resources cfg extra s limits base frame callers p hn hcode haRoot hm hg hr (by omega)
  have cn : WP cfg fuel (.next (atCode (AllocateVectorOuter.callAfter cfg (vectorArguments cfg s p) q) limits base.toArray frame callers code)) rest post := by
    simpa only [allocated] using hnext
  have call := AllocateVectorOuter.wp_call cfg fuel rest (vectorArguments cfg s p) limits base frame callers code q p.address687 post
    (vector_native p hn haRoot) resources.1 (by simpa only [q,actualVector,vectorMemoryTemplate] using haRoot) resources.2.1 resources.2.2.1 resources.2.2.2.1
    (by simpa only [q,actualVector,vectorMemoryTemplate] using hcode.index687) resources.2.2.2.2 hd
    (vectorArguments_credits cfg s p _ (hc.mono (by simp only [Nat.add_mul,q];omega))) cn
  have outEq : q.out687=scratch p+32 := by simpa only [q,actualVector,vectorMemoryTemplate] using hn.vectorOut
  have flagEq : q.flag=0 := by simpa only [q,actualVector,vectorMemoryTemplate] using hn.vectorFlag
  have sizeEq : q.size=p.size := by simp only [q,actualVector,vectorMemoryTemplate]
  have operands : (base++[Value.i32 q.out687,.i32 q.flag,.i32 q.size]).toArray=
      (base++[Value.i32 (scratch p+32),.i32 0,.i32 p.size]).toArray := by rw [outEq,flagEq,sizeEq]
  exact operands ▸ call
end WNear.Proofs.StateReadRegisterOuter
