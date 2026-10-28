import Proofs.StateReadRegisterOuterPrefix
import Proofs.StateReadRegisterOuterAllocate
import Proofs.StateReadRegisterOuterSuffix

/-! The complete deployed523 positive present-register path. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic MeteredHosts
set_option maxRecDepth 16384
set_option maxHeartbeats 600000
attribute [local irreducible] WP atCode looked allocated after actualVector lengthMemory registerMemory fee

theorem wp_body (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : Code s frame.inst p extra)
    (haRoot : p.allocator=1074896) (h0 : frame.locals[0]?=some (.i32 p.out523))
    (h1 : frame.locals[1]?=some (.i64 p.register)) (hs : 3≤frame.locals.size)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global523)
    (hv : p.global523.value=.i32 p.sp523) (hr : s.host.registers p.register.toNat=some p.bytes)
    (hd : callers.length+11<limits.maxCallDepth)
    (hc : s.host.gas.Credits (bodyCost p*cfg.regularOpCost+fee cfg s p+rest))
    (hnext : WP cfg fuel (.next (atCode (after cfg s p) limits base.toArray (reservedFrame frame p) callers code)) rest post) :
    WP cfg (fuel+bodySteps p) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateReadRegisterOuter.body++code)))
      (bodyCost p*cfg.regularOpCost+fee cfg s p+rest) post := by
  let op := cfg.regularOpCost
  let q := actualVector p
  let rf := reservedFrame frame p
  let nf := suffixFrame rf base.toArray.size code
  let suffixCode := WNear.Binary.StateReadRegisterOuter.readArguments++[.call 435]++resultCode
  let tailBudget := (AllocateVectorOuter.bodyCost q+299)*op+AllocateVectorOuter.fee cfg q+RegisterRead.readCost s.host p.bytes.length+rest
  have r0 : rf.locals[0]?=some (.i32 p.out523) := by simp [rf,reservedFrame,h0]
  have r2 : rf.locals[2]?=some (.i32 (scratch p)) := by simp [rf,reservedFrame,show 2<frame.locals.size by omega]
  have rc : Code s rf.inst p extra := by simpa only [rf,reservedFrame] using hcode
  have suffix := wp_suffix cfg extra fuel rest s limits base rf callers code p post hn rc haRoot r0 r2 hm hg hr (by omega) hc hnext
  have an : WP cfg (fuel+187) (.next (atCode (allocated cfg s p) limits base.toArray nf callers suffixCode))
      (275*op+RegisterRead.readCost s.host p.bytes.length+rest) post := by simpa only [nf,suffixCode,op] using suffix
  have nc : Code s nf.inst p extra := by simpa only [nf,suffixFrame,emptyBlockFrame,rf,reservedFrame] using hcode
  have alloc := wp_allocate cfg extra (fuel+187) (275*op+RegisterRead.readCost s.host p.bytes.length+rest) s limits base nf callers suffixCode p post hn nc haRoot r2 hm hg hr hd
    (hc.mono (by simp only [bodyCost,fee,Nat.add_mul,op];omega)) an
  have ce : (AllocateVectorOuter.bodyCost q+24)*cfg.regularOpCost+AllocateVectorOuter.fee cfg q+
      (275*op+RegisterRead.readCost s.host p.bytes.length+rest)=tailBudget := by simp only [tailBudget,Nat.add_mul,op];omega
  have allocN : WP cfg ((fuel+187)+AllocateVectorOuter.bodySteps q+14) (.next (atCode (looked cfg s p) limits base.toArray nf callers
      WNear.Binary.StateReadRegisterOuter.present)) tailBudget post := by
    simpa only [q,ce,suffixCode,resultCode,WNear.Binary.StateReadRegisterOuter.present,List.append_assoc,List.cons_append,List.nil_append] using alloc
  have cl : (looked cfg s p).host.gas.Credits tailBudget :=
    looked_credits cfg s p _ (hc.mono (by simp only [bodyCost,fee,q,tailBudget,Nat.add_mul,op];omega))
  let outer := emptyBlockFrame rf base.toArray.size (WNear.Binary.StateReadRegisterOuter.restore++code)
  have inner := wp_block_empty cfg ((fuel+187)+AllocateVectorOuter.bodySteps q+14) tailBudget (looked cfg s p) limits base.toArray outer callers
    WNear.Binary.StateReadRegisterOuter.present WNear.Binary.StateReadRegisterOuter.absent post cl
    (by simpa only [nf,suffixFrame,outer] using allocN)
  have block := wp_block_empty cfg (((fuel+187)+AllocateVectorOuter.bodySteps q+14)+1) tailBudget (looked cfg s p) limits base.toArray rf callers
    ([.block .empty WNear.Binary.StateReadRegisterOuter.present]++WNear.Binary.StateReadRegisterOuter.absent)
    (WNear.Binary.StateReadRegisterOuter.restore++code) post cl inner
  have pref := wp_prefix cfg extra ((((fuel+187)+AllocateVectorOuter.bodySteps q+14)+1)+1) tailBudget s limits base frame callers
    (.block .empty ([.block .empty WNear.Binary.StateReadRegisterOuter.present]++WNear.Binary.StateReadRegisterOuter.absent)::
      (WNear.Binary.StateReadRegisterOuter.restore++code)) p post hn hcode haRoot h1 hs hm hg hv (by omega)
    (hc.mono (by simp only [bodyCost,fee,q,tailBudget,Nat.add_mul,op];omega)) block
  have cp : 302*cfg.regularOpCost+s.host.extCosts.cost "base"+tailBudget=bodyCost p*cfg.regularOpCost+fee cfg s p+rest := by
    simp only [bodyCost,fee,q,tailBudget,Nat.add_mul,op];omega
  rw [cp] at pref
  have fs : fuel+187+AllocateVectorOuter.bodySteps q+14+1+1+203=fuel+bodySteps p := by simp only [bodySteps,q];omega
  rw [fs] at pref
  simpa only [WNear.Binary.StateReadRegisterOuter.body,List.append_assoc,List.cons_append,List.nil_append] using pref
end WNear.Proofs.StateReadRegisterOuter
