import Proofs.AllocateRecordCopyPrefix
import Proofs.AllocateRecordCopyTail
import Proofs.AllocateRecordCall

/-! Full actual690 wrapper, including the actual689 call and sequential copies. -/
namespace WNear.Proofs.AllocateRecordCopy
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
attribute [local irreducible] WP atCode arguments allocated copyDone after AllocateRecord.callAfter

theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : Code s frame.inst p)
    (ha : p.inner.allocator=1074896)
    (h0 : frame.locals[0]?=some (.i32 p.out)) (h1 : frame.locals[1]?=some (.i32 p.inner.size))
    (h2 : frame.locals[2]?=some (.i32 1)) (hs : 4≤frame.locals.size)
    (hm : s.mems[p.inner.memoryIndex]?=some p.inner.memory)
    (hg : s.globals[p.inner.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp)
    (hd : callers.length+8<limits.maxCallDepth)
    (hc : s.host.gas.Credits (bodyCost p*cfg.regularOpCost+fee cfg p+rest))
    (hnext : WP cfg fuel (.next (atCode (after cfg s p) limits base.toArray (resultFrame frame p) callers code)) rest post) :
    WP cfg (fuel+bodySteps p) (.next (atCode s limits base.toArray frame callers (WNear.Binary.AllocateRecordCopy.body++code)))
      (bodyCost p*cfg.regularOpCost+fee cfg p+rest) post := by
  let op := cfg.regularOpCost
  let rf := resultFrame frame p
  let tail := WNear.Binary.AllocateRecordCopy.copy++WNear.Binary.AllocateRecordCopy.restore++code
  have h0r : rf.locals[0]?=some (.i32 p.out) := by simp [rf,resultFrame,h0]
  have h3r : rf.locals[3]?=some (.i32 p.inner.sp) := by simp [rf,resultFrame,show 3<frame.locals.size by omega]
  have codeR : Code s rf.inst p := by simpa only [rf,resultFrame] using hcode
  have finish := wp_tail cfg fuel rest s limits base rf callers code p post hn codeR h0r h3r hm hg hc hnext
  have fields := arguments_fields s op p
  have codeA : Code (arguments s op p) rf.inst p :=
    codeR.transport s _ rf.inst p fields.1 fields.2.1 fields.2.2
  have memA : (arguments s op p).mems[p.inner.memoryIndex]?=some p.inner.memory := by
    simpa only [arguments,reserved,StorePairCaller.paid,chargedStore,setGlobal] using hm
  have globalA := arguments_global s op p hn hg
  have valueA : p.inner.global.value=.i32 p.inner.sp := by rw [hn.innerGlobal]
  have ca : (arguments s op p).host.gas.Credits ((AllocateRecord.bodyCost p.inner+11)*op+fee cfg p+(12*op+rest)) :=
    (arguments_gas s op p) _ (hc.mono (by simp only [bodyCost,op,Nat.add_mul];omega)) |>.2.2
  have callNext : WP cfg (fuel+12) (.next (atCode (AllocateRecord.callAfter cfg (arguments s op p) p.inner) limits base.toArray rf callers tail)) (12*op+rest) post := by
    simpa only [allocated,AllocateRecord.callAfter,AllocateRecord.entered,recordEntered,tail,op] using finish
  have call := AllocateRecord.wp_call cfg (fuel+12) (12*op+rest) (arguments s op p) limits base rf callers tail p.inner p.address689 post
    hn.inner codeA.inner ha memA globalA valueA codeA.index689 codeA.function689 hd ca callNext
  have prefixNext : WP cfg (fuel+AllocateRecord.bodySteps p.inner+14) (.next (atCode (arguments s op p) limits
      (base++[Value.i32 p.inner.out,.i32 p.inner.size,.i32 1,.i32 1]).toArray rf callers (.call 689::tail)))
      ((AllocateRecord.bodyCost p.inner+23)*op+fee cfg p+rest) post := by
    have ce : (AllocateRecord.bodyCost p.inner+11)*cfg.regularOpCost+AllocateRecord.fee cfg p.inner+(12*op+rest)=
        (AllocateRecord.bodyCost p.inner+23)*op+fee cfg p+rest := by simp only [op,fee,Nat.add_mul];omega
    rw [ce] at call
    have fe : fuel+12+AllocateRecord.bodySteps p.inner+2=fuel+AllocateRecord.bodySteps p.inner+14 := by omega
    simpa only [fe] using call
  have start := wp_prefix cfg (fuel+AllocateRecord.bodySteps p.inner+14) ((AllocateRecord.bodyCost p.inner+23)*op+fee cfg p+rest)
    s limits base frame callers (.call 689::tail) p post hn hcode h1 h2 hs hg hv
    (hc.mono (by simp only [bodyCost,op,Nat.add_mul];omega)) prefixNext
  have ce : 11*cfg.regularOpCost+((AllocateRecord.bodyCost p.inner+23)*op+fee cfg p+rest)=bodyCost p*cfg.regularOpCost+fee cfg p+rest := by simp only [bodyCost,op,Nat.add_mul];omega
  rw [ce] at start
  have fe : fuel+AllocateRecord.bodySteps p.inner+14+11=fuel+bodySteps p := by simp only [bodySteps];omega
  simpa only [WNear.Binary.AllocateRecordCopy.body,tail,List.append_assoc,List.cons_append,List.nil_append,fe] using start
end WNear.Proofs.AllocateRecordCopy
