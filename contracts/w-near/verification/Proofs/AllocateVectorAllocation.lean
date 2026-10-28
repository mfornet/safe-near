import Proofs.AllocateVectorSuffix
import Proofs.AllocateVectorArguments
import Proofs.AllocateVectorControl

/-! The actual flag-one allocation branch includes the real690 invocation. -/
namespace WNear.Proofs.AllocateVector
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
set_option maxHeartbeats 800000
attribute [local irreducible] WP atCode allocated guarded selected allocateArguments after laidOutMemory resultMemory actualRecord derivedGrown

theorem wp_allocation (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame caller : CallFrame) (callers : List CallFrame)
    (p : Layout) (post : Post) (hn : Native p) (hcode : Code s frame.inst p) (haRoot : p.allocator=1074896)
    (h0 : frame.locals[0]?=some (.i32 p.out686)) (h1 : frame.locals[1]?=some (.i32 1))
    (h2 : frame.locals[2]?=some (.i32 1)) (h3 : frame.locals[3]?=some (.i32 (reservedSP p)))
    (h4 : frame.locals[4]?=some (.i32 p.size)) (hs : 6≤frame.locals.size)
    (ha : frame.arity=0) (hh : frame.height=base.length)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.outerGlobal)
    (hd : callers.length+10<limits.maxCallDepth)
    (hc : s.host.gas.Credits (bodyCost p*cfg.regularOpCost+fee cfg p+rest))
    (hnext : WP cfg fuel (.next (atCode (after cfg s p) limits base.toArray caller callers caller.code)) rest post) :
    WP cfg (fuel+AllocateRecordCopy.bodySteps (layout690 p)+33) (.next (atCode (guarded s cfg.regularOpCost p) limits base.toArray frame (caller::callers)
      (WNear.Binary.AllocateVector.accepted)))
      ((AllocateRecordCopy.bodyCost (layout690 p)+40)*cfg.regularOpCost+fee cfg p+rest) post := by
  let op := cfg.regularOpCost
  let q := layout690 p
  have cg : (guarded s op p).host.gas.Credits ((AllocateRecordCopy.bodyCost q+40)*op+fee cfg p+rest) :=
    (guarded_gas s op p _ (hc.mono (by simp only [bodyCost,Nat.add_mul,op,q];omega))).2.2
  let outer := emptyBlockFrame frame base.toArray.size exitCode
  let inner := emptyBlockFrame outer base.toArray.size alternateCode
  have suffix := wp_suffix cfg fuel rest s limits base frame caller callers p post hn hcode h0 h3 hs ha hh hm hg hc hnext
  have cn : WP cfg (fuel+21) (.next (atCode (AllocateRecordCopy.callAfter cfg (allocateArguments s op p) q) limits base.toArray inner
      (caller::callers) (WNear.Binary.AllocateVector.cache++[.br 1]))) (21*op+rest) post := by
    simpa only [allocated,q,inner,outer,op] using suffix
  have fields := allocateArguments_fields s op p
  have cda : Code (allocateArguments s op p) frame.inst p := hcode.transport s _ frame.inst p fields.1 fields.2.1 fields.2.2
  have cd : AllocateRecordCopy.Code (allocateArguments s op p) inner.inst q := by
    simpa only [inner,outer,emptyBlockFrame,q] using cda.copy _ frame.inst p hn
  have ma : (allocateArguments s op p).mems[q.inner.memoryIndex]?=some q.inner.memory := by
    simpa only [q,layout690,actualRecord] using allocateArguments_memory s op p hm
  have ga : (allocateArguments s op p).globals[q.inner.globalIndex]?=some q.global := by
    rw [show q.inner.globalIndex=p.globalIndex by simp only [q,layout690,actualRecord],allocateArguments_globals s op p hg]
    simpa only [q,layout690] using arguments_global s op p hg
  have hf : (allocateArguments s op p).funcs[p.address690]?=some (.wasm WNear.Binary.AllocateRecordCopy.signature inner.inst WNear.Binary.AllocateRecordCopy.function) := by
    rw [fields.1]
    simpa only [inner,outer,emptyBlockFrame] using hcode.function690
  have call := AllocateRecordCopy.wp_call cfg (fuel+21) (21*op+rest) (allocateArguments s op p) limits base inner (caller::callers)
    (WNear.Binary.AllocateVector.cache++[.br 1]) q p.address690 post (copy_native p hn) cd
    (by simpa only [q,layout690,actualRecord] using haRoot) ma ga rfl (by simpa only [q,layout690,actualRecord] using hcode.index690) hf
    (by simpa only [List.length_cons] using hd)
    ((allocateArguments_gas s op p _ (hc.mono (by simp only [bodyCost,Nat.add_mul,fee,op,q];omega))).2.2) cn
  have arr : (base++[Value.i32 q.out,.i32 q.inner.size,.i32 1]).toArray=
      ((base.toArray.push (.i32 q.out)).push (.i32 q.inner.size)).push (.i32 1) := by apply Array.toList_inj.mp;simp
  rw [arr] at call
  have callN : WP cfg ((fuel+21)+AllocateRecordCopy.bodySteps q+2) (.next (atCode (paid (selected s op p) op 5) limits
      (((base.toArray.push (.i32 (reservedSP p+8))).push (.i32 p.size)).push (.i32 1)) inner (caller::callers)
      (.call 690::(WNear.Binary.AllocateVector.cache++[.br 1]))))
      ((AllocateRecordCopy.bodyCost q+11)*op+AllocateRecordCopy.fee cfg q+(21*op+rest)) post := by
    simpa only [allocateArguments,q,layout690,actualRecord,op] using call
  have args := wp_allocate_arguments cfg ((fuel+21)+AllocateRecordCopy.bodySteps q+2)
    ((AllocateRecordCopy.bodyCost q+11)*op+AllocateRecordCopy.fee cfg q+(21*op+rest)) (selected s op p) limits base.toArray inner (caller::callers)
    (.call 690::(WNear.Binary.AllocateVector.cache++[.br 1])) (reservedSP p) p.size post h3 h4 h1
    ((selected_gas s op p _ (hc.mono (by simp only [bodyCost,Nat.add_mul,fee,op,q];omega))).2.2) callN
  have sel := wp_nonzero cfg (((fuel+21)+AllocateRecordCopy.bodySteps q+2)+5)
    (5*op+((AllocateRecordCopy.bodyCost q+11)*op+AllocateRecordCopy.fee cfg q+(21*op+rest)))
    (guarded s op p) limits base.toArray inner (caller::callers)
    (WNear.Binary.AllocateVector.allocateArguments++(.call 690::(WNear.Binary.AllocateVector.cache++[.br 1]))) 2 0 1 post h2 (by decide)
    ((guarded_gas s op p _ (hc.mono (by simp only [bodyCost,Nat.add_mul,fee,op,q];omega))).2.2) (by simpa only [selected,op] using args)
  have ce : 3*cfg.regularOpCost+(5*op+((AllocateRecordCopy.bodyCost q+11)*op+AllocateRecordCopy.fee cfg q+(21*op+rest)))=
      (AllocateRecordCopy.bodyCost q+40)*cfg.regularOpCost+fee cfg p+rest := by simp only [q,fee,Nat.add_mul,op];omega
  rw [ce] at sel
  have enter1 := wp_block_empty cfg ((((fuel+21)+AllocateRecordCopy.bodySteps q+2)+5)+3) ((AllocateRecordCopy.bodyCost q+40)*cfg.regularOpCost+fee cfg p+rest) (guarded s op p) limits base.toArray outer (caller::callers)
    (WNear.Binary.AllocateVector.select++WNear.Binary.AllocateVector.allocateArguments++[.call 690]++WNear.Binary.AllocateVector.cache++[.br 1]) alternateCode post
    (cg.mono (by simp only [op];omega))
    (by simpa only [WNear.Binary.AllocateVector.select,inner,List.append_assoc,List.cons_append,List.nil_append] using sel)
  have enter2 := wp_block_empty cfg (((((fuel+21)+AllocateRecordCopy.bodySteps q+2)+5)+3)+1) ((AllocateRecordCopy.bodyCost q+40)*cfg.regularOpCost+fee cfg p+rest) (guarded s op p) limits base.toArray frame (caller::callers)
    WNear.Binary.AllocateVector.allocation exitCode post
    (cg.mono (by simp only [op];omega))
    (by simpa only [outer,alternateCode,WNear.Binary.AllocateVector.allocation,List.append_assoc,List.cons_append,List.nil_append] using enter1)
  have fe : fuel+21+AllocateRecordCopy.bodySteps q+2+5+3+1+1=fuel+AllocateRecordCopy.bodySteps q+33 := by omega
  rw [fe] at enter2
  simpa only [WNear.Binary.AllocateVector.accepted,exitCode,q,op,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using enter2
end WNear.Proofs.AllocateVector
