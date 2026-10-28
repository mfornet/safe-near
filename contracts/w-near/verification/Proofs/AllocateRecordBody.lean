import Proofs.AllocateRecordSteps
import Proofs.AllocateRecordResources

/-! Full actual689 positive-size/alignment-one/zeroed-flag-one body. -/
namespace WNear.Proofs.AllocateRecord
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode allocated selected after AllocateForwardRetry.callAfter313

def outerFrame (frame : CallFrame) (height : Nat) (code : Expr) :=
  emptyBlockFrame frame height (WNear.Binary.AllocateRecord.record++code)
def innerFrame (frame : CallFrame) (height : Nat) (code : Expr) :=
  emptyBlockFrame (outerFrame frame height code) height WNear.Binary.AllocateRecord.ordinary
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with | zero=>rfl | succ n ih=>exact ih

 theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : Code s frame.inst p)
    (ha : p.allocator=1074896)
    (h0 : frame.locals[0]?=some (.i32 p.out)) (h1 : frame.locals[1]?=some (.i32 p.size))
    (h2 : frame.locals[2]?=some (.i32 1)) (h3 : frame.locals[3]?=some (.i32 1)) (hs : 4≤frame.locals.size)
    (hm : s.mems[p.memoryIndex]?=some p.memory)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp)
    (hd : callers.length+7<limits.maxCallDepth)
    (hc : s.host.gas.Credits (bodyCost p*cfg.regularOpCost+fee cfg p+rest))
    (hnext : WP cfg fuel (.next (atCode (after cfg s p) limits base.toArray (resultFrame frame p) callers code)) rest post) :
    WP cfg (fuel+bodySteps p) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.AllocateRecord.body++code))) (bodyCost p*cfg.regularOpCost+fee cfg p+rest) post := by
  let op := cfg.regularOpCost
  let ac := allocated cfg s p
  let rf := resultFrame frame p
  let inner := innerFrame frame base.toArray.size code
  let outer := outerFrame frame base.toArray.size code
  let branchCode := WNear.Binary.AllocateRecord.record++code
  have cA : ac.host.gas.Credits (8*op+rest) := (allocated_gas cfg s p (8*op+rest)
    (hc.mono (by simp only [bodyCost,Nat.add_mul,op];omega))).2.2
  have cS : (selected cfg s p).host.gas.Credits (6*cfg.regularOpCost+rest) := by
    simpa only [selected,ac,op] using paid_credits ac op 2 (6*op+rest) (cA.mono (by omega))
  have fields := allocated_fields cfg s p
  have sm : (selected cfg s p).modules[rf.inst]?=some p.mi := by
    rw [selected,modules_paid,fields.2.1]
    exact hcode.allocation.retry.originalCode.search.module
  have mm : (selected cfg s p).mems[p.memoryIndex]?=some (allocatedMemory p) := by
    rw [selected,mems_paid]
    exact allocated_memory cfg s p hm
  have f0 : rf.locals[0]?=some (.i32 p.out) := by simp [rf,resultFrame,h0]
  have f1 : rf.locals[1]?=some (.i32 p.size) := by simp [rf,resultFrame,h1]
  have f2 : rf.locals[2]?=some (.i32 (result p)) := by simp [rf,resultFrame,show 2<frame.locals.size by omega]
  have spec := allocated_spec p hn
  have outBound : p.out.toNat+8≤(allocatedMemory p).byteSize := by have := hn.outputBound;omega
  have recordNext : WP cfg fuel (.next (atCode (recordStore (selected cfg s p) cfg.regularOpCost p.memoryIndex
      (allocatedMemory p) p.out (result p) p.size) limits base.toArray rf callers code)) rest post := by
    simpa only [after,rf] using hnext
  have record := wp_record cfg fuel rest (selected cfg s p) limits base.toArray rf callers code p.mi p.memoryIndex
    (allocatedMemory p) p.out (result p) p.size post f0 f1 f2 sm hcode.allocation.retry.originalCode.search.memoryIndex mm
    spec.1 outBound cS recordNext
  have branchNext : WP cfg (fuel+6) (.next (atCode (chargedStore (paid ac op 1) cfg.regularOpCost) limits base.toArray rf callers branchCode))
      (6*op+rest) post := by simpa only [selected,ac,paid,op,branchCode] using record
  have branch := wp_br_two_blocks cfg (fuel+6) (6*op+rest) (paid ac op 1) limits base.toArray rf callers branchCode
    WNear.Binary.AllocateRecord.ordinary [] post (paid_credits ac op 1 _ (cA.mono (by omega))) branchNext
  have setNext : WP cfg (fuel+7) (.next (atCode (chargedStore ac cfg.regularOpCost) limits base.toArray
      {inner with locals:=inner.locals.set! 2 (.i32 (result p))} callers [.br 1])) (7*op+rest) post := by
    have ce : cfg.regularOpCost+(6*op+rest)=7*op+rest := by dsimp [op];omega
    simpa only [ce,inner,innerFrame,outerFrame,rf,resultFrame,branchCode,emptyBlockFrame,paid,op,List.size_toArray,List.append_nil] using branch
  have set := wp_local_set cfg (fuel+7) (7*op+rest) ac limits base.toArray inner callers [.br 1]
    2 (.i32 (result p)) post (cA.mono (by dsimp [op];omega)) setNext
  have arr : (base++[Value.i32 (result p)]).toArray=base.toArray.push (.i32 (result p)) := by apply Array.toList_inj.mp;simp
  have arrZ : (base++[Value.i32 (AllocateZeroedRetry.result p.toZeroed)]).toArray=base.toArray.push (.i32 (AllocateZeroedRetry.result p.toZeroed)) := by
    simpa only [result] using arr
  have callNext : WP cfg (fuel+8) (.next (atCode (AllocateForwardRetry.callAfter313 cfg (paid s op 8) p.toZeroed) limits
      (base++[Value.i32 (AllocateZeroedRetry.result p.toZeroed)]).toArray inner callers [.local_set 2,.br 1])) (8*op+rest) post := by
    have ce : cfg.regularOpCost+(7*op+rest)=8*op+rest := by dsimp [op];omega
    simpa only [ce,allocated,ac,result,arrZ,op,Nat.add_assoc,Nat.reduceAdd] using set
  have cd := hcode.paid s op 8 frame.inst p
  have m8 : (paid s op 8).mems[p.memoryIndex]?=some p.memory := by rw [mems_paid];exact hm
  have g8 : (paid s op 8).globals[p.globalIndex]?=some p.global := by rw [globals_paid];exact hg
  have innerInst : inner.inst=frame.inst := rfl
  have allocCode : AllocateZeroedRetry.Code (paid s op 8) inner.inst p.toZeroed := by rw [innerInst];exact cd.allocation
  have fn153 : (paid s op 8).funcs[p.address153]?=some (.wasm WNear.Binary.AllocateZeroed.signature inner.inst WNear.Binary.AllocateZeroed.function) := by rw [innerInst];exact cd.function153
  have fn239 : (paid s op 8).funcs[p.address239]?=some (.wasm WNear.Binary.AllocateForward.signature inner.inst WNear.Binary.AllocateForward.function239) := by rw [innerInst];exact cd.function239
  have fn313 : (paid s op 8).funcs[p.address313]?=some (.wasm WNear.Binary.AllocateForward.signature inner.inst WNear.Binary.AllocateForward.function313) := by rw [innerInst];exact cd.function313
  have call := AllocateForwardRetry.wp_call313 cfg (fuel+8) (8*op+rest) (paid s op 8) limits base inner callers
    [.local_set 2,.br 1] p.toZeroed p.address153 p.address239 p.address313 post hn.allocation allocCode ha m8 g8 hv
    cd.index153 fn153 cd.index239 fn239 cd.index313 fn313 hd
    (paid_credits s op 8 _ (hc.mono (by simp only [bodyCost,fee,AllocateForwardRetry.fee,AllocateForwardRetry.cost313,AllocateForwardRetry.cost239,Nat.add_mul,op];omega))) callNext
  let cc := (AllocateForwardRetry.cost313 p.toZeroed+11)*op+fee cfg p+(8*op+rest)
  have arr2 : (base++[Value.i32 p.size,.i32 1]).toArray=(base.toArray.push (.i32 p.size)).push (.i32 1) := by apply Array.toList_inj.mp;simp
  have cnext : WP cfg (fuel+AllocateForwardRetry.steps313 p.toZeroed+9) (.next (atCode (paid s op 8) limits
      ((base.toArray.push (.i32 p.size)).push (.i32 1)) inner callers [.call 313,.local_set 2,.br 1])) cc post := by
    have fe : (fuel+8)+AllocateForwardRetry.steps313 p.toZeroed+1=fuel+AllocateForwardRetry.steps313 p.toZeroed+9 := by omega
    simpa only [fe,arr2,cc,op,fee] using call
  have i1 : inner.locals[1]?=some (.i32 p.size) := h1
  have i2 : inner.locals[2]?=some (.i32 1) := h2
  have i3 : inner.locals[3]?=some (.i32 1) := h3
  have g2 := wp_local_get cfg (fuel+AllocateForwardRetry.steps313 p.toZeroed+9) cc (paid s op 7) limits
    (base.toArray.push (.i32 p.size)) inner callers [.call 313,.local_set 2,.br 1] 2 (.i32 1) post i2
    (paid_credits s op 7 _ (hc.mono (by simp only [bodyCost,cc,fee,AllocateForwardRetry.cost313,AllocateForwardRetry.cost239,Nat.add_mul,op];omega))) cnext
  have g1 := wp_local_get cfg (fuel+AllocateForwardRetry.steps313 p.toZeroed+10) (op+cc) (paid s op 6) limits
    base.toArray inner callers [.local_get 2,.call 313,.local_set 2,.br 1] 1 (.i32 p.size) post i1
    (paid_credits s op 6 _ (hc.mono (by simp only [bodyCost,cc,fee,AllocateForwardRetry.cost313,AllocateForwardRetry.cost239,Nat.add_mul,op];omega))) g2
  have guardInner := wp_nonzero_guard cfg (fuel+AllocateForwardRetry.steps313 p.toZeroed+11) (op+(op+cc)) (paid s op 3) limits
    base.toArray inner callers [.local_get 1,.local_get 2,.call 313,.local_set 2,.br 1] 3 1 post i3 (by decide)
    (paid_credits s op 3 _ (hc.mono (by simp only [bodyCost,cc,fee,AllocateForwardRetry.cost313,AllocateForwardRetry.cost239,Nat.add_mul,op];omega))) g1
  have blockInner : WP cfg (fuel+AllocateForwardRetry.steps313 p.toZeroed+14) (.next (atCode (paid s op 3) limits base.toArray
      (emptyBlockFrame outer base.toArray.size WNear.Binary.AllocateRecord.ordinary) callers WNear.Binary.AllocateRecord.zeroed))
      (3*op+(op+(op+cc))) post := by
    simpa only [inner,innerFrame,outer,outerFrame,WNear.Binary.AllocateRecord.zeroed,op,Nat.add_assoc,Nat.reduceAdd] using guardInner
  have enterInner := wp_block_empty cfg (fuel+AllocateForwardRetry.steps313 p.toZeroed+14) _ (paid s op 3) limits base.toArray outer callers
    WNear.Binary.AllocateRecord.zeroed WNear.Binary.AllocateRecord.ordinary post
    (paid_credits s op 3 _ (hc.mono (by simp only [bodyCost,cc,fee,AllocateForwardRetry.cost313,AllocateForwardRetry.cost239,Nat.add_mul,op];omega))) blockInner
  have outer1 : outer.locals[1]?=some (.i32 p.size) := h1
  have guardOuter := wp_nonzero_guard cfg (fuel+AllocateForwardRetry.steps313 p.toZeroed+15) _ s limits base.toArray outer callers
    (.block .empty WNear.Binary.AllocateRecord.zeroed::WNear.Binary.AllocateRecord.ordinary) 1 p.size post outer1 hn.allocation.positive
    (hc.mono (by simp only [bodyCost,cc,fee,AllocateForwardRetry.cost313,AllocateForwardRetry.cost239,Nat.add_mul,op];omega)) enterInner
  have innerWhole : WP cfg (fuel+AllocateForwardRetry.steps313 p.toZeroed+18) (.next (atCode s limits base.toArray outer callers
      WNear.Binary.AllocateRecord.guarded)) (bodyCost p*cfg.regularOpCost+fee cfg p+rest) post := by
    have ce : 3*cfg.regularOpCost+(3*op+(op+(op+cc)))=bodyCost p*cfg.regularOpCost+fee cfg p+rest := by
      simp only [bodyCost,cc,fee,AllocateForwardRetry.cost313,AllocateForwardRetry.cost239,Nat.add_mul,op];omega
    rw [ce] at guardOuter
    simpa only [WNear.Binary.AllocateRecord.guarded,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using guardOuter
  have enterOuter := wp_block_empty cfg (fuel+AllocateForwardRetry.steps313 p.toZeroed+18) _ s limits base.toArray frame callers
    WNear.Binary.AllocateRecord.guarded (WNear.Binary.AllocateRecord.record++code) post hc innerWhole
  have fe : fuel+AllocateForwardRetry.steps313 p.toZeroed+18+1=fuel+bodySteps p := by
    simp only [bodySteps,AllocateForwardRetry.steps313,AllocateForwardRetry.steps239];omega
  simpa only [fe,WNear.Binary.AllocateRecord.body,List.cons_append,List.nil_append,outer,outerFrame] using enterOuter
end WNear.Proofs.AllocateRecord
