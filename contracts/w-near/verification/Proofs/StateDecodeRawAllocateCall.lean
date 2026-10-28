import Proofs.StateDecodeRawRecordState

/-! f770's actual get/get/call310/set allocation sequence. The nested call is
proved from the original allocator domain and installed function descriptors. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode allocatedRecord recordInput AllocateRawForwardDirect.callAfter310
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with |zero=>rfl|succ n ih=>exact ih

theorem wp_raw_allocate (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (q : AllocatePositive.Layout) (a581 a236 a310 : Nat) (post : Post)
    (hn : AllocatePositive.Native q) (hcode : RecordCode s frame.inst q a581 a236 a310)
    (ha : q.allocator=1074896) (h1 : frame.locals[1]?=some (.i32 q.size))
    (h2 : frame.locals[2]?=some (.i32 1))
    (hm : s.mems[q.memoryIndex]?=some q.memory) (hg : s.globals[q.globalIndex]?=some q.global)
    (hv : q.global.value=.i32 q.sp) (hd : callers.length+5<limits.maxCallDepth)
    (hc : s.host.gas.Credits (390*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (recordInput cfg s q) limits base.toArray
      (allocationFrame frame q) callers code)) rest post) :
    WP cfg (fuel+313) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateDecodeRaw.rawCall++code)))
      (390*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let called:=allocatedRecord cfg s q
  have cc : called.host.gas.Credits (op+rest) := by
    unfold called allocatedRecord
    exact (AllocateRawForwardDirect.callAfter310_gas cfg (paid s op 2) q (op+rest)
      (paid_credits s op 2 _ (hc.mono (by simp only [AllocateRawForwardDirect.cost310,AllocateRawForwardDirect.cost236];dsimp[op];omega)))).2.2
  have set:=wp_local_set cfg fuel rest called limits base.toArray frame callers code 2 (.i32 (AllocatePositive.result q)) post cc
    (by simpa only[recordInput,allocationFrame,called,paid,op] using hnext)
  have arr : (base++[Value.i32 (AllocatePositive.result q)]).toArray=base.toArray.push (.i32 (AllocatePositive.result q)) := by
    apply Array.toList_inj.mp;simp
  have call:=AllocateRawForwardDirect.wp_call310 cfg (fuel+1) (op+rest) (paid s op 2) limits base frame callers
    (.local_set 2::code) q a581 a236 a310 post hn (hcode.allocation.paid s op 2 frame.inst q) ha
    (by rw[mems_paid];exact hm) (by rw[globals_paid];exact hg) hv
    hcode.index581 (hcode.paid s op 2 frame.inst q a581 a236 a310).function581
    hcode.index236 (hcode.paid s op 2 frame.inst q a581 a236 a310).function236
    hcode.index310 (hcode.paid s op 2 frame.inst q a581 a236 a310).function310 hd
    (paid_credits s op 2 _ (hc.mono (by simp only[AllocateRawForwardDirect.cost310,AllocateRawForwardDirect.cost236];dsimp[op];omega)))
    (by simpa only[allocatedRecord,called,arr,op] using set)
  have operands : (base++[Value.i32 q.size,.i32 1]).toArray=(base.toArray.push (.i32 q.size)).push (.i32 1) := by
    apply Array.toList_inj.mp;simp
  have cn : WP cfg (fuel+311) (.next (atCode (paid s op 2) limits ((base.toArray.push (.i32 q.size)).push (.i32 1)) frame callers
      (.call 310::.local_set 2::code))) (387*op+(op+rest)) post := by
    simpa only[AllocateRawForwardDirect.steps310,AllocateRawForwardDirect.steps236,AllocateRawForwardDirect.cost310,
      AllocateRawForwardDirect.cost236,operands,Nat.add_assoc,Nat.reduceAdd,op] using call
  have second:=wp_local_get cfg (fuel+311) (387*op+(op+rest)) (paid s op 1) limits (base.toArray.push (.i32 q.size)) frame callers
    (.call 310::.local_set 2::code) 2 (.i32 1) post h2 (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) cn
  have first:=wp_local_get cfg (fuel+312) (op+(387*op+(op+rest))) s limits base.toArray frame callers
    (.local_get 2::.call 310::.local_set 2::code) 1 (.i32 q.size) post h1 (hc.mono (by dsimp[op];omega)) second
  simpa only[WNear.Binary.StateDecodeRaw.rawCall,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(op+(387*op+(op+rest)))=390*cfg.regularOpCost+rest by dsimp[op];omega] using first
end WNear.Proofs.StateDecodeRaw
