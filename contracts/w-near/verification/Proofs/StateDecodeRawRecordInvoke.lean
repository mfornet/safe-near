import Proofs.StateDecodeRawRecordCall
import Proofs.StateDecodeRawArguments

/-! f769's actual argument sequence followed by the complete deployed770 call. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode recordCallAfter
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem funcs_paid (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with |zero=>rfl|succ n ih=>exact ih

def invokedRecord (cfg : WasmConfig) (s : Store NearState) (q : AllocatePositive.Layout) (scratch : UInt32) :=
  recordCallAfter cfg (paid s cfg.regularOpCost 6) q (scratch+8)

theorem wp_invoke_record (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (q : AllocatePositive.Layout) (scratch : UInt32) (a581 a236 a310 address : Nat) (post : Post)
    (hn : AllocatePositive.Native q) (hcode : RecordCode s frame.inst q a581 a236 a310)
    (ha : q.allocator=1074896)
    (h1 : frame.locals[1]?=some (.i32 q.size)) (h2 : frame.locals[2]?=some (.i32 1))
    (h3 : frame.locals[3]?=some (.i32 scratch))
    (hm : s.mems[q.memoryIndex]?=some q.memory) (hg : s.globals[q.globalIndex]?=some q.global)
    (hv : q.global.value=.i32 q.sp) (hb : (scratch+8).toNat+8≤q.memory.byteSize)
    (hi : q.mi.funcAddrs[770]?=some address)
    (hf : s.funcs[address]?=some (.wasm WNear.Binary.StateDecodeRaw.recordSignature frame.inst WNear.Binary.StateDecodeRaw.function770))
    (hd : callers.length+6<limits.maxCallDepth) (hc : s.host.gas.Credits (419*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (invokedRecord cfg s q scratch) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+336) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateDecodeRaw.arguments770++code)))
      (419*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  have call:=wp_record_call cfg fuel rest (paid s op 6) limits base frame callers code q (scratch+8) a581 a236 a310 address post hn
    (hcode.paid s op 6 frame.inst q a581 a236 a310) ha
    (by rw[mems_paid];exact hm) (by rw[globals_paid];exact hg) hv hb hi (by rw[funcs_paid];exact hf) hd
    (paid_credits s op 6 _ (hc.mono (by dsimp[op];omega))) hnext
  have operands : (base++[Value.i32 (scratch+8),.i32 q.size,.i32 1,.i32 0]).toArray=
      ((((base.toArray.push (.i32 (scratch+8))).push (.i32 q.size)).push (.i32 1)).push (.i32 0)) := by
    apply Array.toList_inj.mp;simp
  have cn : WP cfg (fuel+330) (.next (atCode (paid s op 6) limits
      ((((base.toArray.push (.i32 (scratch+8))).push (.i32 q.size)).push (.i32 1)).push (.i32 0)) frame callers (.call 770::code)))
      (413*op+rest) post := by simpa only[operands,op] using call
  have args:=wp_arguments770 cfg (fuel+330) (413*op+rest) s limits base.toArray frame callers (.call 770::code) scratch q.size 1 post h1 h2 h3
    (hc.mono (by dsimp[op];omega)) cn
  simpa only[arguments770Code,WNear.Binary.StateDecodeRaw.arguments770,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 6*cfg.regularOpCost+(413*op+rest)=419*cfg.regularOpCost+rest by dsimp[op];omega] using args
end WNear.Proofs.StateDecodeRaw
