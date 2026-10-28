import Proofs.StateDecodePrefixTakeCall

/-! Actual316 payload-drop arguments and complete361 call. Descriptor reads
come from the current memory; no original descriptor equality is assumed. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem funcs_paid(s:Store NearState)(op n:Nat):(paid s op n).funcs=s.funcs:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

def dropPayloadArguments:Expr:=[.local_get 2,.i32_const 8,.i32_binop .add,.local_get 1,.load .i32 none {align:=2,offset:=0},.local_get 1,.load .i32 none {align:=2,offset:=4},.local_get 3,.i32_const 1052524]

theorem wp_drop_payload_arguments (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(scratch slice count:UInt32)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h1:frame.locals[1]?=some (.i32 slice))(h2:frame.locals[2]?=some (.i32 scratch))(h3:frame.locals[3]?=some (.i32 count))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hb:slice.toNat+8≤memory.byteSize)(hc:s.host.gas.Credits (9*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 9) limits
      (((((stack.push (.i32 (scratch+8))).push (.i32 (readI32 memory (slice.toNat+0)))).push (.i32 (readI32 memory (slice.toNat+4)))).push (.i32 count)).push (.i32 1052524)) frame callers code)) rest post):
    WP cfg (fuel+9) (.next (atCode s limits stack frame callers (dropPayloadArguments++code))) (9*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have p8:=wp_i32_const cfg (fuel+0) (rest) (paid s op 8) limits ((((stack.push (.i32 (scratch+8))).push (.i32 (readI32 memory (slice.toNat+0)))).push (.i32 (readI32 memory (slice.toNat+4)))).push (.i32 (count))) frame callers (code) 1052524 post (paid_credits s op 8 _ (hc.mono (by dsimp[op];omega))) hn
  have p7:=wp_local_get cfg (fuel+1) (op+(rest)) (paid s op 7) limits (((stack.push (.i32 (scratch+8))).push (.i32 (readI32 memory (slice.toNat+0)))).push (.i32 (readI32 memory (slice.toNat+4)))) frame callers (.i32_const 1052524::code) 3 (.i32 (count)) post h3 (paid_credits s op 7 _ (hc.mono (by dsimp[op];omega))) p8
  have mm6:(paid s op 6).modules[frame.inst]?=some mi:=by rw[modules_paid];exact hm
  have me6:(paid s op 6).mems[index]?=some memory:=by rw[mems_paid];exact he
  have p6:=wp_i32_load cfg (fuel+2) (op+(op+(rest))) (paid s op 6) limits ((stack.push (.i32 (scratch+8))).push (.i32 (readI32 memory (slice.toNat+0)))) frame callers (.local_get 3::.i32_const 1052524::code) {align:=2,offset:=4} slice mi index memory post mm6 hi me6 (by dsimp;omega) (paid_credits s op 6 _ (hc.mono (by dsimp[op];omega))) p7
  have p5:=wp_local_get cfg (fuel+3) (op+(op+(op+(rest)))) (paid s op 5) limits ((stack.push (.i32 (scratch+8))).push (.i32 (readI32 memory (slice.toNat+0)))) frame callers (.load .i32 none {align:=2,offset:=4}::.local_get 3::.i32_const 1052524::code) 1 (.i32 (slice)) post h1 (paid_credits s op 5 _ (hc.mono (by dsimp[op];omega))) p6
  have mm4:(paid s op 4).modules[frame.inst]?=some mi:=by rw[modules_paid];exact hm
  have me4:(paid s op 4).mems[index]?=some memory:=by rw[mems_paid];exact he
  have p4:=wp_i32_load cfg (fuel+4) (op+(op+(op+(op+(rest))))) (paid s op 4) limits (stack.push (.i32 (scratch+8))) frame callers (.local_get 1::.load .i32 none {align:=2,offset:=4}::.local_get 3::.i32_const 1052524::code) {align:=2,offset:=0} slice mi index memory post mm4 hi me4 (by dsimp;omega) (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) p5
  have p3:=wp_local_get cfg (fuel+5) (op+(op+(op+(op+(op+(rest)))))) (paid s op 3) limits (stack.push (.i32 (scratch+8))) frame callers (.load .i32 none {align:=2,offset:=0}::.local_get 1::.load .i32 none {align:=2,offset:=4}::.local_get 3::.i32_const 1052524::code) 1 (.i32 (slice)) post h1 (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) p4
  have p2:=wp_i32_add cfg (fuel+6) (op+(op+(op+(op+(op+(op+(rest))))))) (paid s op 2) limits stack frame callers (.local_get 1::.load .i32 none {align:=2,offset:=0}::.local_get 1::.load .i32 none {align:=2,offset:=4}::.local_get 3::.i32_const 1052524::code) scratch 8 post (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) p3
  have p1:=wp_i32_const cfg (fuel+7) (op+(op+(op+(op+(op+(op+(op+(rest)))))))) (paid s op 1) limits (stack.push (.i32 (scratch))) frame callers (.i32_binop .add::.local_get 1::.load .i32 none {align:=2,offset:=0}::.local_get 1::.load .i32 none {align:=2,offset:=4}::.local_get 3::.i32_const 1052524::code) 8 post (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) p2
  have p0:=wp_local_get cfg (fuel+8) (op+(op+(op+(op+(op+(op+(op+(op+(rest))))))))) s limits stack frame callers (.i32_const 8::.i32_binop .add::.local_get 1::.load .i32 none {align:=2,offset:=0}::.local_get 1::.load .i32 none {align:=2,offset:=4}::.local_get 3::.i32_const 1052524::code) 2 (.i32 (scratch)) post h2 (hc.mono (by dsimp[op];omega)) p1
  simpa only[dropPayloadArguments,List.cons_append,List.nil_append,Nat.add_zero,op,show fuel+8+1=fuel+9 by omega,show op+(op+(op+(op+(op+(op+(op+(op+(op+(rest)))))))))=9*cfg.regularOpCost+rest by dsimp[op];omega] using p0


def dropPayloadAfter (cfg:WasmConfig)(s:Store NearState)(index:Nat)(memory:Memory)(scratch slice count:UInt32):=
  StateDecodeSlices.callAfter true (paid s cfg.regularOpCost 9) cfg.regularOpCost index memory (scratch+8)
    (readI32 memory slice.toNat) (readI32 memory (slice.toNat+4)) count

theorem wp_drop_payload_call (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(scratch slice count:UInt32)
    (mi:ModuleInst)(index address:Nat)(memory:Memory)(post:Post)
    (h1:frame.locals[1]?=some (.i32 slice))(h2:frame.locals[2]?=some (.i32 scratch))(h3:frame.locals[3]?=some (.i32 count))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hfi:mi.funcAddrs[361]?=some address)
    (hf:s.funcs[address]?=some (.wasm WNear.Binary.StateDecodeSlices.signature frame.inst (WNear.Binary.StateDecodeSlices.function true)))
    (hw:memory.wf)(hb:slice.toNat+8≤memory.byteSize)(ho:(scratch+8).toNat+8≤memory.byteSize)
    (hs:count.toNat≤(readI32 memory (slice.toNat+4)).toNat)(hd:callers.length+1<limits.maxCallDepth)
    (hc:s.host.gas.Credits (35*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (dropPayloadAfter cfg s index memory scratch slice count) limits base.toArray frame callers code)) rest post):
    WP cfg (fuel+26) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateDecodePrefix.dropPayload++code))) (35*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let args:=paid s op 9
  have mm:args.modules[frame.inst]?=some mi:=by rw[modules_paid];exact hm
  have me:args.mems[index]?=some memory:=by rw[mems_paid];exact he
  have mf:args.funcs[address]?=some (.wasm WNear.Binary.StateDecodeSlices.signature frame.inst (WNear.Binary.StateDecodeSlices.function true)):=by rw[funcs_paid];exact hf
  have ca:=paid_credits s op 9 (26*op+rest) (hc.mono (by dsimp[op];omega))
  have next:WP cfg fuel (.next (atCode (StateDecodeSlices.callAfter true args op index memory (scratch+8) (readI32 memory slice.toNat) (readI32 memory (slice.toNat+4)) count) limits base.toArray frame callers code)) rest post:=hn
  have call:=StateDecodeSlices.wp_call cfg fuel rest args limits base frame callers code true (scratch+8) (readI32 memory slice.toNat) (readI32 memory (slice.toNat+4)) count 1052524 mi index address memory post mm hi me hfi mf hw ho hs hd ca next
  have operands:(base++[Value.i32 (scratch+8),.i32 (readI32 memory slice.toNat),.i32 (readI32 memory (slice.toNat+4)),.i32 count,.i32 1052524]).toArray=
      (((((base.toArray.push (.i32 (scratch+8))).push (.i32 (readI32 memory (slice.toNat+0)))).push (.i32 (readI32 memory (slice.toNat+4)))).push (.i32 count)).push (.i32 1052524)):=by apply Array.toList_inj.mp;simp
  have cn:WP cfg (fuel+17) (.next (atCode args limits
      (((((base.toArray.push (.i32 (scratch+8))).push (.i32 (readI32 memory (slice.toNat+0)))).push (.i32 (readI32 memory (slice.toNat+4)))).push (.i32 count)).push (.i32 1052524)) frame callers (.call 361::code))) (26*op+rest) post:=by
    rw[operands] at call
    simpa only[WNear.Binary.StateDecodeSlices.index,WNear.Binary.StateDecodeSlices.bodySteps,WNear.Binary.StateDecodeSlices.bodyCost,ite_true,Nat.reduceAdd,op] using call
  have argsWP:=wp_drop_payload_arguments cfg (fuel+17) (26*op+rest) s limits base.toArray frame callers (.call 361::code) scratch slice count mi index memory post h1 h2 h3 hm hi he hb (hc.mono (by dsimp[op];omega)) cn
  simpa only[WNear.Binary.StateDecodePrefix.dropPayload,dropPayloadArguments,List.cons_append,List.nil_append,
    show fuel+17+9=fuel+26 by omega,show 9*cfg.regularOpCost+(26*op+rest)=35*cfg.regularOpCost+rest by dsimp[op];omega] using argsWP
end WNear.Proofs.StateDecodePrefix
