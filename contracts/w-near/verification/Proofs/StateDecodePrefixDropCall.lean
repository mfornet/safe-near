import Proofs.StateDecodePrefixArguments
import Proofs.StateDecodeSlicesCall

/-! The actual316 drop-four invocation rereads the current slice descriptor. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem funcs_paid (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl|succ n ih=>exact ih
def dropFourCode : Expr := [.local_get 2,.i32_const (32),.i32_binop .add,.local_get 1,.load .i32 none {align:=2,offset:=0},.local_get 1,.load .i32 none {align:=2,offset:=4},.i32_const (4),.i32_const (1052240)]

theorem wp_drop_four_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch slice _len : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h1 : frame.locals[1]?=some (.i32 slice))
    (h2 : frame.locals[2]?=some (.i32 scratch))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (he : s.mems[index]?=some memory)
    (b4 : slice.toNat+(0)+4≤memory.byteSize)
    (b6 : slice.toNat+(4)+4≤memory.byteSize)
    (hc : s.host.gas.Credits (9*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 9) limits
      ((((((stack).push (.i32 (scratch+(32)))).push (.i32 (readI32 memory (slice.toNat+(0))))).push (.i32 (readI32 memory (slice.toNat+(4))))).push (.i32 (4))).push (.i32 (1052240))) frame callers code)) rest post) :
    WP cfg (fuel+9) (.next (atCode s limits stack frame callers (dropFourCode++code)))
      (9*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have mm4 : (paid s op 4).modules[frame.inst]?=some mi := by rw [modules_paid];exact hm
  have me4 : (paid s op 4).mems[index]?=some memory := by rw [mems_paid];exact he
  have mm6 : (paid s op 6).modules[frame.inst]?=some mi := by rw [modules_paid];exact hm
  have me6 : (paid s op 6).mems[index]?=some memory := by rw [mems_paid];exact he
  have p8 := wp_i32_const cfg fuel (rest) (paid s op 8) limits (((((stack).push (.i32 (scratch+(32)))).push (.i32 (readI32 memory (slice.toNat+(0))))).push (.i32 (readI32 memory (slice.toNat+(4))))).push (.i32 (4))) frame callers code (1052240) post  (paid_credits s op 8 _ (hc.mono (by dsimp [op];omega))) hnext
  have p7 := wp_i32_const cfg (fuel+1) (op+(rest)) (paid s op 7) limits ((((stack).push (.i32 (scratch+(32)))).push (.i32 (readI32 memory (slice.toNat+(0))))).push (.i32 (readI32 memory (slice.toNat+(4))))) frame callers (.i32_const (1052240)::code) (4) post  (paid_credits s op 7 _ (hc.mono (by dsimp [op];omega))) p8
  have p6 := wp_i32_load cfg (fuel+2) (op+(op+(rest))) (paid s op 6) limits (((stack).push (.i32 (scratch+(32)))).push (.i32 (readI32 memory (slice.toNat+(0))))) frame callers (.i32_const (4)::.i32_const (1052240)::code) {align:=2,offset:=4} slice mi index memory post mm6 hi me6 b6 (paid_credits s op 6 _ (hc.mono (by dsimp [op];omega))) p7
  have p5 := wp_local_get cfg (fuel+3) (op+(op+(op+(rest)))) (paid s op 5) limits (((stack).push (.i32 (scratch+(32)))).push (.i32 (readI32 memory (slice.toNat+(0))))) frame callers (.load .i32 none {align:=2,offset:=4}::.i32_const (4)::.i32_const (1052240)::code) 1 (.i32 slice) post h1 (paid_credits s op 5 _ (hc.mono (by dsimp [op];omega))) p6
  have p4 := wp_i32_load cfg (fuel+4) (op+(op+(op+(op+(rest))))) (paid s op 4) limits ((stack).push (.i32 (scratch+(32)))) frame callers (.local_get 1::.load .i32 none {align:=2,offset:=4}::.i32_const (4)::.i32_const (1052240)::code) {align:=2,offset:=0} slice mi index memory post mm4 hi me4 b4 (paid_credits s op 4 _ (hc.mono (by dsimp [op];omega))) p5
  have p3 := wp_local_get cfg (fuel+5) (op+(op+(op+(op+(op+(rest)))))) (paid s op 3) limits ((stack).push (.i32 (scratch+(32)))) frame callers (.load .i32 none {align:=2,offset:=0}::.local_get 1::.load .i32 none {align:=2,offset:=4}::.i32_const (4)::.i32_const (1052240)::code) 1 (.i32 slice) post h1 (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) p4
  have p2 := wp_i32_add cfg (fuel+6) (op+(op+(op+(op+(op+(op+(rest))))))) (paid s op 2) limits (stack) frame callers (.local_get 1::.load .i32 none {align:=2,offset:=0}::.local_get 1::.load .i32 none {align:=2,offset:=4}::.i32_const (4)::.i32_const (1052240)::code) scratch (32) post  (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) p3
  have p1 := wp_i32_const cfg (fuel+7) (op+(op+(op+(op+(op+(op+(op+(rest)))))))) (paid s op 1) limits ((stack).push (.i32 (scratch))) frame callers (.i32_binop .add::.local_get 1::.load .i32 none {align:=2,offset:=0}::.local_get 1::.load .i32 none {align:=2,offset:=4}::.i32_const (4)::.i32_const (1052240)::code) (32) post  (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) p2
  have p0 := wp_local_get cfg (fuel+8) (op+(op+(op+(op+(op+(op+(op+(op+(rest))))))))) s limits (stack) frame callers (.i32_const (32)::.i32_binop .add::.local_get 1::.load .i32 none {align:=2,offset:=0}::.local_get 1::.load .i32 none {align:=2,offset:=4}::.i32_const (4)::.i32_const (1052240)::code) 2 (.i32 scratch) post h2 (hc.mono (by dsimp [op];omega)) p1
  have cost : cfg.regularOpCost+(op+(op+(op+(op+(op+(op+(op+(op+(rest)))))))))=9*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [dropFourCode,List.cons_append,List.nil_append,cost] using p0

def dropFourAfter (cfg : WasmConfig) (s : Store NearState) (i : Nat) (m : Memory) (scratch pointer len : UInt32) :=
  StateDecodeSlices.callAfter true (paid s cfg.regularOpCost 9) cfg.regularOpCost i m (scratch+32) pointer len 4

theorem wp_drop_four_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch slice pointer len : UInt32) (mi : ModuleInst) (i address : Nat) (m : Memory) (post : Post)
    (h1 : frame.locals[1]?=some (.i32 slice)) (h2 : frame.locals[2]?=some (.i32 scratch))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some i) (he : s.mems[i]?=some m)
    (hfi : mi.funcAddrs[361]?=some address)
    (hf : s.funcs[address]?=some (.wasm WNear.Binary.StateDecodeSlices.signature frame.inst (WNear.Binary.StateDecodeSlices.function true)))
    (hw : m.wf) (hs : slice.toNat+8≤m.byteSize) (ho : (scratch+32).toNat+8≤m.byteSize)
    (hp : readI32 m slice.toNat=pointer) (hl : readI32 m (slice.toNat+4)=len) (hn : 4≤len.toNat)
    (hd : callers.length+1<limits.maxCallDepth) (hc : s.host.gas.Credits (35*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (dropFourAfter cfg s i m scratch pointer len) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+26) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateDecodePrefix.dropFour++code)))
      (35*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let args:=paid s op 9
  have call:=StateDecodeSlices.wp_call cfg fuel rest args limits base frame callers code true (scratch+32) pointer len 4 1052240 mi i address m post
    (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) hfi (by rw[funcs_paid];exact hf) hw ho hn hd
    (paid_credits s op 9 _ (hc.mono (by simp only[WNear.Binary.StateDecodeSlices.bodyCost,ite_true];dsimp[op];omega))) hnext
  let argv : Array Value := (((((base.toArray.push (Value.i32 (scratch+32))).push (Value.i32 (readI32 m (slice.toNat+0)))).push (Value.i32 (readI32 m (slice.toNat+4)))).push (Value.i32 4)).push (Value.i32 1052240))
  have operands : (base++[Value.i32 (scratch+32),.i32 pointer,.i32 len,.i32 4,.i32 1052240]).toArray=argv := by
    dsimp only[argv]
    rw[Nat.add_zero,hp,hl];apply Array.toList_inj.mp;simp
  have cn : WP cfg (fuel+17) (.next (atCode args limits argv frame callers (.call 361::code))) (26*op+rest) post := by
    simpa only[operands,WNear.Binary.StateDecodeSlices.index,WNear.Binary.StateDecodeSlices.bodySteps,WNear.Binary.StateDecodeSlices.bodyCost,ite_true,Nat.reduceAdd,op] using call
  have result:=wp_drop_four_arguments cfg (fuel+17) (26*op+rest) s limits base.toArray frame callers (.call 361::code) scratch slice 0 mi i m post
    h1 h2 hm hi he (by omega) hs (hc.mono (by dsimp[op];omega)) cn
  simpa only[dropFourCode,WNear.Binary.StateDecodePrefix.dropFour,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 9*cfg.regularOpCost+(26*op+rest)=35*cfg.regularOpCost+rest by dsimp[op];omega] using result
end WNear.Proofs.StateDecodePrefix
