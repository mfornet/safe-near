import Proofs.StateDecodePrefixTakeCall

/-! Actual316 payload-slice arguments use the cached count and remaining length. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem funcs_paid (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with |zero=>rfl|succ n ih=>exact ih
def takePayloadCode : Expr := [.local_get 2,.i32_const (16),.i32_binop .add,.local_get 1,.load .i32 none {align:=2,offset:=0},.local_get 5,.local_get 3,.i32_const (1052508)]

theorem wp_payload_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch slice len count : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h1 : frame.locals[1]?=some (.i32 slice))
    (h2 : frame.locals[2]?=some (.i32 scratch))
    (h5 : frame.locals[5]?=some (.i32 len))
    (h3 : frame.locals[3]?=some (.i32 count))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (he : s.mems[index]?=some memory)
    (b4 : slice.toNat+(0)+4≤memory.byteSize)
    (hc : s.host.gas.Credits (8*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 8) limits
      ((((((stack).push (.i32 (scratch+(16)))).push (.i32 (readI32 memory (slice.toNat+(0))))).push (.i32 (len))).push (.i32 count)).push (.i32 (1052508))) frame callers code)) rest post) :
    WP cfg (fuel+8) (.next (atCode s limits stack frame callers (takePayloadCode++code)))
      (8*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have mm4 : (paid s op 4).modules[frame.inst]?=some mi := by rw [modules_paid];exact hm
  have me4 : (paid s op 4).mems[index]?=some memory := by rw [mems_paid];exact he
  have p7 := wp_i32_const cfg fuel (rest) (paid s op 7) limits (((((stack).push (.i32 (scratch+(16)))).push (.i32 (readI32 memory (slice.toNat+(0))))).push (.i32 (len))).push (.i32 count)) frame callers code (1052508) post  (paid_credits s op 7 _ (hc.mono (by dsimp [op];omega))) hnext
  have p6 := wp_local_get cfg (fuel+1) (op+(rest)) (paid s op 6) limits ((((stack).push (.i32 (scratch+(16)))).push (.i32 (readI32 memory (slice.toNat+(0))))).push (.i32 (len))) frame callers (.i32_const (1052508)::code) 3 (.i32 count) post h3  (paid_credits s op 6 _ (hc.mono (by dsimp [op];omega))) p7
  have p5 := wp_local_get cfg (fuel+2) (op+(op+(rest))) (paid s op 5) limits (((stack).push (.i32 (scratch+(16)))).push (.i32 (readI32 memory (slice.toNat+(0))))) frame callers (.local_get 3::.i32_const (1052508)::code) 5 (.i32 len) post h5 (paid_credits s op 5 _ (hc.mono (by dsimp [op];omega))) p6
  have p4 := wp_i32_load cfg (fuel+3) (op+(op+(op+(rest)))) (paid s op 4) limits ((stack).push (.i32 (scratch+(16)))) frame callers (.local_get 5::.local_get 3::.i32_const (1052508)::code) {align:=2,offset:=0} slice mi index memory post mm4 hi me4 b4 (paid_credits s op 4 _ (hc.mono (by dsimp [op];omega))) p5
  have p3 := wp_local_get cfg (fuel+4) (op+(op+(op+(op+(rest))))) (paid s op 3) limits ((stack).push (.i32 (scratch+(16)))) frame callers (.load .i32 none {align:=2,offset:=0}::.local_get 5::.local_get 3::.i32_const (1052508)::code) 1 (.i32 slice) post h1 (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) p4
  have p2 := wp_i32_add cfg (fuel+5) (op+(op+(op+(op+(op+(rest)))))) (paid s op 2) limits (stack) frame callers (.local_get 1::.load .i32 none {align:=2,offset:=0}::.local_get 5::.local_get 3::.i32_const (1052508)::code) scratch (16) post  (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) p3
  have p1 := wp_i32_const cfg (fuel+6) (op+(op+(op+(op+(op+(op+(rest))))))) (paid s op 1) limits ((stack).push (.i32 (scratch))) frame callers (.i32_binop .add::.local_get 1::.load .i32 none {align:=2,offset:=0}::.local_get 5::.local_get 3::.i32_const (1052508)::code) (16) post  (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) p2
  have p0 := wp_local_get cfg (fuel+7) (op+(op+(op+(op+(op+(op+(op+(rest)))))))) s limits (stack) frame callers (.i32_const (16)::.i32_binop .add::.local_get 1::.load .i32 none {align:=2,offset:=0}::.local_get 5::.local_get 3::.i32_const (1052508)::code) 2 (.i32 scratch) post h2 (hc.mono (by dsimp [op];omega)) p1
  have cost : cfg.regularOpCost+(op+(op+(op+(op+(op+(op+(op+(rest))))))))=8*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [takePayloadCode,List.cons_append,List.nil_append,cost] using p0

theorem payload_code_eq : WNear.Binary.StateDecodePrefix.takePayload=takePayloadCode++[.call 362]:=rfl

def payloadAfter (cfg : WasmConfig) (s : Store NearState) (index : Nat) (memory : Memory) (scratch pointer len count : UInt32) :=
  StateDecodeSlices.callAfter false (paid s cfg.regularOpCost 8) cfg.regularOpCost index memory
    (scratch+16) pointer len count

theorem wp_payload_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (scratch slice pointer len count : UInt32)
    (mi : ModuleInst) (index address : Nat) (memory : Memory) (post : Post)
    (h1 : frame.locals[1]?=some (.i32 slice)) (h2 : frame.locals[2]?=some (.i32 scratch)) (h5 : frame.locals[5]?=some (.i32 len)) (h3 : frame.locals[3]?=some (.i32 count))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (he : s.mems[index]?=some memory)
    (hfi : mi.funcAddrs[362]?=some address)
    (hf : s.funcs[address]?=some (.wasm WNear.Binary.StateDecodeSlices.signature frame.inst (WNear.Binary.StateDecodeSlices.function false)))
    (hwf : memory.wf) (hs : slice.toNat+4≤memory.byteSize)
    (ho : (scratch+16).toNat+8≤memory.byteSize)
    (hp : readI32 memory slice.toNat=pointer) (hn : count.toNat≤len.toNat)
    (hd : callers.length+1<limits.maxCallDepth) (hc : s.host.gas.Credits (30*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (payloadAfter cfg s index memory scratch pointer len count) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+21) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateDecodePrefix.takePayload++code)))
      (30*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let args := paid s op 8
  let out := scratch+16
  have mm : args.modules[frame.inst]?=some mi := by rw [modules_paid];exact hm
  have me : args.mems[index]?=some memory := by rw [mems_paid];exact he
  have mf : args.funcs[address]?=some (.wasm WNear.Binary.StateDecodeSlices.signature frame.inst (WNear.Binary.StateDecodeSlices.function false)) := by rw [funcs_paid];exact hf
  have ca := paid_credits s op 8 (22*op+rest) (hc.mono (by dsimp [op];omega))
  have next : WP cfg fuel (.next (atCode (StateDecodeSlices.callAfter false args op index memory out pointer len count) limits base.toArray frame callers code)) rest post := hnext
  have call := StateDecodeSlices.wp_call cfg fuel rest args limits base frame callers code false out pointer len
    count (1052508) mi index address memory post
    mm hi me hfi mf hwf ho hn hd ca next
  have operands : (base++[Value.i32 out,.i32 pointer,.i32 len,.i32 count,.i32 (1052508)]).toArray=
      (((((base.toArray.push (.i32 out)).push (.i32 (readI32 memory (slice.toNat+0)))).push (.i32 len)).push (.i32 count)).push (.i32 (1052508))) := by
    simp only [Nat.add_zero,hp]
    apply Array.toList_inj.mp;simp
  have cn : WP cfg (fuel+13) (.next (atCode args limits
      (((((base.toArray.push (.i32 out)).push (.i32 (readI32 memory (slice.toNat+0)))).push (.i32 len)).push (.i32 count)).push (.i32 (1052508))) frame callers (.call 362::code))) (22*op+rest) post := by
    rw [operands] at call
    simpa only [WNear.Binary.StateDecodeSlices.index,WNear.Binary.StateDecodeSlices.bodySteps,WNear.Binary.StateDecodeSlices.bodyCost,
      Bool.false_eq_true,ite_false,Nat.reduceAdd,op] using call
  have arguments := wp_payload_arguments cfg (fuel+13) (22*op+rest) s limits base.toArray frame callers (.call 362::code) scratch slice len count mi index memory post
    h1 h2 h5 h3 hm hi he (by simpa only [Nat.add_zero] using hs) (hc.mono (by dsimp [op];omega)) cn
  have ce : 8*cfg.regularOpCost+(22*op+rest)=30*cfg.regularOpCost+rest := by dsimp [op];omega
  rw [ce] at arguments
  simpa only [payload_code_eq,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using arguments
end WNear.Proofs.StateDecodePrefix
