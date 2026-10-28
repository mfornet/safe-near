import Binary.StateDecodeBorsh
import Proofs.StateDecodeScalarOutput
import Proofs.StateDecodePrefixOutputSteps

/-! Actual425 writes cached values in deployed order. The rule retains arbitrary
output aliases and the exact UInt32 added addresses. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
open StateDecodeScalar (store64Added wp_store64_added)
attribute [local irreducible] WP atCode readI32 readI64 writeI32 writeI64
private theorem paid_modules(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_mems(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
def store32Added (s : Store NearState) (op index : Nat) (memory : Memory) (pointer delta : UInt32) (value : UInt32) :=
  storeI32 (paid s op 5) index (pointer+delta).toNat memory value

theorem wp_store32_added (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr)
    (destination source : Nat) (pointer delta : UInt32) (value : UInt32)
    (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hp : frame.locals[destination]?=some (.i32 pointer)) (hv : frame.locals[source]?=some (.i32 value))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index) (hmem : s.mems[index]?=some memory)
    (hb : (pointer+delta).toNat+4≤memory.byteSize) (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (store32Added s cfg.regularOpCost index memory pointer delta value) limits stack frame callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers
      (.local_get destination::.i32_const delta::.i32_binop .add::.local_get source::.store .i32 none {align:=2,offset:=0}::code)))
      (5*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  have mm : (paid s op 4).modules[frame.inst]?=some mi := by rw [paid_modules];exact hm
  have me : (paid s op 4).mems[index]?=some memory := by rw [paid_mems];exact hmem
  have st := wp_i32_store cfg fuel rest (paid s op 4) limits stack frame callers code {align:=2,offset:=0}
    (pointer+delta) value mi index memory post mm hi me hb (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) hnext
  have gv := wp_local_get cfg (fuel+1) (op+rest) (paid s op 3) limits (stack.push (.i32 (pointer+delta))) frame callers
    (.store .i32 none {align:=2,offset:=0}::code) source (.i32 value) post hv
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) st
  have add := wp_i32_add cfg (fuel+2) (op+(op+rest)) (paid s op 2) limits stack frame callers
    (.local_get source::.store .i32 none {align:=2,offset:=0}::code) pointer delta post
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) gv
  have constant := wp_i32_const cfg (fuel+3) (op+(op+(op+rest))) (paid s op 1) limits (stack.push (.i32 pointer)) frame callers
    (.i32_binop .add::.local_get source::.store .i32 none {align:=2,offset:=0}::code) delta post
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) add
  have get := wp_local_get cfg (fuel+4) (op+(op+(op+(op+rest)))) s limits stack frame callers
    (.i32_const delta::.i32_binop .add::.local_get source::.store .i32 none {align:=2,offset:=0}::code) destination (.i32 pointer) post hp
    (hc.mono (by dsimp[op];omega)) constant
  simpa only [Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(op+(op+(op+(op+rest))))=5*cfg.regularOpCost+rest by dsimp[op];omega] using get

private theorem modules64(s:Store NearState)(op index:Nat)(m:Memory)(p d:UInt32)(v:UInt64):
    (store64Added s op index m p d v).modules=s.modules:=by
  change (paid s op 5).modules=s.modules;exact paid_modules s op 5
private theorem modules32(s:Store NearState)(op index:Nat)(m:Memory)(p d:UInt32)(v:UInt32):
    (store32Added s op index m p d v).modules=s.modules:=by
  change (paid s op 5).modules=s.modules;exact paid_modules s op 5
private theorem credits64(s:Store NearState)(op index rest:Nat)(m:Memory)(p d:UInt32)(v:UInt64)
    (hc:s.host.gas.Credits (5*op+rest)):
    (store64Added s op index m p d v).host.gas.Credits rest:=by
  simpa only[store64Added,storeI64_host] using paid_credits s op 5 rest hc
private theorem credits32(s:Store NearState)(op index rest:Nat)(m:Memory)(p d:UInt32)(v:UInt32)
    (hc:s.host.gas.Credits (5*op+rest)):
    (store32Added s op index m p d v).host.gas.Credits rest:=by
  simpa only[store32Added,storeI32_host] using paid_credits s op 5 rest hc

def cachedOutputStore(s:Store NearState)(op index:Nat)(m:Memory)(out:UInt32)
    (high low usage packed:UInt64)(length:UInt32):=
  let m1:=writeI64 m (out+16).toNat high
  let t1:=store64Added s op index m out 16 high
  let m2:=writeI64 m1 (out+8).toNat low
  let t2:=store64Added t1 op index m1 out 8 low
  let m3:=writeI64 m2 (out+24).toNat usage
  let t3:=store64Added t2 op index m2 out 24 usage
  let m4:=writeI64 m3 (out+32).toNat packed
  let t4:=store64Added t3 op index m3 out 32 packed
  let m5:=writeI32 m4 (out+40).toNat length
  let t5:=store32Added t4 op index m4 out 40 length
  StateDecodePrefix.outputTagStore t5 op index m5 out

theorem wp_output (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)
    (out scratch:UInt32)(high low usage packed:UInt64)(length:UInt32)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h0:frame.locals[0]?=some (.i32 out))(h2:frame.locals[2]?=some (.i32 scratch))
    (h3:frame.locals[3]?=some (.i64 high))(h5:frame.locals[5]?=some (.i64 low))
    (h7:frame.locals[7]?=some (.i64 usage))(h6:frame.locals[6]?=some (.i64 packed))
    (h1:frame.locals[1]?=some (.i32 length))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hw:memory.wf)(b16:(out+16).toNat+8≤memory.byteSize)(b8:(out+8).toNat+8≤memory.byteSize)
    (b24:(out+24).toNat+8≤memory.byteSize)(b32:(out+32).toNat+8≤memory.byteSize)
    (b40:(out+40).toNat+4≤memory.byteSize)(b0:out.toNat+4≤memory.byteSize)
    (hc:s.host.gas.Credits (28*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (cachedOutputStore s cfg.regularOpCost index memory out high low usage packed length)
      limits stack frame callers code)) rest post):
    WP cfg (fuel+28) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodeBorsh.output++code)))
      (28*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let m1:=writeI64 memory (out+16).toNat high
  let t1:=store64Added s op index memory out 16 high
  have sh1:=writeI64_spec memory (out+16).toNat high hw (by exact b16)
  have mm1:t1.modules[frame.inst]?=some mi:=by rw[modules64];exact hm
  have me1:t1.mems[index]?=some m1:=storeI64_memory _ _ _ _ _ (by rw[paid_mems];exact he)
  have cr1:t1.host.gas.Credits (23*op+rest):=credits64 s op index (23*op+rest) memory out 16 high (hc.mono (by dsimp[op];omega))
  let m2:=writeI64 m1 (out+8).toNat low
  let t2:=store64Added t1 op index m1 out 8 low
  have sh2:=writeI64_spec m1 (out+8).toNat low sh1.1 (by rw[sh1.2.1];exact b8)
  have mm2:t2.modules[frame.inst]?=some mi:=by rw[modules64];exact mm1
  have me2:t2.mems[index]?=some m2:=storeI64_memory _ _ _ _ _ (by rw[paid_mems];exact me1)
  have cr2:t2.host.gas.Credits (18*op+rest):=credits64 t1 op index (18*op+rest) m1 out 8 low (cr1.mono (by omega))
  let m3:=writeI64 m2 (out+24).toNat usage
  let t3:=store64Added t2 op index m2 out 24 usage
  have sh3:=writeI64_spec m2 (out+24).toNat usage sh2.1 (by rw[sh2.2.1];rw[sh1.2.1];exact b24)
  have mm3:t3.modules[frame.inst]?=some mi:=by rw[modules64];exact mm2
  have me3:t3.mems[index]?=some m3:=storeI64_memory _ _ _ _ _ (by rw[paid_mems];exact me2)
  have cr3:t3.host.gas.Credits (13*op+rest):=credits64 t2 op index (13*op+rest) m2 out 24 usage (cr2.mono (by omega))
  let m4:=writeI64 m3 (out+32).toNat packed
  let t4:=store64Added t3 op index m3 out 32 packed
  have sh4:=writeI64_spec m3 (out+32).toNat packed sh3.1 (by rw[sh3.2.1];rw[sh2.2.1];rw[sh1.2.1];exact b32)
  have mm4:t4.modules[frame.inst]?=some mi:=by rw[modules64];exact mm3
  have me4:t4.mems[index]?=some m4:=storeI64_memory _ _ _ _ _ (by rw[paid_mems];exact me3)
  have cr4:t4.host.gas.Credits (8*op+rest):=credits64 t3 op index (8*op+rest) m3 out 32 packed (cr3.mono (by omega))
  let m5:=writeI32 m4 (out+40).toNat length
  let t5:=store32Added t4 op index m4 out 40 length
  have sh5:=writeI32_spec m4 (out+40).toNat length sh4.1 (by rw[sh4.2.1];rw[sh3.2.1];rw[sh2.2.1];rw[sh1.2.1];exact b40)
  have mm5:t5.modules[frame.inst]?=some mi:=by rw[modules32];exact mm4
  have me5:t5.mems[index]?=some m5:=storeI32_memory _ _ _ _ _ (by rw[paid_mems];exact me4)
  have cr5:t5.host.gas.Credits (3*op+rest):=credits32 t4 op index (3*op+rest) m4 out 40 length (cr4.mono (by omega))
  have tag:=StateDecodePrefix.wp_output_tag cfg fuel rest t5 limits stack frame callers code out scratch mi index m5 post
    h0 h2 mm5 hi me5 (by rw[sh5.2.1,sh4.2.1,sh3.2.1,sh2.2.1,sh1.2.1];exact b0) cr5 hn
  have p5:=wp_store32_added cfg (fuel+3) (3*op+rest) t4 limits stack frame callers (StateDecodePrefix.outputTagCode++code) 0 1 out 40 length mi index m4 post h0 h1 mm4 hi me4 (by rw[sh4.2.1];rw[sh3.2.1];rw[sh2.2.1];rw[sh1.2.1];exact b40) (cr4.mono (by omega))
    (by simpa only[Nat.add_zero,Nat.zero_mul,Nat.add_assoc,Nat.reduceAdd,show 3*op+rest=3*cfg.regularOpCost+rest by rfl] using tag)
  have p4:=wp_store64_added cfg (fuel+8) (8*op+rest) t3 limits stack frame callers ([.local_get 0,.i32_const 40,.i32_binop .add,.local_get 1,.store .i32 none {align:=2,offset:=0}]++(StateDecodePrefix.outputTagCode++code)) 0 6 out 32 packed mi index m3 post h0 h6 mm3 hi me3 (by rw[sh3.2.1];rw[sh2.2.1];rw[sh1.2.1];exact b32) (cr3.mono (by omega))
    (by simpa only[Nat.add_zero,Nat.zero_mul,Nat.add_assoc,Nat.reduceAdd,List.cons_append,List.nil_append,show 5*cfg.regularOpCost+(3*op+rest)=8*op+rest by dsimp[op];omega] using p5)
  have p3:=wp_store64_added cfg (fuel+13) (13*op+rest) t2 limits stack frame callers ([.local_get 0,.i32_const 32,.i32_binop .add,.local_get 6,.store .i64 none {align:=3,offset:=0}]++([.local_get 0,.i32_const 40,.i32_binop .add,.local_get 1,.store .i32 none {align:=2,offset:=0}]++(StateDecodePrefix.outputTagCode++code))) 0 7 out 24 usage mi index m2 post h0 h7 mm2 hi me2 (by rw[sh2.2.1];rw[sh1.2.1];exact b24) (cr2.mono (by omega))
    (by simpa only[Nat.add_zero,Nat.zero_mul,Nat.add_assoc,Nat.reduceAdd,List.cons_append,List.nil_append,show 5*cfg.regularOpCost+(8*op+rest)=13*op+rest by dsimp[op];omega] using p4)
  have p2:=wp_store64_added cfg (fuel+18) (18*op+rest) t1 limits stack frame callers ([.local_get 0,.i32_const 24,.i32_binop .add,.local_get 7,.store .i64 none {align:=3,offset:=0}]++([.local_get 0,.i32_const 32,.i32_binop .add,.local_get 6,.store .i64 none {align:=3,offset:=0}]++([.local_get 0,.i32_const 40,.i32_binop .add,.local_get 1,.store .i32 none {align:=2,offset:=0}]++(StateDecodePrefix.outputTagCode++code)))) 0 5 out 8 low mi index m1 post h0 h5 mm1 hi me1 (by rw[sh1.2.1];exact b8) (cr1.mono (by omega))
    (by simpa only[Nat.add_zero,Nat.zero_mul,Nat.add_assoc,Nat.reduceAdd,List.cons_append,List.nil_append,show 5*cfg.regularOpCost+(13*op+rest)=18*op+rest by dsimp[op];omega] using p3)
  have p1:=wp_store64_added cfg (fuel+23) (23*op+rest) s limits stack frame callers ([.local_get 0,.i32_const 8,.i32_binop .add,.local_get 5,.store .i64 none {align:=3,offset:=0}]++([.local_get 0,.i32_const 24,.i32_binop .add,.local_get 7,.store .i64 none {align:=3,offset:=0}]++([.local_get 0,.i32_const 32,.i32_binop .add,.local_get 6,.store .i64 none {align:=3,offset:=0}]++([.local_get 0,.i32_const 40,.i32_binop .add,.local_get 1,.store .i32 none {align:=2,offset:=0}]++(StateDecodePrefix.outputTagCode++code))))) 0 3 out 16 high mi index memory post h0 h3 hm hi he (by exact b16) (hc.mono (by dsimp[op];omega))
    (by simpa only[Nat.add_zero,Nat.zero_mul,Nat.add_assoc,Nat.reduceAdd,List.cons_append,List.nil_append,show 5*cfg.regularOpCost+(18*op+rest)=23*op+rest by dsimp[op];omega] using p2)
  simpa only[WNear.Binary.StateDecodeBorsh.output,StateDecodePrefix.outputTagCode,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 5*cfg.regularOpCost+(23*op+rest)=28*cfg.regularOpCost+rest by dsimp[op];omega] using p1
end WNear.Proofs.StateDecodeBorsh
