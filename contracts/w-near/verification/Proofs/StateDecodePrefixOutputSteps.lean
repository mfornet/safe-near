import Proofs.StateDecodeScalarOutput
import Binary.StateDecodePrefix
import NearVM.MeteredI32MemoryRules

/-! Sequential output writes of316. Each capsule reads its current input memory. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32 readI64
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

def outputHighCode:Expr:=[.local_get 0,.i32_const 12,.i32_binop .add,.local_get 2,.load .i32 none {align:=2,offset:=56},.store .i32 none {align:=2,offset:=0}]
def outputLowCode:Expr:=[.local_get 0,.local_get 2,.load .i64 none {align:=3,offset:=48},.store .i64 none {align:=2,offset:=4}]
def outputTagCode:Expr:=[.local_get 0,.i32_const 0,.store .i32 none {align:=2,offset:=0}]
def outputHighStore(s:Store NearState)(op index:Nat)(memory:Memory)(out scratch:UInt32):=
  storeI32 (paid s op 6) index (out+12).toNat memory (readI32 memory (scratch.toNat+56))
def outputLowStore(s:Store NearState)(op index:Nat)(memory:Memory)(out scratch:UInt32):=
  storeI64 (paid s op 4) index (out.toNat+4) memory (readI64 memory (scratch.toNat+48))
def outputTagStore(s:Store NearState)(op index:Nat)(memory:Memory)(out:UInt32):=
  storeI32 (paid s op 3) index out.toNat memory 0

theorem wp_output_high (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(out scratch:UInt32)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h0:frame.locals[0]?=some (.i32 out))(h2:frame.locals[2]?=some (.i32 scratch))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hb:(out+12).toNat+4≤memory.byteSize)(hs:scratch.toNat+60≤memory.byteSize)
    (hc:s.host.gas.Credits (6*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (outputHighStore s cfg.regularOpCost index memory out scratch) limits stack frame callers code)) rest post):
    WP cfg (fuel+6) (.next (atCode s limits stack frame callers (outputHighCode++code))) (6*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have mm5:(paid s op 5).modules[frame.inst]?=some mi:=by rw[modules_paid];exact hm
  have me5:(paid s op 5).mems[index]?=some memory:=by rw[mems_paid];exact he
  have p5:=wp_i32_store cfg (fuel+0) (rest) (paid s op 5) limits stack frame callers (code) {align:=2,offset:=0} (out+12) (readI32 memory (scratch.toNat+56)) mi index memory post mm5 hi me5 (by dsimp;omega) (paid_credits s op 5 _ (hc.mono (by dsimp[op];omega))) hn
  have mm4:(paid s op 4).modules[frame.inst]?=some mi:=by rw[modules_paid];exact hm
  have me4:(paid s op 4).mems[index]?=some memory:=by rw[mems_paid];exact he
  have p4:=wp_i32_load cfg (fuel+1) (op+(rest)) (paid s op 4) limits (stack.push (.i32 (out+12))) frame callers (.store .i32 none {align:=2,offset:=0}::code) {align:=2,offset:=56} scratch mi index memory post mm4 hi me4 (by dsimp;omega) (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) p5
  have p3:=wp_local_get cfg (fuel+2) (op+(op+(rest))) (paid s op 3) limits (stack.push (.i32 (out+12))) frame callers (.load .i32 none {align:=2,offset:=56}::.store .i32 none {align:=2,offset:=0}::code) 2 (.i32 scratch) post h2 (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) p4
  have p2:=wp_i32_add cfg (fuel+3) (op+(op+(op+(rest)))) (paid s op 2) limits stack frame callers (.local_get 2::.load .i32 none {align:=2,offset:=56}::.store .i32 none {align:=2,offset:=0}::code) out 12 post (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) p3
  have p1:=wp_i32_const cfg (fuel+4) (op+(op+(op+(op+(rest))))) (paid s op 1) limits (stack.push (.i32 out)) frame callers (.i32_binop .add::.local_get 2::.load .i32 none {align:=2,offset:=56}::.store .i32 none {align:=2,offset:=0}::code) 12 post (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) p2
  have p0:=wp_local_get cfg (fuel+5) (op+(op+(op+(op+(op+(rest)))))) s limits stack frame callers (.i32_const 12::.i32_binop .add::.local_get 2::.load .i32 none {align:=2,offset:=56}::.store .i32 none {align:=2,offset:=0}::code) 0 (.i32 out) post h0 (hc.mono (by dsimp[op];omega)) p1
  simpa only[outputHighCode,List.cons_append,List.nil_append,Nat.add_zero,op,show fuel+5+1=fuel+6 by omega,show op+(op+(op+(op+(op+(op+(rest))))))=6*cfg.regularOpCost+rest by dsimp[op];omega] using p0

theorem wp_output_low (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(out scratch:UInt32)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h0:frame.locals[0]?=some (.i32 out))(h2:frame.locals[2]?=some (.i32 scratch))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hb:out.toNat+12≤memory.byteSize)(hs:scratch.toNat+56≤memory.byteSize)
    (hc:s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (outputLowStore s cfg.regularOpCost index memory out scratch) limits stack frame callers code)) rest post):
    WP cfg (fuel+4) (.next (atCode s limits stack frame callers (outputLowCode++code))) (4*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have mm3:(paid s op 3).modules[frame.inst]?=some mi:=by rw[modules_paid];exact hm
  have me3:(paid s op 3).mems[index]?=some memory:=by rw[mems_paid];exact he
  have p3:=wp_i64_store cfg (fuel+0) (rest) (paid s op 3) limits stack frame callers (code) {align:=2,offset:=4} out (readI64 memory (scratch.toNat+48)) mi index memory post mm3 hi me3 (by dsimp;omega) (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) hn
  have mm2:(paid s op 2).modules[frame.inst]?=some mi:=by rw[modules_paid];exact hm
  have me2:(paid s op 2).mems[index]?=some memory:=by rw[mems_paid];exact he
  have p2:=wp_i64_load cfg (fuel+1) (op+(rest)) (paid s op 2) limits (stack.push (.i32 out)) frame callers (.store .i64 none {align:=2,offset:=4}::code) {align:=3,offset:=48} scratch mi index memory post mm2 hi me2 (by dsimp;omega) (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) p3
  have p1:=wp_local_get cfg (fuel+2) (op+(op+(rest))) (paid s op 1) limits (stack.push (.i32 out)) frame callers (.load .i64 none {align:=3,offset:=48}::.store .i64 none {align:=2,offset:=4}::code) 2 (.i32 scratch) post h2 (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) p2
  have p0:=wp_local_get cfg (fuel+3) (op+(op+(op+(rest)))) s limits stack frame callers (.local_get 2::.load .i64 none {align:=3,offset:=48}::.store .i64 none {align:=2,offset:=4}::code) 0 (.i32 out) post h0 (hc.mono (by dsimp[op];omega)) p1
  simpa only[outputLowCode,List.cons_append,List.nil_append,Nat.add_zero,op,show fuel+3+1=fuel+4 by omega,show op+(op+(op+(op+(rest))))=4*cfg.regularOpCost+rest by dsimp[op];omega] using p0

theorem wp_output_tag (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(out scratch:UInt32)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h0:frame.locals[0]?=some (.i32 out))(_h2:frame.locals[2]?=some (.i32 scratch))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hb:out.toNat+4≤memory.byteSize)
    (hc:s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (outputTagStore s cfg.regularOpCost index memory out) limits stack frame callers code)) rest post):
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers (outputTagCode++code))) (3*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have mm2:(paid s op 2).modules[frame.inst]?=some mi:=by rw[modules_paid];exact hm
  have me2:(paid s op 2).mems[index]?=some memory:=by rw[mems_paid];exact he
  have p2:=wp_i32_store cfg (fuel+0) (rest) (paid s op 2) limits stack frame callers (code) {align:=2,offset:=0} out 0 mi index memory post mm2 hi me2 (by dsimp;omega) (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) hn
  have p1:=wp_i32_const cfg (fuel+1) (op+(rest)) (paid s op 1) limits (stack.push (.i32 out)) frame callers (.store .i32 none {align:=2,offset:=0}::code) 0 post (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) p2
  have p0:=wp_local_get cfg (fuel+2) (op+(op+(rest))) s limits stack frame callers (.i32_const 0::.store .i32 none {align:=2,offset:=0}::code) 0 (.i32 out) post h0 (hc.mono (by dsimp[op];omega)) p1
  simpa only[outputTagCode,List.cons_append,List.nil_append,Nat.add_zero,op,show fuel+2+1=fuel+3 by omega,show op+(op+(op+(rest)))=3*cfg.regularOpCost+rest by dsimp[op];omega] using p0
end WNear.Proofs.StateDecodePrefix
