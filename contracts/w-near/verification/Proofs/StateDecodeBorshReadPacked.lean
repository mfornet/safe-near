import Proofs.StateDecodeBorshReadPhases
import NearVM.MeteredPackedI64Rules
import NearVM.MeteredWordRules

/-! Actual161 preserves the cached i64, shifts it by32, and executes the
real packed i64.store32 opcode. Exactly four destination bytes are written. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32 readI64 writeI32 writeI64
set_option maxHeartbeats 1000000
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

def upperStore(s:Store NearState)(op index:Nat)(m:Memory)(out:UInt32)(packed:UInt64):=
  storeI32 (paid s op 5) index (out.toNat+16) m (UInt32.ofNat ((packed>>>32).toNat))

theorem wp_packed_store(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(out:UInt32)(packed:UInt64)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h0:frame.locals[3]?=some (.i32 out))(h3:frame.locals[4]?=some (.i64 packed))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hb:(out.toNat+16)+4≤memory.byteSize)(hc:s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (upperStore s cfg.regularOpCost index memory out packed) limits stack frame callers code)) rest post):
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers ([.local_get 3,.local_get 4,.i64_const 32,.i64_binop .shr_u,.store .i64 (some 32) {align:=2,offset:=16}]++code))) (5*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have store:=wp_i64_store32 cfg fuel rest (paid s op 4) limits stack frame callers code {align:=2,offset:=16} out (packed>>>32) mi index memory post
    (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) (by simpa only[Nat.add_zero] using hb)
    (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) hn
  have shift:=wp_i64_binop_ok cfg (fuel+1) (op+rest) (paid s op 3) limits (stack.push (.i32 out)) frame callers
    (.store .i64 (some 32) {align:=2,offset:=16}::code) .shr_u packed 32 (packed>>>32) post
    (by simp only[Numeric.ibinop64,show (32:UInt64)%64=32 by decide])
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) store
  have constant:=wp_i64_const cfg (fuel+2) (op+(op+rest)) (paid s op 2) limits ((stack.push (.i32 out)).push (.i64 packed)) frame callers
    (.i64_binop .shr_u::.store .i64 (some 32) {align:=2,offset:=16}::code) 32 post
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) shift
  have value:=wp_local_get cfg (fuel+3) (op+(op+(op+rest))) (paid s op 1) limits (stack.push (.i32 out)) frame callers
    (.i64_const 32::.i64_binop .shr_u::.store .i64 (some 32) {align:=2,offset:=16}::code) 4 (.i64 packed) post h3
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) constant
  have get:=wp_local_get cfg (fuel+4) (op+(op+(op+(op+rest)))) s limits stack frame callers
    (.local_get 4::.i64_const 32::.i64_binop .shr_u::.store .i64 (some 32) {align:=2,offset:=16}::code) 3 (.i32 out) post h0
    (hc.mono (by dsimp[op];omega)) value
  simpa only[List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(op+(op+(op+(op+rest))))=5*cfg.regularOpCost+rest by dsimp[op];omega] using get
end WNear.Proofs.StateDecodeBorshRead
