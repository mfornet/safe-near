import Proofs.StateDecodeBorshWrapperCode
import NearVM.MeteredPackedI64Rules
import NearVM.MeteredWordRules

/-! Actual162 preserves the cached i64, shifts it by32, and executes the
real packed i64.store32 opcode. Exactly four destination bytes are written. -/
namespace WNear.Proofs.StateDecodeBorshWrapper
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

def packedStore(s:Store NearState)(op index:Nat)(m:Memory)(out:UInt32)(packed:UInt64):=
  storeI32 (paid s op 7) index (out+8).toNat m (UInt32.ofNat ((packed>>>32).toNat))

theorem wp_packed_store(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(out:UInt32)(packed:UInt64)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h0:frame.locals[0]?=some (.i32 out))(h3:frame.locals[3]?=some (.i64 packed))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hb:(out+8).toNat+4≤memory.byteSize)(hc:s.host.gas.Credits (7*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (packedStore s cfg.regularOpCost index memory out packed) limits stack frame callers code)) rest post):
    WP cfg (fuel+7) (.next (atCode s limits stack frame callers (packedStoreCode++code))) (7*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have store:=wp_i64_store32 cfg fuel rest (paid s op 6) limits stack frame callers code {align:=2,offset:=0} (out+8) (packed>>>32) mi index memory post
    (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) (by simpa only[Nat.add_zero] using hb)
    (paid_credits s op 6 _ (hc.mono (by dsimp[op];omega))) hn
  have shift:=wp_i64_binop_ok cfg (fuel+1) (op+rest) (paid s op 5) limits (stack.push (.i32 (out+8))) frame callers
    (.store .i64 (some 32) {align:=2,offset:=0}::code) .shr_u packed 32 (packed>>>32) post
    (by simp only[Numeric.ibinop64,show (32:UInt64)%64=32 by decide])
    (paid_credits s op 5 _ (hc.mono (by dsimp[op];omega))) store
  have constant:=wp_i64_const cfg (fuel+2) (op+(op+rest)) (paid s op 4) limits ((stack.push (.i32 (out+8))).push (.i64 packed)) frame callers
    (.i64_binop .shr_u::.store .i64 (some 32) {align:=2,offset:=0}::code) 32 post
    (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) shift
  have value:=wp_local_get cfg (fuel+3) (op+(op+(op+rest))) (paid s op 3) limits (stack.push (.i32 (out+8))) frame callers
    (.i64_const 32::.i64_binop .shr_u::.store .i64 (some 32) {align:=2,offset:=0}::code) 3 (.i64 packed) post h3
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) constant
  have add:=wp_i32_add cfg (fuel+4) (op+(op+(op+(op+rest)))) (paid s op 2) limits stack frame callers
    (.local_get 3::.i64_const 32::.i64_binop .shr_u::.store .i64 (some 32) {align:=2,offset:=0}::code) out 8 post
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) value
  have offset:=wp_i32_const cfg (fuel+5) (op+(op+(op+(op+(op+rest))))) (paid s op 1) limits (stack.push (.i32 out)) frame callers
    (.i32_binop .add::.local_get 3::.i64_const 32::.i64_binop .shr_u::.store .i64 (some 32) {align:=2,offset:=0}::code) 8 post
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) add
  have get:=wp_local_get cfg (fuel+6) (op+(op+(op+(op+(op+(op+rest)))))) s limits stack frame callers
    (.i32_const 8::.i32_binop .add::.local_get 3::.i64_const 32::.i64_binop .shr_u::.store .i64 (some 32) {align:=2,offset:=0}::code) 0 (.i32 out) post h0
    (hc.mono (by dsimp[op];omega)) offset
  simpa only[packedStoreCode,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(op+(op+(op+(op+(op+(op+rest))))))=7*cfg.regularOpCost+rest by dsimp[op];omega] using get
end WNear.Proofs.StateDecodeBorshWrapper
