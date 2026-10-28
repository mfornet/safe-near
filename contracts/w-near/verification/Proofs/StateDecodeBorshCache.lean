import Binary.StateDecodeBorsh
import Proofs.StateDecodeScalarCache

/-! Actual425 caches its scalar words before later result records are reused. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI64

def cachePrefixFrame(frame:CallFrame)(memory:Memory)(scratch:UInt32):=
  StateDecodeScalar.loaded64Frame frame 3 (readI64 memory (scratch.toNat+60))
def cacheNarrowFrame(frame:CallFrame)(memory:Memory)(scratch:UInt32):=
  StateDecodeScalar.loaded64Frame frame 7 (readI64 memory (scratch.toNat+84))

theorem wp_cache_prefix (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(scratch:UInt32)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h2:frame.locals[2]?=some (.i32 scratch))(hm:s.modules[frame.inst]?=some mi)
    (hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)(hb:scratch.toNat+68≤memory.byteSize)
    (hc:s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits stack (cachePrefixFrame frame memory scratch) callers code)) rest post):
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodeBorsh.cachePrefix++code))) (3*cfg.regularOpCost+rest) post:=by
  exact StateDecodeScalar.wp_load64_local cfg fuel rest s limits stack frame callers code 2 3 {align:=2,offset:=60} scratch mi index memory post h2 hm hi he hb hc hn

theorem wp_cache_narrow (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(scratch:UInt32)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h2:frame.locals[2]?=some (.i32 scratch))(hm:s.modules[frame.inst]?=some mi)
    (hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)(hb:scratch.toNat+92≤memory.byteSize)
    (hc:s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits stack (cacheNarrowFrame frame memory scratch) callers code)) rest post):
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodeBorsh.cacheNarrow++code))) (3*cfg.regularOpCost+rest) post:=by
  exact StateDecodeScalar.wp_load64_local cfg fuel rest s limits stack frame callers code 2 7 {align:=2,offset:=84} scratch mi index memory post h2 hm hi he hb hc hn
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

def cacheWideFirstFrame(frame:CallFrame)(memory:Memory)(scratch:UInt32):=
  StateDecodeScalar.loaded64Frame frame 3 (readI64 memory ((scratch+32+12).toNat))
def cacheWideFrame(frame:CallFrame)(memory:Memory)(scratch:UInt32):=
  StateDecodeScalar.loaded64Frame (cacheWideFirstFrame frame memory scratch) 5 (readI64 memory (scratch.toNat+36))

theorem wp_cache_wide (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(scratch:UInt32)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h2:frame.locals[2]?=some (.i32 scratch))(hm:s.modules[frame.inst]?=some mi)
    (hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hbHigh:(scratch+32+12).toNat+8≤memory.byteSize)(hbLow:scratch.toNat+44≤memory.byteSize)
    (hc:s.host.gas.Credits (10*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 10) limits stack (cacheWideFrame frame memory scratch) callers code)) rest post):
    WP cfg (fuel+10) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodeBorsh.cacheWide++code))) (10*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let f:=cacheWideFirstFrame frame memory scratch
  let suffix:Expr:=[.local_get 2,.load .i64 none {align:=2,offset:=36},.local_set 5]++code
  have low:=StateDecodeScalar.wp_load64_local cfg fuel rest (paid s op 7) limits stack f callers code 2 5 {align:=2,offset:=36} scratch mi index memory post
    (by simp[f,cacheWideFirstFrame,StateDecodeScalar.loaded64Frame,h2]) (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) hbLow
    (paid_credits s op 7 _ (hc.mono (by dsimp[op];omega)))
    (by simpa only[paid,op,f,cacheWideFrame] using hn)
  have high:=StateDecodeScalar.wp_load64_set cfg (fuel+3) (3*op+rest) (paid s op 5) limits stack frame callers suffix {align:=2,offset:=0}
    (scratch+32+12) 3 mi index memory post (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he)
    (by simpa only[Nat.add_zero] using hbHigh) (paid_credits s op 5 _ (hc.mono (by dsimp[op];omega)))
    (by simpa only[f,cacheWideFirstFrame,StateDecodeScalar.loaded64Frame,paid,op,suffix,Nat.add_zero,List.cons_append,List.nil_append] using low)
  have add12:=wp_i32_add cfg (fuel+5) (2*op+(3*op+rest)) (paid s op 4) limits stack frame callers
    (.load .i64 none {align:=2,offset:=0}::.local_set 3::suffix) (scratch+32) 12 post
    (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op,Nat.add_assoc,Nat.reduceAdd] using high)
  have con12:=wp_i32_const cfg (fuel+6) (op+(2*op+(3*op+rest))) (paid s op 3) limits (stack.push (.i32 (scratch+32))) frame callers
    (.i32_binop .add::.load .i64 none {align:=2,offset:=0}::.local_set 3::suffix) 12 post
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) add12
  have add32:=wp_i32_add cfg (fuel+7) (op+(op+(2*op+(3*op+rest)))) (paid s op 2) limits stack frame callers
    (.i32_const 12::.i32_binop .add::.load .i64 none {align:=2,offset:=0}::.local_set 3::suffix) scratch 32 post
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) con12
  have con32:=wp_i32_const cfg (fuel+8) (op+(op+(op+(2*op+(3*op+rest))))) (paid s op 1) limits (stack.push (.i32 scratch)) frame callers
    (.i32_binop .add::.i32_const 12::.i32_binop .add::.load .i64 none {align:=2,offset:=0}::.local_set 3::suffix) 32 post
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) add32
  have get:=wp_local_get cfg (fuel+9) (op+(op+(op+(op+(2*op+(3*op+rest)))))) s limits stack frame callers
    (.i32_const 32::.i32_binop .add::.i32_const 12::.i32_binop .add::.load .i64 none {align:=2,offset:=0}::.local_set 3::suffix) 2 (.i32 scratch) post h2
    (hc.mono (by dsimp[op];omega)) con32
  simpa only[WNear.Binary.StateDecodeBorsh.cacheWide,suffix,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(op+(op+(op+(op+(2*op+(3*op+rest))))))=10*cfg.regularOpCost+rest by dsimp[op];omega] using get

end WNear.Proofs.StateDecodeBorsh
