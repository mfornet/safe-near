import Proofs.StateDecodePrefixWrapperTailState

namespace WNear.Proofs.StateDecodePrefixWrapper.Tail
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32 readI64
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

def readHighCode:Expr:=[.local_get 2,.i32_const 12,.i32_binop .add,.load .i32 none {align:=2,offset:=0},.local_set 1]
def writeLowCode:Expr:=[.local_get 0,.local_get 3,.store .i64 none {align:=2,offset:=4}]
def writeHighCode:Expr:=[.local_get 0,.i32_const 12,.i32_binop .add,.local_get 1,.store .i32 none {align:=2,offset:=0}]
def zeroCode:Expr:=[.i32_const 0,.local_set 1]
def tagCode:Expr:=[.local_get 0,.local_get 1,.store .i32 none {align:=2,offset:=0}]
def highFrame(frame:CallFrame)(value:UInt32):={frame with locals:=frame.locals.set! 1 (.i32 value)}
def lowStore(s:Store NearState)(op index:Nat)(memory:Memory)(out:UInt32)(value:UInt64):=storeI64 (paid s op 3) index (out.toNat+4) memory value
def highStore(s:Store NearState)(op index:Nat)(memory:Memory)(out value:UInt32):=storeI32 (paid s op 5) index (out+12).toNat memory value
def tagStore(s:Store NearState)(op index:Nat)(memory:Memory)(out value:UInt32):=storeI32 (paid s op 3) index out.toNat memory value

theorem wp_readHigh (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(out pointer high:UInt32)(low:UInt64)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (_h0:frame.locals[0]?=some (.i32 out))(_h1:frame.locals[1]?=some (.i32 high))
    (h2:frame.locals[2]?=some (.i32 pointer))(_h3:frame.locals[3]?=some (.i64 low))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hb:(pointer+12).toNat+4≤memory.byteSize)(hc:s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits stack (highFrame frame (readI32 memory (pointer+12).toNat)) callers code)) rest post):
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers (readHighCode++code))) (5*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have p4:=wp_local_set cfg (fuel+0) (rest) (paid s op 4) limits stack frame callers (code) 1 (.i32 (readI32 memory (pointer+12).toNat)) post (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) hn
  have mm3:(paid s op 3).modules[frame.inst]?=some mi:=by rw[modules_paid];exact hm
  have me3:(paid s op 3).mems[index]?=some memory:=by rw[mems_paid];exact he
  have p3:=wp_i32_load cfg (fuel+1) (op+(rest)) (paid s op 3) limits stack frame callers (.local_set 1::code) {align:=2,offset:=0} (pointer+12) mi index memory post mm3 hi me3 (by dsimp;exact hb) (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) p4
  have p2:=wp_i32_add cfg (fuel+2) (op+(op+(rest))) (paid s op 2) limits stack frame callers (.load .i32 none {align:=2,offset:=0}::.local_set 1::code) pointer 12 post (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) p3
  have p1:=wp_i32_const cfg (fuel+3) (op+(op+(op+(rest)))) (paid s op 1) limits (stack.push (.i32 pointer)) frame callers (.i32_binop .add::.load .i32 none {align:=2,offset:=0}::.local_set 1::code) 12 post (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) p2
  have p0:=wp_local_get cfg (fuel+4) (op+(op+(op+(op+(rest))))) s limits stack frame callers (.i32_const 12::.i32_binop .add::.load .i32 none {align:=2,offset:=0}::.local_set 1::code) 2 (.i32 pointer) post h2 (hc.mono (by dsimp[op];omega)) p1
  simpa only[readHighCode,List.cons_append,List.nil_append,Nat.add_zero,op,show fuel+4+1=fuel+5 by omega,show op+(op+(op+(op+(op+(rest)))))=5*cfg.regularOpCost+rest by dsimp[op];omega] using p0

theorem wp_writeLow (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(out pointer high:UInt32)(low:UInt64)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h0:frame.locals[0]?=some (.i32 out))(_h1:frame.locals[1]?=some (.i32 high))
    (_h2:frame.locals[2]?=some (.i32 pointer))(h3:frame.locals[3]?=some (.i64 low))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hb:out.toNat+12≤memory.byteSize)(hc:s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (lowStore s cfg.regularOpCost index memory out low) limits stack frame callers code)) rest post):
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers (writeLowCode++code))) (3*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have mm2:(paid s op 2).modules[frame.inst]?=some mi:=by rw[modules_paid];exact hm
  have me2:(paid s op 2).mems[index]?=some memory:=by rw[mems_paid];exact he
  have p2:=wp_i64_store cfg (fuel+0) (rest) (paid s op 2) limits stack frame callers (code) {align:=2,offset:=4} out low mi index memory post mm2 hi me2 (by dsimp;exact hb) (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) hn
  have p1:=wp_local_get cfg (fuel+1) (op+(rest)) (paid s op 1) limits (stack.push (.i32 out)) frame callers (.store .i64 none {align:=2,offset:=4}::code) 3 (.i64 low) post h3 (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) p2
  have p0:=wp_local_get cfg (fuel+2) (op+(op+(rest))) s limits stack frame callers (.local_get 3::.store .i64 none {align:=2,offset:=4}::code) 0 (.i32 out) post h0 (hc.mono (by dsimp[op];omega)) p1
  simpa only[writeLowCode,List.cons_append,List.nil_append,Nat.add_zero,op,show fuel+2+1=fuel+3 by omega,show op+(op+(op+(rest)))=3*cfg.regularOpCost+rest by dsimp[op];omega] using p0

theorem wp_writeHigh (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(out pointer high:UInt32)(low:UInt64)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h0:frame.locals[0]?=some (.i32 out))(h1:frame.locals[1]?=some (.i32 high))
    (_h2:frame.locals[2]?=some (.i32 pointer))(_h3:frame.locals[3]?=some (.i64 low))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hb:(out+12).toNat+4≤memory.byteSize)(hc:s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (highStore s cfg.regularOpCost index memory out high) limits stack frame callers code)) rest post):
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers (writeHighCode++code))) (5*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have mm4:(paid s op 4).modules[frame.inst]?=some mi:=by rw[modules_paid];exact hm
  have me4:(paid s op 4).mems[index]?=some memory:=by rw[mems_paid];exact he
  have p4:=wp_i32_store cfg (fuel+0) (rest) (paid s op 4) limits stack frame callers (code) {align:=2,offset:=0} (out+12) high mi index memory post mm4 hi me4 (by dsimp;exact hb) (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) hn
  have p3:=wp_local_get cfg (fuel+1) (op+(rest)) (paid s op 3) limits (stack.push (.i32 (out+12))) frame callers (.store .i32 none {align:=2,offset:=0}::code) 1 (.i32 high) post h1 (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) p4
  have p2:=wp_i32_add cfg (fuel+2) (op+(op+(rest))) (paid s op 2) limits stack frame callers (.local_get 1::.store .i32 none {align:=2,offset:=0}::code) out 12 post (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) p3
  have p1:=wp_i32_const cfg (fuel+3) (op+(op+(op+(rest)))) (paid s op 1) limits (stack.push (.i32 out)) frame callers (.i32_binop .add::.local_get 1::.store .i32 none {align:=2,offset:=0}::code) 12 post (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) p2
  have p0:=wp_local_get cfg (fuel+4) (op+(op+(op+(op+(rest))))) s limits stack frame callers (.i32_const 12::.i32_binop .add::.local_get 1::.store .i32 none {align:=2,offset:=0}::code) 0 (.i32 out) post h0 (hc.mono (by dsimp[op];omega)) p1
  simpa only[writeHighCode,List.cons_append,List.nil_append,Nat.add_zero,op,show fuel+4+1=fuel+5 by omega,show op+(op+(op+(op+(op+(rest)))))=5*cfg.regularOpCost+rest by dsimp[op];omega] using p0

theorem wp_tag (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(out pointer high:UInt32)(low:UInt64)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h0:frame.locals[0]?=some (.i32 out))(h1:frame.locals[1]?=some (.i32 high))
    (_h2:frame.locals[2]?=some (.i32 pointer))(_h3:frame.locals[3]?=some (.i64 low))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hb:out.toNat+4≤memory.byteSize)(hc:s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (tagStore s cfg.regularOpCost index memory out high) limits stack frame callers code)) rest post):
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers (tagCode++code))) (3*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have mm2:(paid s op 2).modules[frame.inst]?=some mi:=by rw[modules_paid];exact hm
  have me2:(paid s op 2).mems[index]?=some memory:=by rw[mems_paid];exact he
  have p2:=wp_i32_store cfg (fuel+0) (rest) (paid s op 2) limits stack frame callers (code) {align:=2,offset:=0} out high mi index memory post mm2 hi me2 (by dsimp;exact hb) (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) hn
  have p1:=wp_local_get cfg (fuel+1) (op+(rest)) (paid s op 1) limits (stack.push (.i32 out)) frame callers (.store .i32 none {align:=2,offset:=0}::code) 1 (.i32 high) post h1 (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) p2
  have p0:=wp_local_get cfg (fuel+2) (op+(op+(rest))) s limits stack frame callers (.local_get 1::.store .i32 none {align:=2,offset:=0}::code) 0 (.i32 out) post h0 (hc.mono (by dsimp[op];omega)) p1
  simpa only[tagCode,List.cons_append,List.nil_append,Nat.add_zero,op,show fuel+2+1=fuel+3 by omega,show op+(op+(op+(rest)))=3*cfg.regularOpCost+rest by dsimp[op];omega] using p0

theorem wp_zero(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)(stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(post:Post)
    (hc:s.host.gas.Credits (2*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 2) limits stack (highFrame frame 0) callers code)) rest post):
    WP cfg (fuel+2) (.next (atCode s limits stack frame callers (zeroCode++code))) (2*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have set:=wp_local_set cfg fuel rest (paid s op 1) limits stack frame callers code 1 (.i32 0) post
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) hn
  have constant:=wp_i32_const cfg (fuel+1) (op+rest) s limits stack frame callers (.local_set 1::code) 0 post (hc.mono (by dsimp[op];omega)) set
  simpa only[zeroCode,List.cons_append,List.nil_append,show cfg.regularOpCost+(op+rest)=2*cfg.regularOpCost+rest by dsimp[op];omega] using constant
end WNear.Proofs.StateDecodePrefixWrapper.Tail
