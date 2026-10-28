import Proofs.StateDecodeBorshReadPhases
import Proofs.StateDecodeScalarCache
import NearVM.MeteredLoopRules
import NearVM.MeteredNumericRules

/-! Real161 local snapshots and accepted tag control. The packed i64 and tag
are cached before either36-byte copy or caller-output write. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32 readI64
def cacheValueCode:Expr:=[.local_get 3,.load .i64 none {align:=2,offset:=100},.local_set 4]
def cacheTagCode:Expr:=[.local_get 3,.load .i32 none {align:=2,offset:=96},.local_set 1]
def guardCode:Expr:=[.local_get 1,.i32_const 1,.i32_relop .eq,.br_if 0]
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

def tagSnapshotFrame(frame:CallFrame)(value:UInt32):={frame with locals:=frame.locals.set! 1 (.i32 value)}
def loadedTagFrame(frame:CallFrame)(memory:Memory)(r:UInt32):=
  tagSnapshotFrame (StateDecodeScalar.loaded64Frame frame 4 (readI64 memory (r.toNat+100))) (readI32 memory (r.toNat+96))
theorem wp_tag_cache(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(r:UInt32)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h2:frame.locals[3]?=some (.i32 r))(hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hb:r.toNat+100≤memory.byteSize)(hc:s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits stack (tagSnapshotFrame frame (readI32 memory (r.toNat+96))) callers code)) rest post):
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers (cacheTagCode++code))) (3*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have set:=wp_local_set cfg fuel rest (paid s op 2) limits stack frame callers code 1 (.i32 (readI32 memory (r.toNat+96))) post
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) hn
  have load:=wp_i32_load cfg (fuel+1) (op+rest) (paid s op 1) limits stack frame callers (.local_set 1::code) {align:=2,offset:=96} r mi index memory post
    (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) (by dsimp;omega)
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) set
  have get:=wp_local_get cfg (fuel+2) (op+(op+rest)) s limits stack frame callers (.load .i32 none {align:=2,offset:=96}::.local_set 1::code) 3 (.i32 r) post h2
    (hc.mono (by dsimp[op];omega)) load
  simpa only[cacheTagCode,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(op+(op+rest))=3*cfg.regularOpCost+rest by dsimp[op];omega] using get

theorem wp_cache(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(r:UInt32)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h2:frame.locals[3]?=some (.i32 r))(hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hb:r.toNat+108≤memory.byteSize)(hc:s.host.gas.Credits (6*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 6) limits stack (loadedTagFrame frame memory r) callers code)) rest post):
    WP cfg (fuel+6) (.next (atCode s limits stack frame callers (cacheValueCode++cacheTagCode++code))) (6*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let f:=StateDecodeScalar.loaded64Frame frame 4 (readI64 memory (r.toNat+100))
  have tag:=wp_tag_cache cfg fuel rest (paid s op 3) limits stack f callers code r mi index memory post
    (by simp[f,StateDecodeScalar.loaded64Frame,h2])
    (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) (by omega)
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega)))
    (by simpa only[loadedTagFrame,f,paid,op] using hn)
  have value:=StateDecodeScalar.wp_load64_local cfg (fuel+3) (3*op+rest) s limits stack frame callers (cacheTagCode++code)
    3 4 {align:=2,offset:=100} r mi index memory post h2 hm hi he (by dsimp;omega)
    (hc.mono (by dsimp[op];omega)) tag
  simpa only[cacheValueCode,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 3*cfg.regularOpCost+(3*op+rest)=6*cfg.regularOpCost+rest by dsimp[op];omega] using value

theorem wp_accepted_guard(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(tag:UInt32)(post:Post)
    (h4:frame.locals[1]?=some (.i32 tag))(ht:tag≠1)(hc:s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits stack frame callers code)) rest post):
    WP cfg (fuel+4) (.next (atCode s limits stack frame callers (guardCode++code))) (4*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have hz:Numeric.bool (Numeric.irelop32 .eq tag 1)=0:=by simp[Numeric.bool,Numeric.irelop32,ht]
  have branch:=wp_br_if_zero cfg fuel rest (paid s op 3) limits stack frame callers code 0 post
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) hn
  have eq:=wp_i32_relop cfg (fuel+1) (op+rest) (paid s op 2) limits stack frame callers (.br_if 0::code) .eq tag 1 post
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) (by simpa only[hz,paid,op] using branch)
  have constant:=wp_i32_const cfg (fuel+2) (op+(op+rest)) (paid s op 1) limits (stack.push (.i32 tag)) frame callers
    (.i32_relop .eq::.br_if 0::code) 1 post (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) eq
  have get:=wp_local_get cfg (fuel+3) (op+(op+(op+rest))) s limits stack frame callers
    (.i32_const 1::.i32_relop .eq::.br_if 0::code) 1 (.i32 tag) post h4 (hc.mono (by dsimp[op];omega)) constant
  simpa only[guardCode,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(op+(op+(op+rest)))=4*cfg.regularOpCost+rest by dsimp[op];omega] using get
end WNear.Proofs.StateDecodeBorshRead
