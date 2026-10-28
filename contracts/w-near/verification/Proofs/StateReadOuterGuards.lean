import Proofs.StateReadOuterArguments
import NearVM.MeteredLoopRules
import NearVM.MeteredNumericRules

/-! Real161 accepted exhausted-input branch, reading the CURRENT descriptor.
The caller supplies its pure readback theorem, not an execution outcome. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

theorem wp_presence(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code rejected:Expr)(r:UInt32)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h1:frame.locals[1]?=some (.i32 r))(hm:s.modules[frame.inst]?=some mi)
    (hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hb:r.toNat+8+4≤memory.byteSize)(hz:readI32 memory (r.toNat+8)≠0)
    (hc:s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits stack frame callers code)) rest post):
    WP cfg (fuel+4) (.next (atCode s limits stack frame callers
      (.block .empty ([.local_get 1,.load .i32 none {align:=2,offset:=8},.br_if 0]++rejected)::code)))
      (3*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let bf:=emptyBlockFrame frame stack.size code
  have br:=wp_br_if_block_nonzero cfg fuel rest (paid s op 2) limits stack frame callers code rejected
    (readI32 memory (r.toNat+8)) post hz
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) hn
  have load:=wp_i32_load cfg (fuel+1) (op+rest) (paid s op 1) limits stack bf callers
    (.br_if 0::rejected) {align:=2,offset:=8} r mi index memory post
    (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) hb
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) br
  have get:=wp_local_get cfg (fuel+2) (op+(op+rest)) s limits stack bf callers
    (.load .i32 none {align:=2,offset:=8}::.br_if 0::rejected) 1 (.i32 r) post h1
    (hc.mono (by dsimp[op];omega)) load
  have inside:WP cfg (fuel+3) (.next (atCode s limits stack bf callers
      ([.local_get 1,.load .i32 none {align:=2,offset:=8},.br_if 0]++rejected)))
      (3*cfg.regularOpCost+rest) post:=by
    simpa only[List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
      show cfg.regularOpCost+(op+(op+rest))=3*cfg.regularOpCost+rest by dsimp[op];omega] using get
  simpa only[Nat.add_assoc,Nat.reduceAdd] using wp_block_empty cfg (fuel+3) _ s limits stack frame callers _ code post hc inside


def acceptedGuardCode:Expr:=[.local_get 1,.load .i32 none {align:=2,offset:=40},.i32_const 1,.i32_relop .eq,.br_if 1]
theorem accepted_guard_code:WNear.Binary.StateReadOuter.tagGuard=acceptedGuardCode:=by kernel_rfl

theorem wp_decode_guard(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(r:UInt32)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h1:frame.locals[1]?=some (.i32 r))(hm:s.modules[frame.inst]?=some mi)
    (hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hb:r.toNat+40+4≤memory.byteSize)(ht:readI32 memory (r.toNat+40)≠1)
    (hc:s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits stack frame callers code)) rest post):
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers (acceptedGuardCode++code)))
      (5*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have hz:Numeric.bool (Numeric.irelop32 .eq (readI32 memory (r.toNat+40)) 1)=0:=by simp[Numeric.bool,Numeric.irelop32,ht]
  have br:=wp_br_if_zero cfg fuel rest (paid s op 4) limits stack frame callers code 1 post
    (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) hn
  have eq:=wp_i32_relop cfg (fuel+1) (op+rest) (paid s op 3) limits stack frame callers (.br_if 1::code) .eq (readI32 memory (r.toNat+40)) 1 post
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) (by simpa only[hz,paid,op] using br)
  have constant:=wp_i32_const cfg (fuel+2) (op+(op+rest)) (paid s op 2) limits (stack.push (.i32 (readI32 memory (r.toNat+40)))) frame callers
    (.i32_relop .eq::.br_if 1::code) 1 post (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) eq
  have load:=wp_i32_load cfg (fuel+3) (op+(op+(op+rest))) (paid s op 1) limits stack frame callers
    (.i32_const 1::.i32_relop .eq::.br_if 1::code) {align:=2,offset:=40} r mi index memory post
    (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) hb
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) constant
  have get:=wp_local_get cfg (fuel+4) (op+(op+(op+(op+rest)))) s limits stack frame callers
    (.load .i32 none {align:=2,offset:=40}::.i32_const 1::.i32_relop .eq::.br_if 1::code) 1 (.i32 r) post h1 (hc.mono (by dsimp[op];omega)) load
  simpa only[acceptedGuardCode,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(op+(op+(op+(op+rest))))=5*cfg.regularOpCost+rest by dsimp[op];omega] using get
end WNear.Proofs.StateReadOuter
