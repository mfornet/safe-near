import Proofs.StateDecodeBorshReadControl

/-! Real161 accepted exhausted-input branch, reading the CURRENT descriptor.
The caller supplies its pure readback theorem, not an execution outcome. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

theorem wp_exhausted(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code rejected:Expr)(r:UInt32)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h3:frame.locals[3]?=some (.i32 r))(hm:s.modules[frame.inst]?=some mi)
    (hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hb:r.toNat+12+4≤memory.byteSize)(hz:readI32 memory (r.toNat+12)=0)
    (hc:s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits stack frame callers code)) rest post):
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers
      (.block .empty ([.local_get 3,.load .i32 none {align:=2,offset:=12},.i32_eqz,.br_if 0]++rejected)::code)))
      (4*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let bf:=emptyBlockFrame frame stack.size code
  have test:Numeric.bool ((readI32 memory (r.toNat+12))==0)≠0:=by rw[hz];decide
  have br:=wp_br_if_block_nonzero cfg fuel rest (paid s op 3) limits stack frame callers code rejected
    (Numeric.bool ((readI32 memory (r.toNat+12))==0)) post test
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) hn
  have eqz:=wp_i32_eqz cfg (fuel+1) (op+rest) (paid s op 2) limits stack bf callers
    (.br_if 0::rejected) (readI32 memory (r.toNat+12)) post
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) br
  have load:=wp_i32_load cfg (fuel+2) (op+(op+rest)) (paid s op 1) limits stack bf callers
    (.i32_eqz::.br_if 0::rejected) {align:=2,offset:=12} r mi index memory post
    (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) hb
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) eqz
  have get:=wp_local_get cfg (fuel+3) (op+(op+(op+rest))) s limits stack bf callers
    (.load .i32 none {align:=2,offset:=12}::.i32_eqz::.br_if 0::rejected) 3 (.i32 r) post h3
    (hc.mono (by dsimp[op];omega)) load
  have inside:WP cfg (fuel+4) (.next (atCode s limits stack bf callers
      ([.local_get 3,.load .i32 none {align:=2,offset:=12},.i32_eqz,.br_if 0]++rejected)))
      (4*cfg.regularOpCost+rest) post:=by
    simpa only[List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
      show cfg.regularOpCost+(op+(op+(op+rest)))=4*cfg.regularOpCost+rest by dsimp[op];omega] using get
  exact wp_block_empty cfg (fuel+4) _ s limits stack frame callers _ code post hc inside
end WNear.Proofs.StateDecodeBorshRead
