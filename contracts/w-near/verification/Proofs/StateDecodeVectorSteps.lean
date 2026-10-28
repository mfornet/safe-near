import Proofs.StateDecodeVectorState
import Proofs.StateDecodeScalarOutput
import Proofs.InterfaceStack

/-! Actual373 argument and cached-output instruction groups. -/
namespace WNear.Proofs.StateDecodeVector
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode

def zeroStore (s:Store NearState) (op i:Nat) (m:Memory) (out:UInt32) := storeI32 (paid s op 3) i (out.toNat+8) m 0
def outputStore (s:Store NearState) (op i:Nat) (m:Memory) (out:UInt32) (packed:UInt64) :=
  StateDecodeScalar.store64Local (zeroStore s op i m out) op i (writeI32 m (out.toNat+8) 0) out packed

private theorem modules_paid (s:Store NearState) (op n:Nat) : (paid s op n).modules=s.modules:=by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem mems_paid (s:Store NearState) (op n:Nat) : (paid s op n).mems=s.mems:=by
  induction n with |zero=>rfl|succ n ih=>exact ih

theorem wp_arguments (cfg:WasmConfig) (fuel rest:Nat) (s:Store NearState) (limits:ExecLimits)
    (stack:Array Value) (frame:CallFrame) (callers:List CallFrame) (code:Expr) (scratch size:UInt32) (post:Post)
    (h2:frame.locals[2]?=some (.i32 scratch)) (h1:frame.locals[1]?=some (.i32 size))
    (hc:s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits
      (((stack.push (.i32 (scratch+8))).push (.i32 size)).push (.i32 0)) frame callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodeVector.arguments++code))) (5*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  have zero:=wp_i32_const cfg fuel rest (paid s op 4) limits ((stack.push (.i32 (scratch+8))).push (.i32 size)) frame callers code 0 post
    (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) hn
  have sizeArg:=wp_local_get cfg (fuel+1) (op+rest) (paid s op 3) limits (stack.push (.i32 (scratch+8))) frame callers
    (.i32_const 0::code) 1 (.i32 size) post h1 (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) zero
  have add:=wp_i32_add cfg (fuel+2) (op+(op+rest)) (paid s op 2) limits stack frame callers
    (.local_get 1::.i32_const 0::code) scratch 8 post (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) sizeArg
  have constant:=wp_i32_const cfg (fuel+3) (op+(op+(op+rest))) (paid s op 1) limits (stack.push (.i32 scratch)) frame callers
    (.i32_binop .add::.local_get 1::.i32_const 0::code) 8 post (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) add
  have get:=wp_local_get cfg (fuel+4) (op+(op+(op+(op+rest)))) s limits stack frame callers
    (.i32_const 8::.i32_binop .add::.local_get 1::.i32_const 0::code) 2 (.i32 scratch) post h2 (hc.mono (by dsimp[op];omega)) constant
  simpa only[WNear.Binary.StateDecodeVector.arguments,List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+(op+(op+(op+rest))))=5*cfg.regularOpCost+rest by dsimp[op];omega] using get

private theorem wp_zero (cfg:WasmConfig) (fuel rest:Nat) (s:Store NearState) (limits:ExecLimits)
    (stack:Array Value) (frame:CallFrame) (callers:List CallFrame) (code:Expr) (out:UInt32)
    (mi:ModuleInst) (i:Nat) (m:Memory) (post:Post) (h0:frame.locals[0]?=some (.i32 out))
    (hm:s.modules[frame.inst]?=some mi) (hi:mi.memAddrs[0]?=some i) (he:s.mems[i]?=some m)
    (hb:out.toNat+8+4≤m.byteSize) (hc:s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (zeroStore s cfg.regularOpCost i m out) limits stack frame callers code)) rest post) :
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers
      (.local_get 0::.i32_const 0::.store .i32 none {align:=2,offset:=8}::code))) (3*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  have mm:(paid s op 2).modules[frame.inst]?=some mi:=by rw[modules_paid];exact hm
  have me:(paid s op 2).mems[i]?=some m:=by rw[mems_paid];exact he
  have store:=wp_i32_store cfg fuel rest (paid s op 2) limits stack frame callers code {align:=2,offset:=8} out 0 mi i m post mm hi me hb
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) hn
  have zero:=wp_i32_const cfg (fuel+1) (op+rest) (paid s op 1) limits (stack.push (.i32 out)) frame callers
    (.store .i32 none {align:=2,offset:=8}::code) 0 post (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) store
  have get:=wp_local_get cfg (fuel+2) (op+(op+rest)) s limits stack frame callers
    (.i32_const 0::.store .i32 none {align:=2,offset:=8}::code) 0 (.i32 out) post h0 (hc.mono (by dsimp[op];omega)) zero
  simpa only[show cfg.regularOpCost+(op+(op+rest))=3*cfg.regularOpCost+rest by dsimp[op];omega] using get

theorem wp_output (cfg:WasmConfig) (fuel rest:Nat) (s:Store NearState) (limits:ExecLimits)
    (stack:Array Value) (frame:CallFrame) (callers:List CallFrame) (code:Expr) (out:UInt32) (packed:UInt64)
    (mi:ModuleInst) (i:Nat) (m:Memory) (post:Post) (h0:frame.locals[0]?=some (.i32 out)) (h3:frame.locals[3]?=some (.i64 packed))
    (hm:s.modules[frame.inst]?=some mi) (hi:mi.memAddrs[0]?=some i) (he:s.mems[i]?=some m)
    (hw:m.wf) (hb:out.toNat+12≤m.byteSize) (hc:s.host.gas.Credits (6*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (outputStore s cfg.regularOpCost i m out packed) limits stack frame callers code)) rest post) :
    WP cfg (fuel+6) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodeVector.output++code))) (6*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let one:=zeroStore s op i m out
  have z:=writeI32_spec m (out.toNat+8) 0 hw hb
  have mm:one.modules[frame.inst]?=some mi:=by simp only[one,zeroStore,storeI32_modules,modules_paid];exact hm
  have mp:(paid s op 3).mems[i]?=some m:=by rw[mems_paid];exact he
  have me:one.mems[i]?=some (writeI32 m (out.toNat+8) 0):=storeI32_memory _ i _ m 0 mp
  have cb:3*op+(3*op+rest)≤6*cfg.regularOpCost+rest:=by dsimp[op];omega
  have co:one.host.gas.Credits (3*op+rest):=paid_credits s op 3 _ (hc.mono cb)
  have bound:out.toNat+8≤(writeI32 m (out.toNat+8) 0).byteSize:=by rw[z.2.1];omega
  have low:=StateDecodeScalar.wp_store64_local cfg fuel rest one limits stack frame callers code 0 3 out packed mi i
    (writeI32 m (out.toNat+8) 0) post h0 h3 mm hi me bound co hn
  have high:=wp_zero cfg (fuel+3) (3*op+rest) s limits stack frame callers
    (.local_get 0::.local_get 3::.store .i64 none {align:=2,offset:=0}::code) out mi i m post h0 hm hi he hb
    (hc.mono (by dsimp[op];omega)) low
  simpa only[WNear.Binary.StateDecodeVector.output,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 3*cfg.regularOpCost+(3*op+rest)=6*cfg.regularOpCost+rest by dsimp[op];omega] using high
end WNear.Proofs.StateDecodeVector
