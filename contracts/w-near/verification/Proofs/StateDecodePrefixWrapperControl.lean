import Proofs.StateDecodePrefixWrapperState
import Proofs.StateDecodeScalarCache
import NearVM.MeteredLoopRules
import NearVM.MeteredNumericRules

/-! Actual315 caches the packed result before testing its tag. Accepted tag
control preserves both labels and never invokes the rejected760 branch. -/
namespace WNear.Proofs.StateDecodePrefixWrapper
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32 readI64
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules:=by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems:=by
  induction n with |zero=>rfl|succ n ih=>exact ih

theorem wp_cache (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (pointer : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h2 : frame.locals[2]?=some (.i32 pointer)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (he : s.mems[index]?=some memory)
    (hb : pointer.toNat+12≤memory.byteSize) (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits stack (cacheFrame frame memory pointer) callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodePrefixWrapper.cache++code)))
      (5*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let f:={frame with locals:=frame.locals.set! 1 (.i32 1)}
  have load:=StateDecodeScalar.wp_load64_local cfg fuel rest (paid s op 2) limits stack f callers code 2 3
    {align:=2,offset:=4} pointer mi index memory post
    (by simpa[f] using h2) (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) hb
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega)))
    (by simpa only[paid,op,f,cacheFrame,StateDecodeScalar.loaded64Frame] using hnext)
  have set:=wp_local_set cfg (fuel+3) (3*op+rest) (paid s op 1) limits stack frame callers
    ([.local_get 2,.load .i64 none {align:=2,offset:=4},.local_set 3]++code) 1 (.i32 1) post
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega)))
    (by simpa only[StateDecodeScalar.loaded64Frame,f,op,paid,List.cons_append,List.nil_append] using load)
  have constant:=wp_i32_const cfg (fuel+4) (op+(3*op+rest)) s limits stack frame callers
    (.local_set 1::.local_get 2::.load .i64 none {align:=2,offset:=4}::.local_set 3::code) 1 post
    (hc.mono (by dsimp[op];omega)) set
  simpa only[WNear.Binary.StateDecodePrefixWrapper.cache,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(op+(3*op+rest))=5*cfg.regularOpCost+rest by dsimp[op];omega] using constant

theorem wp_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (pointer : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (h2 : frame.locals[2]?=some (.i32 pointer)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some index) (he : s.mems[index]?=some memory)
    (hb : pointer.toNat+4≤memory.byteSize) (hn : readI32 memory pointer.toNat≠1)
    (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits stack frame callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodePrefixWrapper.guard++code)))
      (5*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let value:=readI32 memory pointer.toNat
  have zero : Numeric.bool (Numeric.irelop32 .eq value 1)=0:=by simp[Numeric.bool,Numeric.irelop32,value,hn]
  have branch:=wp_br_if_zero cfg fuel rest (paid s op 4) limits stack frame callers code 0 post
    (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) hnext
  have rel:=wp_i32_relop cfg (fuel+1) (op+rest) (paid s op 3) limits stack frame callers (.br_if 0::code) .eq value 1 post
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) (by simpa only[zero,paid,op] using branch)
  have constant:=wp_i32_const cfg (fuel+2) (op+(op+rest)) (paid s op 2) limits (stack.push (.i32 value)) frame callers
    (.i32_relop .eq::.br_if 0::code) 1 post (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) rel
  have load:=wp_i32_load cfg (fuel+3) (op+(op+(op+rest))) (paid s op 1) limits stack frame callers
    (.i32_const 1::.i32_relop .eq::.br_if 0::code) {align:=2,offset:=0} pointer mi index memory post
    (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) (by simpa only[Nat.add_zero] using hb)
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) constant
  have get:=wp_local_get cfg (fuel+4) (op+(op+(op+(op+rest)))) s limits stack frame callers
    (.load .i32 none {align:=2,offset:=0}::.i32_const 1::.i32_relop .eq::.br_if 0::code) 2 (.i32 pointer) post h2
    (hc.mono (by dsimp[op];omega)) load
  simpa only[WNear.Binary.StateDecodePrefixWrapper.guard,List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+(op+(op+(op+rest))))=5*cfg.regularOpCost+rest by dsimp[op];omega] using get
end WNear.Proofs.StateDecodePrefixWrapper
