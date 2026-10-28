import Binary.StateDecodeBorsh
import Proofs.StateDecodePrefixWrapperControl
import NearVM.MeteredMemoryRules

/-! Actual425 saves the vector record before reusing its temporary result.
The length read occurs before either write, retaining arbitrary aliases. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem modules_store(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):(storeI32 s i a m v).modules=s.modules:=rfl

def prefixSavedFrame(frame:CallFrame)(scratch:UInt32):={frame with locals:=frame.locals.set! 4 (.i32 (scratch+68))}
def prefixSavedHighMemory(memory:Memory)(scratch:UInt32):=writeI32 memory (scratch.toNat+24) (readI32 memory (scratch+68).toNat)
def prefixHighStore(s:Store NearState)(op index:Nat)(memory:Memory)(scratch:UInt32):=
  storeI32 (paid s op 7) index (scratch.toNat+24) memory (readI32 memory (scratch+68).toNat)
def prefixSavedStore(s:Store NearState)(op index:Nat)(memory:Memory)(scratch:UInt32)(packed:UInt64):=
  storeI64 (paid (prefixHighStore s op index memory scratch) op 3) index (scratch.toNat+16) (prefixSavedHighMemory memory scratch) packed

theorem wp_save_prefix (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(scratch:UInt32)(packed:UInt64)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h2:frame.locals[2]?=some (.i32 scratch))(h3:frame.locals[3]?=some (.i64 packed))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hw:memory.wf)(hb:scratch.toNat+28≤memory.byteSize)(hr:(scratch+68).toNat+4≤memory.byteSize)
    (hc:s.host.gas.Credits (10*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (prefixSavedStore s cfg.regularOpCost index memory scratch packed) limits stack
      (prefixSavedFrame frame scratch) callers code)) rest post):
    WP cfg (fuel+10) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodeBorsh.savePrefix++code))) (10*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let f:=prefixSavedFrame frame scratch
  let t:=prefixHighStore s op index memory scratch
  let m:=prefixSavedHighMemory memory scratch
  have shape:=writeI32_spec memory (scratch.toNat+24) (readI32 memory (scratch+68).toNat) hw hb
  have tm:t.modules[frame.inst]?=some mi:=by unfold t prefixHighStore;rw[modules_store,modules_paid];exact hm
  have te:t.mems[index]?=some m:=storeI32_memory _ _ _ _ _ (by rw[mems_paid];exact he)
  have tc:t.host.gas.Credits (3*op+rest):=by
    simpa only[t,prefixHighStore,storeI32_host] using paid_credits s op 7 (3*op+rest) (hc.mono (by dsimp[op];omega))
  have f2:f.locals[2]?=some (.i32 scratch):=by simp[f,prefixSavedFrame,h2]
  have f3:f.locals[3]?=some (.i64 packed):=by simp[f,prefixSavedFrame,h3]
  have store:=wp_i64_store cfg fuel rest (paid t op 2) limits stack f callers code {align:=3,offset:=16} scratch packed mi index m post
    (by rw[modules_paid];exact tm) hi (by rw[mems_paid];exact te) (by change scratch.toNat+16+8≤(writeI32 _ _ _).byteSize;rw[shape.2.1];omega)
    (paid_credits t op 2 _ (tc.mono (by dsimp[op];omega))) hn
  have get3:=wp_local_get cfg (fuel+1) (op+rest) (paid t op 1) limits (stack.push (.i32 scratch)) f callers
    (.store .i64 none {align:=3,offset:=16}::code) 3 (.i64 packed) post f3 (paid_credits t op 1 _ (tc.mono (by dsimp[op];omega))) store
  have get2:=wp_local_get cfg (fuel+2) (op+(op+rest)) t limits stack f callers
    (.local_get 3::.store .i64 none {align:=3,offset:=16}::code) 2 (.i32 scratch) post f2 (tc.mono (by dsimp[op];omega)) get3
  let suffix:Expr:=[.local_get 2,.local_get 3,.store .i64 none {align:=3,offset:=16}]++code
  have save:=wp_i32_store cfg (fuel+3) (3*op+rest) (paid s op 6) limits stack f callers suffix {align:=2,offset:=24} scratch (readI32 memory (scratch+68).toNat) mi index memory post
    (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) hb (paid_credits s op 6 _ (hc.mono (by dsimp[op];omega)))
    (by simpa only[t,prefixHighStore,suffix,paid,op,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
      show cfg.regularOpCost+(op+(op+rest))=3*op+rest by dsimp[op];omega] using get2)
  have load:=wp_i32_load cfg (fuel+4) (op+(3*op+rest)) (paid s op 5) limits (stack.push (.i32 scratch)) f callers
    (.store .i32 none {align:=2,offset:=24}::suffix) {align:=2,offset:=0} (scratch+68) mi index memory post
    (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) (by simpa only[Nat.add_zero] using hr)
    (paid_credits s op 5 _ (hc.mono (by dsimp[op];omega))) save
  have tee:=wp_local_tee cfg (fuel+5) (op+(op+(3*op+rest))) (paid s op 4) limits (stack.push (.i32 scratch)) frame callers
    (.load .i32 none {align:=2,offset:=0}::.store .i32 none {align:=2,offset:=24}::suffix) 4 (.i32 (scratch+68)) post
    (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) load
  have add:=wp_i32_add cfg (fuel+6) (op+(op+(op+(3*op+rest)))) (paid s op 3) limits (stack.push (.i32 scratch)) frame callers
    (.local_tee 4::.load .i32 none {align:=2,offset:=0}::.store .i32 none {align:=2,offset:=24}::suffix) scratch 68 post
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) tee
  have con:=wp_i32_const cfg (fuel+7) (op+(op+(op+(op+(3*op+rest))))) (paid s op 2) limits ((stack.push (.i32 scratch)).push (.i32 scratch)) frame callers
    (.i32_binop .add::.local_tee 4::.load .i32 none {align:=2,offset:=0}::.store .i32 none {align:=2,offset:=24}::suffix) 68 post
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) add
  have inner:=wp_local_get cfg (fuel+8) (op+(op+(op+(op+(op+(3*op+rest)))))) (paid s op 1) limits (stack.push (.i32 scratch)) frame callers
    (.i32_const 68::.i32_binop .add::.local_tee 4::.load .i32 none {align:=2,offset:=0}::.store .i32 none {align:=2,offset:=24}::suffix) 2 (.i32 scratch) post h2
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) con
  have outer:=wp_local_get cfg (fuel+9) (op+(op+(op+(op+(op+(op+(3*op+rest))))))) s limits stack frame callers
    (.local_get 2::.i32_const 68::.i32_binop .add::.local_tee 4::.load .i32 none {align:=2,offset:=0}::.store .i32 none {align:=2,offset:=24}::suffix) 2 (.i32 scratch) post h2 (hc.mono (by dsimp[op];omega)) inner
  simpa only[WNear.Binary.StateDecodeBorsh.savePrefix,suffix,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(op+(op+(op+(op+(op+(op+(3*op+rest)))))))=10*cfg.regularOpCost+rest by dsimp[op];omega] using outer
end WNear.Proofs.StateDecodeBorsh
