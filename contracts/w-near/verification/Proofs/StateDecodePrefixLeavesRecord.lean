import Binary.StateDecodePrefixLeaves
import Proofs.StateDecodeSlicesResult

/-! Actual764 records an accepted length with a zero status word. -/
namespace WNear.Proofs.StateDecodePrefixLeaves
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode

def recordHigh (s : Store NearState) (op i : Nat) (m : Memory) (out len : UInt32) :=
  storeI32 (paid s op 3) i (out.toNat+4) m len
def recordMemory (m : Memory) (out len : UInt32) := writeI32 (writeI32 m (out.toNat+4) len) out.toNat 0
def recordAfter (s : Store NearState) (op i : Nat) (m : Memory) (out len : UInt32) :=
  storeI32 (paid (recordHigh s op i m out len) op 3) i out.toNat (writeI32 m (out.toNat+4) len) 0
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl|succ n ih=>exact ih

private theorem wp_zero_store (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr)
    (out : UInt32) (mi : ModuleInst) (i : Nat) (m : Memory) (post : Post)
    (h0 : frame.locals[0]?=some (.i32 out)) (hm : s.modules[frame.inst]?=some mi)
    (hi : mi.memAddrs[0]?=some i) (he : s.mems[i]?=some m) (hb : out.toNat+4≤m.byteSize)
    (hc : s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hn : WP cfg fuel (.next (atCode (storeI32 (paid s cfg.regularOpCost 3) i out.toNat m 0) limits stack frame callers code)) rest post) :
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers
      (.local_get 0::.i32_const 0::.store .i32 none {align:=2,offset:=0}::code))) (3*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  have mm:(paid s op 2).modules[frame.inst]?=some mi:=by rw[modules_paid];exact hm
  have me:(paid s op 2).mems[i]?=some m:=by rw[mems_paid];exact he
  have st:=wp_i32_store cfg fuel rest (paid s op 2) limits stack frame callers code {align:=2,offset:=0} out 0 mi i m post mm hi me
    (by simpa only[Nat.add_zero] using hb) (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) hn
  have co:=wp_i32_const cfg (fuel+1) (op+rest) (paid s op 1) limits (stack.push (.i32 out)) frame callers
    (.store .i32 none {align:=2,offset:=0}::code) 0 post (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) st
  have ge:=wp_local_get cfg (fuel+2) (op+(op+rest)) s limits stack frame callers
    (.i32_const 0::.store .i32 none {align:=2,offset:=0}::code) 0 (.i32 out) post h0 (hc.mono (by dsimp[op];omega)) co
  simpa only [show cfg.regularOpCost+(op+(op+rest))=3*cfg.regularOpCost+rest by dsimp[op];omega] using ge

theorem wp_record_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr)
    (out len : UInt32) (mi : ModuleInst) (i : Nat) (m : Memory) (post : Post)
    (h0 : frame.locals[0]?=some (.i32 out)) (h1 : frame.locals[1]?=some (.i32 len))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some i) (he : s.mems[i]?=some m)
    (hw : m.wf) (hb : out.toNat+8≤m.byteSize) (hc : s.host.gas.Credits (6*cfg.regularOpCost+rest))
    (hn : WP cfg fuel (.next (atCode (recordAfter s cfg.regularOpCost i m out len) limits stack frame callers code)) rest post) :
    WP cfg (fuel+6) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodePrefixLeaves.recordBody++code)))
      (6*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let one:=recordHigh s op i m out len
  have spec:=writeI32_spec m (out.toNat+4) len hw (by omega)
  have mm:one.modules[frame.inst]?=some mi:=by simp only[one,recordHigh,storeI32_modules,modules_paid];exact hm
  have mp:(paid s op 3).mems[i]?=some m:=by rw[mems_paid];exact he
  have me:one.mems[i]?=some (writeI32 m (out.toNat+4) len):=storeI32_memory _ i _ m len mp
  have co:one.host.gas.Credits (3*op+rest):=by
    change (paid s op 3).host.gas.Credits _
    exact paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))
  have bound:out.toNat+4≤(writeI32 m (out.toNat+4) len).byteSize:=by rw[spec.2.1];omega
  have low:=wp_zero_store cfg fuel rest one limits stack frame callers code out mi i (writeI32 m (out.toNat+4) len) post h0 mm hi me bound co hn
  have high:=StateDecodeSlices.wp_word_store cfg (fuel+3) (3*op+rest) s limits stack frame callers
    (.local_get 0::.i32_const 0::.store .i32 none {align:=2,offset:=0}::code) out len 1 4 mi i m post h0 h1 hm hi he
    (by omega) (hc.mono (by dsimp[op];omega)) low
  simpa only[WNear.Binary.StateDecodePrefixLeaves.recordBody,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 3*cfg.regularOpCost+(3*op+rest)=6*cfg.regularOpCost+rest by dsimp[op];omega] using high
end WNear.Proofs.StateDecodePrefixLeaves
