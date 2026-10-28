import Proofs.AllocateVectorOuterOutput
import NearVM.MeteredBitRules
import NearVM.MeteredLoopRules
import NearVM.MeteredScalarRules

/-! The actual f687 low-byte guard and cached record read, independent of allocation. -/
namespace WNear.Proofs.AllocateVectorOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384

def cachedFrame (frame : CallFrame) (memory : Memory) (scratch : UInt32) :=
  {frame with locals:=frame.locals.set! 4 (.i64 (readI64 memory (scratch.toNat+8)))}

theorem wp_byte_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (flag : UInt32) (post : Post)
    (h1 : frame.locals[1]?=some (.i32 flag)) (hflag : flag &&& 255=0)
    (hc : s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits stack frame callers code)) rest post) :
    WP cfg (fuel+4) (.next (atCode s limits stack frame callers
      (.local_get 1::.i32_const 255::.i32_binop .and::.br_if 0::code))) (4*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have next : WP cfg fuel (.next (atCode (chargedStore (paid s op 3) cfg.regularOpCost) limits stack frame callers code)) rest post := by
    simpa only [paid,op] using hnext
  have branch := wp_br_if_zero cfg fuel rest (paid s op 3) limits stack frame callers code 0 post
    (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) next
  have andNext : WP cfg (fuel+1) (.next (atCode (chargedStore (paid s op 2) cfg.regularOpCost) limits
      (stack.push (.i32 (flag &&& 255))) frame callers (.br_if 0::code))) (op+rest) post := by
    simpa only [hflag,paid,op] using branch
  have bit := wp_i32_and cfg (fuel+1) (op+rest) (paid s op 2) limits stack frame callers (.br_if 0::code) flag 255 post
    (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) andNext
  have constant := wp_i32_const cfg (fuel+2) (op+(op+rest)) (paid s op 1) limits (stack.push (.i32 flag)) frame callers
    (.i32_binop .and::.br_if 0::code) 255 post (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) bit
  have get := wp_local_get cfg (fuel+3) (op+(op+(op+rest))) s limits stack frame callers
    (.i32_const 255::.i32_binop .and::.br_if 0::code) 1 (.i32 flag) post h1 (hc.mono (by dsimp [op];omega)) constant
  have ce : cfg.regularOpCost+(op+(op+(op+rest)))=4*cfg.regularOpCost+rest := by dsimp [op];omega
  rw [ce] at get
  simpa only [Nat.add_assoc,Nat.reduceAdd] using get

theorem wp_cache (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (mi : ModuleInst) (index : Nat) (memory : Memory) (scratch : UInt32) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 scratch))
    (hm : s.modules[frame.inst]?=some mi) (hi : mi.memAddrs[0]?=some index)
    (hmem : s.mems[index]?=some memory) (hb : scratch.toNat+16≤memory.byteSize)
    (hc : s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits stack (cachedFrame frame memory scratch) callers code)) rest post) :
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers (WNear.Binary.AllocateVectorOuter.cache++code)))
      (3*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let value := readI64 memory (scratch.toNat+8)
  have next : WP cfg fuel (.next (atCode (chargedStore (paid s op 2) cfg.regularOpCost) limits stack
      {frame with locals:=frame.locals.set! 4 (.i64 value)} callers code)) rest post := by
    simpa only [cachedFrame,value,paid,op] using hnext
  have set := wp_local_set cfg fuel rest (paid s op 2) limits stack frame callers code 4 (.i64 value) post
    (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) next
  have load := wp_i64_load cfg (fuel+1) (op+rest) (paid s op 1) limits stack frame callers (.local_set 4::code)
    {align:=3,offset:=8} scratch mi index memory post hm hi hmem (by omega)
    (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) set
  have get := wp_local_get cfg (fuel+2) (op+(op+rest)) s limits stack frame callers
    (.load .i64 none {align:=3,offset:=8}::.local_set 4::code) 3 (.i32 scratch) post h3
    (hc.mono (by dsimp [op];omega)) load
  have ce : cfg.regularOpCost+(op+(op+rest))=3*cfg.regularOpCost+rest := by dsimp [op];omega
  rw [ce] at get
  simpa only [WNear.Binary.AllocateVectorOuter.cache,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using get
end WNear.Proofs.AllocateVectorOuter
