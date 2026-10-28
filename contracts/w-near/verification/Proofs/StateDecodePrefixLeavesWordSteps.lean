import Binary.StateDecodePrefixLeaves
import Proofs.StorePairCallerState
import NearVM.MeteredControlRules
import NearVM.MeteredLoopRules
import NearVM.MeteredWordRules
import NearVM.MeteredI32MemoryRules

/-! Accepted765's deployed branch, original word read, and packed i64 result. -/
namespace WNear.Proofs.StateDecodePrefixLeaves
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32

def wordFrame (frame : CallFrame) (m : Memory) (ptr : UInt32) :=
  {frame with locals:=(frame.locals.set! 0 (.i32 (readI32 m ptr.toNat))).set! 1 (.i32 0)}
def packedWord (word : UInt32) : UInt64 := word.toUInt64 <<< 8

theorem wp_word_pack (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr)
    (word : UInt32) (post : Post) (h0:frame.locals[0]?=some (.i32 word)) (h1:frame.locals[1]?=some (.i32 0))
    (hc:s.host.gas.Credits (7*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits (stack.push (.i64 (packedWord word))) frame callers code)) rest post) :
    WP cfg (fuel+7) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodePrefixLeaves.pack++code))) (7*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  have calcOr:Numeric.ibinop64 .or (packedWord word) (UInt32.toUInt64 0)=.ok (packedWord word):=by simp[Numeric.ibinop64]
  have last:=wp_i64_binop_ok cfg fuel rest (paid s op 6) limits stack frame callers code .or (packedWord word) (UInt32.toUInt64 0) (packedWord word) post calcOr
    (paid_credits s op 6 _ (hc.mono (by dsimp[op];omega))) hn
  have ex0:=wp_i64_extend_i32_u cfg (fuel+1) (op+rest) (paid s op 5) limits (stack.push (.i64 (packedWord word))) frame callers
    (.i64_binop .or::code) 0 post (paid_credits s op 5 _ (hc.mono (by dsimp[op];omega))) last
  have ge0:=wp_local_get cfg (fuel+2) (op+(op+rest)) (paid s op 4) limits (stack.push (.i64 (packedWord word))) frame callers
    (.cvt .i64_extend_i32_u::.i64_binop .or::code) 1 (.i32 0) post h1 (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) ex0
  have calcShift:Numeric.ibinop64 .shl word.toUInt64 8=.ok (packedWord word):=by simp[Numeric.ibinop64,packedWord]
  have sh:=wp_i64_binop_ok cfg (fuel+3) (op+(op+(op+rest))) (paid s op 3) limits stack frame callers
    (.local_get 1::.cvt .i64_extend_i32_u::.i64_binop .or::code) .shl word.toUInt64 8 (packedWord word) post calcShift
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) ge0
  have co:=wp_i64_const cfg (fuel+4) (op+(op+(op+(op+rest)))) (paid s op 2) limits (stack.push (.i64 word.toUInt64)) frame callers
    (.i64_binop .shl::.local_get 1::.cvt .i64_extend_i32_u::.i64_binop .or::code) 8 post
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) sh
  have ex:=wp_i64_extend_i32_u cfg (fuel+5) (op+(op+(op+(op+(op+rest))))) (paid s op 1) limits stack frame callers
    (.i64_const 8::.i64_binop .shl::.local_get 1::.cvt .i64_extend_i32_u::.i64_binop .or::code) word post
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) co
  have ge:=wp_local_get cfg (fuel+6) (op+(op+(op+(op+(op+(op+rest)))))) s limits stack frame callers
    (.cvt .i64_extend_i32_u::.i64_const 8::.i64_binop .shl::.local_get 1::.cvt .i64_extend_i32_u::.i64_binop .or::code) 0 (.i32 word) post h0
    (hc.mono (by dsimp[op];omega)) ex
  simpa only[WNear.Binary.StateDecodePrefixLeaves.pack,List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+(op+(op+(op+(op+(op+rest))))))=7*cfg.regularOpCost+rest by dsimp[op];omega] using ge

theorem wp_word_read (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr)
    (ptr : UInt32) (mi : ModuleInst) (i : Nat) (m : Memory) (post : Post)
    (h0:frame.locals[0]?=some (.i32 ptr)) (hm:s.modules[frame.inst]?=some mi) (hi:mi.memAddrs[0]?=some i)
    (he:s.mems[i]?=some m) (hb:ptr.toNat+4≤m.byteSize) (hc:s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits stack (wordFrame frame m ptr) callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodePrefixLeaves.read++code))) (5*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let w:=readI32 m ptr.toNat
  let f:={frame with locals:=frame.locals.set! 0 (.i32 w)}
  have se1:=wp_local_set cfg fuel rest (paid s op 4) limits stack f callers code 1 (.i32 0) post
    (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) hn
  have co:=wp_i32_const cfg (fuel+1) (op+rest) (paid s op 3) limits stack f callers (.local_set 1::code) 0 post
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) se1
  have se0:=wp_local_set cfg (fuel+2) (op+(op+rest)) (paid s op 2) limits stack frame callers
    (.i32_const 0::.local_set 1::code) 0 (.i32 w) post (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) co
  have ld:=wp_i32_load cfg (fuel+3) (op+(op+(op+rest))) (paid s op 1) limits stack frame callers
    (.local_set 0::.i32_const 0::.local_set 1::code) {align:=0,offset:=0} ptr mi i m post hm hi he
    (by simpa only[Nat.add_zero] using hb) (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) se0
  have ge:=wp_local_get cfg (fuel+4) (op+(op+(op+(op+rest)))) s limits stack frame callers
    (.load .i32 none {align:=0,offset:=0}::.local_set 0::.i32_const 0::.local_set 1::code) 0 (.i32 ptr) post h0
    (hc.mono (by dsimp[op];omega)) ld
  simpa only[WNear.Binary.StateDecodePrefixLeaves.read,List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+(op+(op+(op+rest))))=5*cfg.regularOpCost+rest by dsimp[op];omega] using ge
end WNear.Proofs.StateDecodePrefixLeaves
