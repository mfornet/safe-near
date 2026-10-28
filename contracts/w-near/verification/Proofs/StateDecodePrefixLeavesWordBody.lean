import Proofs.StateDecodePrefixLeavesWordSuffix
import Proofs.ValueReturnBorrow

/-! Full accepted765 body: real length guard, original unaligned word, packed result. -/
namespace WNear.Proofs.StateDecodePrefixLeaves
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode readI32

private theorem wp_four (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr) (post : Post)
    (h1:frame.locals[1]?=some (.i32 4)) (hc:s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits stack frame callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers
      (.block .empty (WNear.Binary.StateDecodePrefixLeaves.guard++[.i32_const 1,.local_set 1,.br 1])::code))) (4*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let bf:=emptyBlockFrame frame stack.size code
  have test:Numeric.bool (Numeric.irelop32 .eq 4 4)≠0:=by decide
  have br:=wp_br_if_block_nonzero cfg fuel rest (paid s op 3) limits stack frame callers code
    [.i32_const 1,.local_set 1,.br 1] (Numeric.bool (Numeric.irelop32 .eq 4 4)) post test
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) hn
  have rel:=wp_i32_relop cfg (fuel+1) (op+rest) (paid s op 2) limits stack bf callers
    [.br_if 0,.i32_const 1,.local_set 1,.br 1] .eq 4 4 post (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) br
  have co:=wp_i32_const cfg (fuel+2) (op+(op+rest)) (paid s op 1) limits (stack.push (.i32 4)) bf callers
    [.i32_relop .eq,.br_if 0,.i32_const 1,.local_set 1,.br 1] 4 post (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) rel
  have ge:=wp_local_get cfg (fuel+3) (op+(op+(op+rest))) s limits stack bf callers
    [.i32_const 4,.i32_relop .eq,.br_if 0,.i32_const 1,.local_set 1,.br 1] 1 (.i32 4) post h1
    (hc.mono (by dsimp[op];omega)) co
  have inside:WP cfg (fuel+4) (.next (atCode s limits stack bf callers
      (WNear.Binary.StateDecodePrefixLeaves.guard++[.i32_const 1,.local_set 1,.br 1]))) (4*cfg.regularOpCost+rest) post:=by
    simpa only[WNear.Binary.StateDecodePrefixLeaves.guard,List.cons_append,List.nil_append,
      show cfg.regularOpCost+(op+(op+(op+rest)))=4*cfg.regularOpCost+rest by dsimp[op];omega] using ge
  exact wp_block_empty cfg (fuel+4) _ s limits stack frame callers _ code post hc inside

private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules:=by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems:=by
  induction n with |zero=>rfl|succ n ih=>exact ih

theorem wp_word_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr)
    (ptr : UInt32) (mi : ModuleInst) (i : Nat) (m : Memory) (post : Post)
    (h0:frame.locals[0]?=some (.i32 ptr)) (h1:frame.locals[1]?=some (.i32 4)) (hsize:2≤frame.locals.size)
    (hm:s.modules[frame.inst]?=some mi) (hi:mi.memAddrs[0]?=some i) (he:s.mems[i]?=some m) (hb:ptr.toNat+4≤m.byteSize)
    (hc:s.host.gas.Credits (16*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 16) limits
      (stack.push (.i64 (packedWord (readI32 m ptr.toNat)))) (wordFrame frame m ptr) callers code)) rest post) :
    WP cfg (fuel+19) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodePrefixLeaves.wordBody++code))) (16*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let outer:=emptyBlockFrame frame stack.size (WNear.Binary.StateDecodePrefixLeaves.pack++code)
  have suffixNext:WP cfg fuel (.next (atCode (paid (paid s op 4) op 12) limits
      (stack.push (.i64 (packedWord (readI32 m ptr.toNat)))) (wordFrame frame m ptr) callers code)) rest post:=by
    simpa only[ValueReturnBorrow.paid_add,op] using hn
  have mh:(paid s op 4).modules[frame.inst]?=some mi:=by rw[modules_paid];exact hm
  have eh:(paid s op 4).mems[i]?=some m:=by rw[mems_paid];exact he
  have ch:(paid s op 4).host.gas.Credits (12*cfg.regularOpCost+rest):=paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))
  have suffix:=wp_read_pack cfg fuel rest (paid s op 4) limits stack frame callers code ptr mi i m post
    h0 hsize mh hi eh hb ch suffixNext
  have cut:=wp_four cfg (fuel+13) (12*op+rest) s limits stack outer callers WNear.Binary.StateDecodePrefixLeaves.read post h1
    (hc.mono (by dsimp[op];omega)) suffix
  have outerProof:=wp_block_empty cfg (fuel+18) (16*op+rest) s limits stack frame callers
    ([.block .empty (WNear.Binary.StateDecodePrefixLeaves.guard++[.i32_const 1,.local_set 1,.br 1])]++WNear.Binary.StateDecodePrefixLeaves.read)
    (WNear.Binary.StateDecodePrefixLeaves.pack++code) post hc
    (by simpa only[outer,List.singleton_append,show 4*cfg.regularOpCost+(12*op+rest)=16*op+rest by dsimp[op];omega] using cut)
  simpa only[WNear.Binary.StateDecodePrefixLeaves.wordBody,List.cons_append,List.nil_append] using outerProof
end WNear.Proofs.StateDecodePrefixLeaves
