import Proofs.AllocateLayoutState
import NearVM.MeteredWordRules

/-! Actual popcount assertion guard on the alignment-one accepted path. -/
namespace WNear.Proofs.AllocateLayout
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP readI32

def alignmentFrame (frame : CallFrame) := {frame with locals := frame.locals.set! 3 (.i32 1)}

/-- The real seven charged guard instructions skip the panic block. The free
block entry is counted separately; no assertion outcome is assumed. -/
theorem wp_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code panic : List Instr) (input : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hp : frame.locals[1]? = some (.i32 input)) (hm : s.modules[frame.inst]? = some mi)
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hb : input.toNat + 8 ≤ memory.byteSize) (ha : readI32 memory (input.toNat + 4) = 1)
    (hc : s.host.gas.Credits (7 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits stack (alignmentFrame frame) callers code)) rest post) :
    WP cfg (fuel + 8) (.next (atCode s limits stack frame callers
      (.block .empty (WNear.Binary.AllocateLayout.guard ++ panic) :: code))) (7 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let bf := emptyBlockFrame frame stack.size code
  let af := alignmentFrame bf
  have branch := wp_br_if_block_nonzero cfg fuel rest (paid s op 6) limits stack (alignmentFrame frame) callers code panic 1 post
    (by decide) (paid_credits s op 6 _ (hc.mono (by dsimp [op]; omega))) hnext
  have rel := wp_i32_relop cfg (fuel + 1) (op + rest) (paid s op 5) limits stack af callers (.br_if 0 :: panic) .eq 1 1 post
    (paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))) branch
  have con := wp_i32_const cfg (fuel + 2) (op + (op + rest)) (paid s op 4) limits (stack.push (.i32 1)) af callers
    (.i32_relop .eq :: .br_if 0 :: panic) 1 post (paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))) rel
  have unop := wp_i32_unop cfg (fuel + 3) (op + (op + (op + rest))) (paid s op 3) limits stack af callers
    (.i32_const 1 :: .i32_relop .eq :: .br_if 0 :: panic) .popcnt 1 post
    (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))) con
  have tee := wp_local_tee cfg (fuel + 4) (op + (op + (op + (op + rest)))) (paid s op 2) limits stack bf callers
    (.i32_unop .popcnt :: .i32_const 1 :: .i32_relop .eq :: .br_if 0 :: panic) 3 (.i32 1) post
    (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) unop
  have hm1 : (paid s op 1).modules[bf.inst]? = some mi := by simpa only [paid,chargedStore,bf,emptyBlockFrame] using hm
  have mm1 : (paid s op 1).mems[index]? = some memory := by simpa only [paid,chargedStore] using hmem
  have ln : WP cfg (fuel + 5) (.next (atCode (paid s op 2) limits (stack.push (.i32 (readI32 memory (input.toNat + 4)))) bf callers
      (.local_tee 3 :: .i32_unop .popcnt :: .i32_const 1 :: .i32_relop .eq :: .br_if 0 :: panic)))
      (op + (op + (op + (op + (op + rest))))) post := by simpa only [ha] using tee
  have load := wp_i32_load cfg (fuel + 5) (op + (op + (op + (op + (op + rest))))) (paid s op 1) limits stack bf callers
    (.local_tee 3 :: .i32_unop .popcnt :: .i32_const 1 :: .i32_relop .eq :: .br_if 0 :: panic)
    {align := 2,offset := 4} input mi index memory post hm1 hi mm1 hb
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) ln
  have get := wp_local_get cfg (fuel + 6) (op + (op + (op + (op + (op + (op + rest)))))) s limits stack bf callers
    (.load .i32 none {align := 2,offset := 4} :: .local_tee 3 :: .i32_unop .popcnt :: .i32_const 1 :: .i32_relop .eq :: .br_if 0 :: panic)
    1 (.i32 input) post hp (hc.mono (by dsimp [op]; omega)) load
  have inside : WP cfg (fuel + 7) (.next (atCode s limits stack bf callers (WNear.Binary.AllocateLayout.guard ++ panic))) (7 * cfg.regularOpCost + rest) post := by
    simpa only [WNear.Binary.AllocateLayout.guard,List.cons_append,List.nil_append,
      show cfg.regularOpCost + (op + (op + (op + (op + (op + (op + rest)))))) = 7 * cfg.regularOpCost + rest by dsimp [op]; omega] using get
  exact wp_block_empty cfg (fuel + 7) _ s limits stack frame callers _ code post hc inside

end WNear.Proofs.AllocateLayout
