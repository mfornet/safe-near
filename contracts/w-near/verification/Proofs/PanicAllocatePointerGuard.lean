import Proofs.PanicAllocatePointerState

/-! Actual nonzero-pointer block of deployed f503. -/
namespace WNear.Proofs.PanicAllocatePointerGuard
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 200000
attribute [local irreducible] WP

def guardFrame (frame : CallFrame) (pointer : UInt32) := {frame with locals := frame.locals.set! 3 (.i32 pointer)}

theorem wp_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch pointer : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hs : frame.locals[2]? = some (.i32 scratch)) (hm : s.modules[frame.inst]? = some mi)
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hb : scratch.toNat + 8 + 4 ≤ memory.byteSize) (hread : readI32 memory (scratch.toNat + 8) = pointer)
    (hn : pointer ≠ 0) (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits stack (guardFrame frame pointer) callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits stack frame callers
      (.block .empty WNear.Binary.PanicAllocate.guard503 :: code))) (4 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let bf := emptyBlockFrame frame stack.size code
  let gf := guardFrame frame pointer
  let panic : List Instr := [.local_get 0, .local_get 1, .call 842, .unreachable]
  have branch := wp_br_if_block_nonzero cfg fuel rest (paid s op 3) limits stack gf callers code panic pointer post hn
    (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))) hnext
  have branchNext : WP cfg (fuel + 1) (.next (atCode (paid s op 3) limits (stack.push (.i32 pointer))
      {bf with locals := bf.locals.set! 3 (.i32 pointer)} callers (.br_if 0 :: panic))) (op + rest) post := by
    simpa only [gf, guardFrame, bf, emptyBlockFrame, op] using branch
  have tee := wp_local_tee cfg (fuel + 1) (op + rest) (paid s op 2) limits stack bf callers
    (.br_if 0 :: panic) 3 (.i32 pointer) post (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) branchNext
  have hm1 : (paid s op 1).modules[bf.inst]? = some mi := by simpa only [paid, chargedStore, bf, emptyBlockFrame] using hm
  have hmem1 : (paid s op 1).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have teeNext : WP cfg (fuel + 1 + 1) (.next (atCode (paid s op 2) limits
      (stack.push (.i32 (readI32 memory (scratch.toNat + 8)))) bf callers (.local_tee 3 :: .br_if 0 :: panic)))
      (op + (op + rest)) post := by simpa only [hread, op] using tee
  have load := wp_i32_load cfg (fuel + 1 + 1) (op + (op + rest)) (paid s op 1) limits stack bf callers
    (.local_tee 3 :: .br_if 0 :: panic) {align := 2, offset := 8} scratch mi index memory post hm1 hi hmem1 hb
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) teeNext
  have get := wp_local_get cfg (fuel + 1 + 1 + 1) (op + (op + (op + rest))) s limits stack bf callers
    (.load .i32 none {align := 2, offset := 8} :: .local_tee 3 :: .br_if 0 :: panic) 2 (.i32 scratch) post hs
    (hc.mono (by dsimp [op]; omega)) load
  have inside : WP cfg (fuel + 4) (.next (atCode s limits stack bf callers WNear.Binary.PanicAllocate.guard503))
      (4 * op + rest) post := by
    have ge : cfg.regularOpCost + (op + (op + (op + rest))) = 4 * op + rest := by dsimp [op]; omega
    simpa only [ge, panic, WNear.Binary.PanicAllocate.guard503, Nat.add_assoc, Nat.reduceAdd] using get
  have result := wp_block_empty cfg (fuel + 4) (4 * op + rest) s limits stack frame callers
    WNear.Binary.PanicAllocate.guard503 code post hc inside
  simpa only [Nat.add_assoc, Nat.reduceAdd, op] using result

end WNear.Proofs.PanicAllocatePointerGuard
