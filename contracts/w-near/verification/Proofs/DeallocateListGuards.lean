import Binary.DeallocateList
import NearVM.MeteredBitRules
import Proofs.ValueReturnOuterBody

/-! The exact normal-path header guards used by both575 unlink blocks. -/
namespace WNear.Proofs.DeallocateListGuards
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP readI32

def headerFrame (frame : CallFrame) (raw : UInt32) :=
  {frame with locals := (frame.locals.set! 1 (.i32 raw)).set! 2 (.i32 (raw &&& 4294967292))}

/-- Both real eight-instruction guards load the current snapshot, retain its
raw flags and masked link, and fall through only for a nonzero link. -/
theorem wp_header (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (offset : Nat) (pointer : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hp : frame.locals[0]? = some (.i32 pointer)) (_hn : 3 ≤ frame.locals.size)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : pointer.toNat + offset + 4 ≤ memory.byteSize)
    (hlink : readI32 memory (pointer.toNat + offset) &&& 4294967292 ≠ 0)
    (hc : s.host.gas.Credits (8 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 8) limits stack
      (headerFrame frame (readI32 memory (pointer.toNat + offset))) callers code)) rest post) :
    WP cfg (fuel + 8) (.next (atCode s limits stack frame callers
      ([.local_get 0, .load .i32 none {align := 2, offset}, .local_tee 1, .i32_const 4294967292,
        .i32_binop .and, .local_tee 2, .i32_eqz, .br_if 0] ++ code)))
      (8 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let raw := readI32 memory (pointer.toNat + offset)
  let link := raw &&& 4294967292
  let f1 := {frame with locals := frame.locals.set! 1 (.i32 raw)}
  let f2 := headerFrame frame raw
  have zero : Numeric.bool (link == 0) = 0 := by simp [Numeric.bool, link, raw, hlink]
  have branch := wp_br_if_zero cfg fuel rest (paid s op 7) limits stack f2 callers code 0 post
    (paid_credits s op 7 _ (hc.mono (by dsimp [op]; omega))) hnext
  have branchNext : WP cfg (fuel + 1) (.next (atCode (paid s op 7) limits
      (stack.push (.i32 (Numeric.bool (link == 0)))) f2 callers (.br_if 0 :: code))) (op + rest) post := by
    simpa only [zero, op] using branch
  have eqz := wp_i32_eqz cfg (fuel + 1) (op + rest) (paid s op 6) limits stack f2 callers (.br_if 0 :: code) link post
    (paid_credits s op 6 _ (hc.mono (by dsimp [op]; omega))) branchNext
  have tee2 := wp_local_tee cfg (fuel + 2) (op + (op + rest)) (paid s op 5) limits stack f1 callers
    (.i32_eqz :: .br_if 0 :: code) 2 (.i32 link) post (paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))) eqz
  have and := wp_i32_and cfg (fuel + 3) (op + (op + (op + rest))) (paid s op 4) limits stack f1 callers
    (.local_tee 2 :: .i32_eqz :: .br_if 0 :: code) raw 4294967292 post (paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))) tee2
  have con := wp_i32_const cfg (fuel + 4) (op + (op + (op + (op + rest)))) (paid s op 3) limits (stack.push (.i32 raw)) f1 callers
    (.i32_binop .and :: .local_tee 2 :: .i32_eqz :: .br_if 0 :: code) 4294967292 post
    (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))) and
  have tee1 := wp_local_tee cfg (fuel + 5) (op + (op + (op + (op + (op + rest))))) (paid s op 2) limits stack frame callers
    (.i32_const 4294967292 :: .i32_binop .and :: .local_tee 2 :: .i32_eqz :: .br_if 0 :: code) 1 (.i32 raw) post
    (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) con
  have hm1 : (paid s op 1).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hmem1 : (paid s op 1).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have load := wp_i32_load cfg (fuel + 6) (op + (op + (op + (op + (op + (op + rest)))))) (paid s op 1) limits stack frame callers
    (.local_tee 1 :: .i32_const 4294967292 :: .i32_binop .and :: .local_tee 2 :: .i32_eqz :: .br_if 0 :: code)
    {align := 2, offset} pointer mi index memory post hm1 hi hmem1 hb
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) tee1
  have result := wp_local_get cfg (fuel + 7) (op + (op + (op + (op + (op + (op + (op + rest))))))) s limits stack frame callers
    (.load .i32 none {align := 2, offset} :: .local_tee 1 :: .i32_const 4294967292 :: .i32_binop .and :: .local_tee 2 :: .i32_eqz :: .br_if 0 :: code)
    0 (.i32 pointer) post hp (hc.mono (by dsimp [op]; omega)) load
  have ge : cfg.regularOpCost + (op + (op + (op + (op + (op + (op + (op + rest))))))) = 8 * cfg.regularOpCost + rest := by dsimp [op]; omega
  exact ValueReturnOuterBody.cast_phase cfg _ _ _ _ s limits stack frame callers _ _ post rfl ge rfl result

def selectedFrame (frame : CallFrame) (link : UInt32) := {frame with locals := frame.locals.set! 1 (.i32 link)}

/-- The actual flag-controlled predecessor selection, followed by its nonzero
fallthrough. The mask test is an initial loaded-word predicate. -/
theorem wp_select_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (raw link : UInt32) (post : Post)
    (h1 : frame.locals[1]? = some (.i32 raw)) (h2 : frame.locals[2]? = some (.i32 link))
    (hflag : raw &&& 2 = 0) (hlink : link ≠ 0)
    (hc : s.host.gas.Credits (9 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 9) limits stack (selectedFrame frame link) callers code)) rest post) :
    WP cfg (fuel + 9) (.next (atCode s limits stack frame callers
      ([.i32_const 0, .local_get 2, .local_get 1, .i32_const 2, .i32_binop .and,
        .select none, .local_tee 1, .i32_eqz, .br_if 0] ++ code))) (9 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let f := selectedFrame frame link
  have zero : Numeric.bool (link == 0) = 0 := by simp [Numeric.bool, hlink]
  have branch := wp_br_if_zero cfg fuel rest (paid s op 8) limits stack f callers code 0 post
    (paid_credits s op 8 _ (hc.mono (by dsimp [op]; omega))) hnext
  have branchNext : WP cfg (fuel + 1) (.next (atCode (paid s op 8) limits (stack.push (.i32 (Numeric.bool (link == 0)))) f callers
      (.br_if 0 :: code))) (op + rest) post := by simpa only [zero, op] using branch
  have eqz := wp_i32_eqz cfg (fuel + 1) (op + rest) (paid s op 7) limits stack f callers (.br_if 0 :: code) link post
    (paid_credits s op 7 _ (hc.mono (by dsimp [op]; omega))) branchNext
  have tee := wp_local_tee cfg (fuel + 2) (op + (op + rest)) (paid s op 6) limits stack frame callers
    (.i32_eqz :: .br_if 0 :: code) 1 (.i32 link) post (paid_credits s op 6 _ (hc.mono (by dsimp [op]; omega))) eqz
  have selectNext : WP cfg (fuel + 3) (.next (atCode (paid s op 6) limits
      (stack.push (if (raw &&& 2) ≠ 0 then Value.i32 0 else .i32 link)) frame callers
      (.local_tee 1 :: .i32_eqz :: .br_if 0 :: code))) (op + (op + (op + rest))) post := by
    simpa [hflag, op] using tee
  have select := wp_select cfg (fuel + 3) (op + (op + (op + rest))) (paid s op 5) limits stack frame callers
    (.local_tee 1 :: .i32_eqz :: .br_if 0 :: code) (.i32 0) (.i32 link) (raw &&& 2) post
    (paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))) selectNext
  have and := wp_i32_and cfg (fuel + 4) (op + (op + (op + (op + rest)))) (paid s op 4) limits
    ((stack.push (.i32 0)).push (.i32 link)) frame callers (.select none :: .local_tee 1 :: .i32_eqz :: .br_if 0 :: code) raw 2 post
    (paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))) select
  have con := wp_i32_const cfg (fuel + 5) (op + (op + (op + (op + (op + rest))))) (paid s op 3) limits
    (((stack.push (.i32 0)).push (.i32 link)).push (.i32 raw)) frame callers
    (.i32_binop .and :: .select none :: .local_tee 1 :: .i32_eqz :: .br_if 0 :: code) 2 post
    (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))) and
  have get1 := wp_local_get cfg (fuel + 6) (op + (op + (op + (op + (op + (op + rest)))))) (paid s op 2) limits
    ((stack.push (.i32 0)).push (.i32 link)) frame callers
    (.i32_const 2 :: .i32_binop .and :: .select none :: .local_tee 1 :: .i32_eqz :: .br_if 0 :: code) 1 (.i32 raw) post h1
    (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) con
  have get2 := wp_local_get cfg (fuel + 7) (op + (op + (op + (op + (op + (op + (op + rest))))))) (paid s op 1) limits
    (stack.push (.i32 0)) frame callers
    (.local_get 1 :: .i32_const 2 :: .i32_binop .and :: .select none :: .local_tee 1 :: .i32_eqz :: .br_if 0 :: code) 2 (.i32 link) post h2
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) get1
  have result := wp_i32_const cfg (fuel + 8) (op + (op + (op + (op + (op + (op + (op + (op + rest)))))))) s limits stack frame callers
    (.local_get 2 :: .local_get 1 :: .i32_const 2 :: .i32_binop .and :: .select none :: .local_tee 1 :: .i32_eqz :: .br_if 0 :: code) 0 post
    (hc.mono (by dsimp [op]; omega)) get2
  have ge : cfg.regularOpCost + (op + (op + (op + (op + (op + (op + (op + (op + rest)))))))) = 9 * cfg.regularOpCost + rest := by dsimp [op]; omega
  exact ValueReturnOuterBody.cast_phase cfg _ _ _ _ s limits stack frame callers _ _ post rfl ge rfl result

end WNear.Proofs.DeallocateListGuards
