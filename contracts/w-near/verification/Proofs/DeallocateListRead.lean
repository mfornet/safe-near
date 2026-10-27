import Proofs.DeallocateListState

/-! The final current-memory reread in f575's second block. -/
namespace WNear.Proofs.DeallocateListRead
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
attribute [local irreducible] WP readI32

theorem wp_read (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (pointer : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hp : frame.locals[0]? = some (.i32 pointer))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : pointer.toNat + 8 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits stack
      {frame with locals := frame.locals.set! 1 (.i32 (readI32 memory (pointer.toNat + 4)))} callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack frame callers
      ([.local_get 0, .load .i32 none {align := 2, offset := 4}, .local_set 1] ++ code)))
      (3 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have set := wp_local_set cfg fuel rest (paid s op 2) limits stack frame callers code 1
    (.i32 (readI32 memory (pointer.toNat + 4))) post
    (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) hnext
  have hm1 : (paid s op 1).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hmem1 : (paid s op 1).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have load := wp_i32_load cfg (fuel + 1) (op + rest) (paid s op 1) limits stack frame callers
    (.local_set 1 :: code) {align := 2, offset := 4} pointer mi index memory post hm1 hi hmem1 hb
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) set
  have result := wp_local_get cfg (fuel + 2) (op + (op + rest)) s limits stack frame callers
    (.load .i32 none {align := 2, offset := 4} :: .local_set 1 :: code) 0 (.i32 pointer) post hp
    (hc.mono (by dsimp [op]; omega)) load
  have ge : cfg.regularOpCost + (op + (op + rest)) = 3 * cfg.regularOpCost + rest := by dsimp [op]; omega
  exact ValueReturnOuterBody.cast_phase cfg _ _ _ _ s limits stack frame callers _ _ post rfl ge rfl result

end WNear.Proofs.DeallocateListRead
