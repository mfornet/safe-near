import Binary.SerializeFormatter
import Proofs.StorePairCallerState
import Proofs.StorePairAddresses
import Proofs.TotalSupplyRepresentation

/-! Actual pointer and U128 reads leading to the deployed decimal formatter.
These contracts stop before f902, and assume no decimal-conversion result. -/
namespace WNear.Proofs.SerializeFormatter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP

/-- f353 loads the actual pointer stored in its argument object. -/
theorem wp_box_prefix (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (box context : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hp : frame.locals[0]? = some (.i32 box)) (hcxt : frame.locals[1]? = some (.i32 context))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hb : box.toNat + 4 ≤ memory.byteSize) (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits
      ((stack.push (.i32 (readI32 memory box.toNat))).push (.i32 context)) frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack frame callers (WNear.Binary.SerializeFormatter.boxPrefix ++ code)))
      (3 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have hm1 : (paid s op 1).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hmem1 : (paid s op 1).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * op + rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel + 2) _ s limits stack frame callers _ 0 (.i32 box) post hp (hc.mono (by dsimp [op]; omega))
  rw [show 2 * op + rest = cfg.regularOpCost + (op + rest) by dsimp [op]; omega]
  apply wp_i32_load cfg (fuel + 1) _ (paid s op 1) limits stack frame callers _ {align := 2, offset := 0} box mi index memory post hm1 hi hmem1 (by simpa using hb)
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  simp only [Nat.add_zero]
  apply wp_local_get cfg fuel rest (paid s op 2) limits _ frame callers code 1 (.i32 context) post hcxt
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  · exact hnext

/-- f901 reads both original U128 words, sets the actual formatting flag one,
and passes its original context pointer to the pending decimal call. -/
theorem wp_u128_prefix (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (pointer context : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hp : frame.locals[0]? = some (.i32 pointer)) (hcxt : frame.locals[1]? = some (.i32 context))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hwidth : memory.byteSize ≤ 2 ^ 32) (hb : pointer.toNat + 16 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (8 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 8) limits
      ((((stack.push (.i64 (readI64 memory pointer.toNat))).push (.i64 (readI64 memory (pointer.toNat + 8)))).push (.i32 1)).push (.i32 context)) frame callers code)) rest post) :
    WP cfg (fuel + 8) (.next (atCode s limits stack frame callers (WNear.Binary.SerializeFormatter.u128Prefix ++ code)))
      (8 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have address := StorePairAddresses.add_eight_memory memory pointer hwidth hb
  have hm1 : (paid s op 1).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hmem1 : (paid s op 1).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have hm5 : (paid s op 5).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hmem5 : (paid s op 5).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have highBound : (pointer + 8).toNat + 0 + 8 ≤ memory.byteSize := by rw [address]; omega
  rw [show 8 * cfg.regularOpCost + rest = cfg.regularOpCost + (7 * op + rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel + 7) _ s limits stack frame callers _ 0 (.i32 pointer) post hp (hc.mono (by dsimp [op]; omega))
  rw [show 7 * op + rest = cfg.regularOpCost + (6 * op + rest) by dsimp [op]; omega]
  apply wp_i64_load cfg (fuel + 6) _ (paid s op 1) limits stack frame callers _ {align := 3, offset := 0} pointer mi index memory post hm1 hi hmem1 (by change pointer.toNat + 0 + 8 ≤ memory.byteSize; omega)
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  simp only [Nat.add_zero]
  rw [show 6 * op + rest = cfg.regularOpCost + (5 * op + rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel + 5) _ (paid s op 2) limits _ frame callers _ 0 (.i32 pointer) post hp
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  rw [show 5 * op + rest = cfg.regularOpCost + (4 * op + rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel + 4) _ (paid s op 3) limits _ frame callers _ 8 post
  · exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  rw [show 4 * op + rest = cfg.regularOpCost + (3 * op + rest) by dsimp [op]; omega]
  apply wp_i32_add cfg (fuel + 3) _ (paid s op 4) limits _ frame callers _ pointer 8 post
  · exact paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
  rw [show 3 * op + rest = cfg.regularOpCost + (2 * op + rest) by dsimp [op]; omega]
  apply wp_i64_load cfg (fuel + 2) _ (paid s op 5) limits _ frame callers _ {align := 3, offset := 0} (pointer + 8) mi index memory post hm5 hi hmem5 highBound
  · exact paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  simp only [address, Nat.add_zero]
  rw [show 2 * op + rest = cfg.regularOpCost + (op + rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel + 1) _ (paid s op 6) limits _ frame callers _ 1 post
  · exact paid_credits s op 6 _ (hc.mono (by dsimp [op]; omega))
  apply wp_local_get cfg fuel rest (paid s op 7) limits _ frame callers code 1 (.i32 context) post hcxt
  · exact paid_credits s op 7 _ (hc.mono (by dsimp [op]; omega))
  · exact hnext

/-- The words actually passed to f902 represent the original model value. -/
theorem decimal_arguments_value (memory : Memory) (pointer : UInt32) (value : Nat)
    (h : TotalSupply.U128At memory pointer.toNat value) :
    (readI64 memory pointer.toNat).toNat + 2 ^ 64 * (readI64 memory (pointer.toNat + 8)).toNat = value := h
end WNear.Proofs.SerializeFormatter
