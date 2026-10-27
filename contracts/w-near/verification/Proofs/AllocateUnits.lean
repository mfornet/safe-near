import Binary.AllocateUnits
import NearVM.MeteredWordRules
import Init.Data.UInt.Bitwise
import Proofs.ValueReturnOuterBody
import Proofs.StorePairCaller

/-! Checked size scaling in the actual allocator helper572. -/
namespace WNear.Proofs.AllocateUnits
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
open WNear.Binary.AllocateUnits
set_option maxRecDepth 16384
attribute [local irreducible] WP

theorem mask_of_bound (value : UInt32) (h : value.toNat < 2^30) :
    value &&& 1073741823 = value := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and]
  change value.toNat &&& (2^30 - 1) = value.toNat
  exact Nat.and_two_pow_sub_one_of_lt_two_pow h

theorem wp_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (value : UInt32) (post : Post)
    (hv : frame.locals[0]? = some (.i32 value)) (hb : value.toNat < 2^30)
    (hc : s.host.gas.Credits (6 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 6) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 7) (.next (atCode s limits stack frame callers
      (.block .empty (unitsGuard ++ unitsPanic) :: code))) (6 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let bf := emptyBlockFrame frame stack.size code
  apply wp_block_empty cfg (fuel + 6) _ s limits stack frame callers _ code post hc
  rw [show 6 * cfg.regularOpCost + rest = cfg.regularOpCost + (5 * op + rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel + 5) _ s limits stack bf callers _ 0 (.i32 value) post hv (hc.mono (by dsimp [op]; omega))
  rw [show 5 * op + rest = cfg.regularOpCost + (4 * op + rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel + 4) _ (paid s op 1) limits (stack.push (.i32 value)) bf callers _ 1073741823 post
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  rw [show 4 * op + rest = cfg.regularOpCost + (3 * op + rest) by dsimp [op]; omega]
  apply wp_i32_and cfg (fuel + 3) _ (paid s op 2) limits stack bf callers _ value 1073741823 post
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  rw [show 3 * op + rest = cfg.regularOpCost + (2 * op + rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel + 2) _ (paid s op 3) limits (stack.push (.i32 (value &&& 1073741823))) bf callers _ 0 (.i32 value) post hv
  · exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  rw [show 2 * op + rest = cfg.regularOpCost + (op + rest) by dsimp [op]; omega]
  apply wp_i32_relop cfg (fuel + 1) _ (paid s op 4) limits stack bf callers _ .eq (value &&& 1073741823) value post
  · exact paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
  have branch := wp_br_if_block_nonzero cfg fuel rest (paid s op 5) limits stack frame callers code
    unitsPanic 1 post (by decide) (paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))) hnext
  simpa only [Numeric.irelop32, mask_of_bound value hb, BEq.rfl, Numeric.bool, ite_true, bf, op, paid,
    List.append_eq, List.cons_append, List.nil_append] using branch

theorem wp_tail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (value : UInt32) (post : Post)
    (hv : frame.locals[0]? = some (.i32 value))
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits
      (stack.push (.i32 (value <<< (2 : UInt32)))) frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack frame callers (unitsTail ++ code)))
      (3 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * op + rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel + 2) _ s limits stack frame callers _ 0 (.i32 value) post hv (hc.mono (by dsimp [op]; omega))
  rw [show 2 * op + rest = cfg.regularOpCost + (op + rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel + 1) _ (paid s op 1) limits (stack.push (.i32 value)) frame callers _ 2 post
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  apply wp_i32_binop_ok cfg fuel rest (paid s op 2) limits stack frame callers code .shl value 2 (value <<< (2 : UInt32)) post rfl
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  · simpa only [paid, op] using hnext

theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (value : UInt32) (post : Post)
    (hv : frame.locals[0]? = some (.i32 value)) (hb : value.toNat < 2^30)
    (hc : s.host.gas.Credits (9 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 9) limits
      (stack.push (.i32 (value <<< (2 : UInt32)))) frame callers code)) rest post) :
    WP cfg (fuel + 10) (.next (atCode s limits stack frame callers (unitsBody ++ code)))
      (9 * cfg.regularOpCost + rest) post := by
  have tail := wp_tail cfg fuel rest (paid s cfg.regularOpCost 6) limits stack frame callers code value post hv
    (paid_credits s cfg.regularOpCost 6 _ (hc.mono (by omega))) (by simpa only [paid] using hnext)
  have guard := wp_guard cfg (fuel + 3) (3 * cfg.regularOpCost + rest) s limits stack frame callers
    (unitsTail ++ code) value post hv hb (hc.mono (by omega)) tail
  simpa only [unitsBody, List.cons_append, List.nil_append,
    show 6 * cfg.regularOpCost + (3 * cfg.regularOpCost + rest) = 9 * cfg.regularOpCost + rest by omega,
    show fuel + 3 + 7 = fuel + 10 by omega] using guard

end WNear.Proofs.AllocateUnits
