import Proofs.VectorDropPositiveState
import Proofs.ValueReturnLazyReturn

/-! Exact post-deallocator control flow: f311 returns explicitly, f777 and
f747 finish their empty-result blocks and leave normally. -/
namespace WNear.Proofs.VectorDropPositive
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.VectorDrop
open WNear.Proofs.ValueReturnLazyLookup (wp_return_wasm)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP

/-- The real five-instruction administrative suffix after f237 returns.
Only f311's explicit return is charged; both block exits and both normal frame
exits are free interpreter steps. -/
theorem wp_unwind (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post)
    (hc : s.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore s cfg.regularOpCost) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits base.toArray (forwardLeaf frame.inst base.length p)
      ([capacityBlocked frame.inst base.length p, vectorBlocked frame.inst base.length p, {frame with code}] ++ callers) [.return]))
      (cfg.regularOpCost + rest) post := by
  let afterReturn := chargedStore s cfg.regularOpCost
  let saved := {frame with code}
  let vector := capacityFrame (vectorLeaf frame.inst base.length p) (capacity p)
  let cap := capacityLeaf frame.inst base.length p
  let blockedVector := vectorBlocked frame.inst base.length p
  let blockedCapacity := capacityBlocked frame.inst base.length p
  have cr := StorePair.charged_credits s cfg.regularOpCost rest hc
  have vectorLeave := wp_leave_wasm cfg fuel rest afterReturn limits base [] vector saved callers post rfl rfl rfl cr
  have vectorLeaveNext : WP cfg fuel (.next (atCode afterReturn limits (base ++ []).toArray saved callers saved.code)) rest post := by
    simpa only [afterReturn, saved, atCode, List.append_nil] using hnext
  have vectorLeft := vectorLeave vectorLeaveNext
  have vectorEnd := wp_end_label cfg (fuel + 1) rest afterReturn limits base.toArray vector (saved :: callers)
    {arity := 0, height := base.length, rest := [], loop := none} post cr
  have vectorEndNext : WP cfg (fuel + 1) (.next (atCode afterReturn limits base.toArray vector (saved :: callers) [])) rest post := by
    simpa only [List.append_nil] using vectorLeft
  have vectorEnded := vectorEnd vectorEndNext
  have capacityLeave := wp_leave_wasm cfg (fuel + 2) rest afterReturn limits base [] cap blockedVector (saved :: callers) post rfl rfl rfl cr
  have capacityLeaveNext : WP cfg (fuel + 2) (.next (atCode afterReturn limits (base ++ []).toArray blockedVector (saved :: callers) blockedVector.code)) rest post := by
    simpa only [blockedVector, vectorBlocked, emptyBlockFrame, vector, vectorLeaf, vectorFrame, capacityFrame, List.append_nil, Nat.add_assoc, Nat.reduceAdd] using vectorEnded
  have capacityLeft := capacityLeave capacityLeaveNext
  have capacityEnd := wp_end_label cfg (fuel + 3) rest afterReturn limits base.toArray cap (blockedVector :: saved :: callers)
    {arity := 0, height := base.length, rest := [], loop := none} post cr
  have capacityEndNext : WP cfg (fuel + 3) (.next (atCode afterReturn limits base.toArray cap (blockedVector :: saved :: callers) [])) rest post := by
    simpa only [List.append_nil, Nat.add_assoc, Nat.reduceAdd] using capacityLeft
  have capacityEnded := capacityEnd capacityEndNext
  have ret := wp_return_wasm cfg (fuel + 4) rest s limits base [] (forwardLeaf frame.inst base.length p) blockedCapacity (blockedVector :: saved :: callers) [] post rfl rfl hc
  have retNext : WP cfg (fuel + 4) (.next (atCode afterReturn limits (base ++ []).toArray blockedCapacity (blockedVector :: saved :: callers) blockedCapacity.code)) rest post := by
    simpa only [blockedCapacity, capacityBlocked, emptyBlockFrame, cap, capacityLeaf, tripleFrame, List.append_nil, Nat.add_assoc, Nat.reduceAdd] using capacityEnded
  have result := ret retNext
  simpa only [List.append_nil, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd, blockedCapacity, blockedVector, saved] using result
end WNear.Proofs.VectorDropPositive
