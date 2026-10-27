import Proofs.VectorDropPositive237Call
import Proofs.VectorDropPositivePrefix
import Proofs.VectorDropPositiveUnwind
import Proofs.VectorDropPositiveCredits

/-! Complete positive vector destruction through the actual allocator path. -/
namespace WNear.Proofs.VectorDropPositive
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.VectorDrop
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP

/-- Full actual f68 positive body, including all nested wrappers and the real
previous-free heap-coalescing branch of f582. Native and code premises concern
only the original store or explicitly computed sequential memory reads. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (q : DeallocateCore.Layout) (address68 address237 address582 : Nat) (post : Post)
    (hr : Resources s frame.inst p q address68 address237 address582)
    (hv : frame.locals[0]? = some (.i32 p.vector)) (hd : callers.length + 7 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (309 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (bodyAfter s cfg.regularOpCost q) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 228) (.next (atCode s limits base.toArray frame callers (WNear.Binary.VectorDrop.body68 ++ code)))
      (309 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let pending := before237 s op
  let returned := VectorDropPositive237.callAfter pending op q
  let saved := {frame with code}
  let wrappers := [capacityBlocked frame.inst base.length p, vectorBlocked frame.inst base.length p, saved] ++ callers
  have cp := before237_credits s op (247 * op + rest) (hc.mono (by dsimp [op]; omega))
  have cd := VectorDropPositive237.callAfter_credits pending op (op + rest) q (cp.mono (by omega))
  have unwindNext : WP cfg fuel (.next (atCode (chargedStore returned cfg.regularOpCost) limits base.toArray frame callers code)) rest post := by
    simpa only [bodyAfter, returned, pending, op] using hnext
  have unwind := wp_unwind cfg fuel rest returned limits base frame callers code p post cd unwindNext
  have ready := heap_before237 s frame.inst op q address582 hr.heap
  have hi : q.mi.funcAddrs[237]? = some address237 := by
    rw [hr.module_eq s frame.inst p q address68 address237 address582]
    exact hr.index237
  have hf : pending.funcs[address237]? = some (.wasm WNear.Binary.Deallocate.entrySignature (forwardLeaf frame.inst base.length p).inst WNear.Binary.Deallocate.entryFunction) := by
    simpa only [pending, before237, before311, before777, before747, StorePairCaller.paid, entered, tripleEntry, chargedStore, forwardLeaf, tripleFrame] using hr.function237
  have callNext : WP cfg (fuel + 5) (.next (atCode (VectorDropPositive237.callAfter pending op q) limits base.toArray
      (forwardLeaf frame.inst base.length p) wrappers [.return])) (op + rest) post := by
    simpa only [returned, wrappers, saved, op] using unwind
  have call := VectorDropPositive237.wp_call cfg (fuel + 5) (op + rest) pending limits base (forwardLeaf frame.inst base.length p) wrappers [.return] q address237 address582 post
    ready hi hf (by simpa only [wrappers, List.length_append, List.length_cons, List.length_nil, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, Nat.reduceAdd] using hd)
    (cp.mono (by dsimp [op]; omega)) callNext
  have prefixNext : WP cfg (fuel + 201) (.next (atCode (before237 s op) limits (base ++ arguments p).toArray
      (forwardLeaf frame.inst base.length p) ([capacityBlocked frame.inst base.length p, vectorBlocked frame.inst base.length p, {frame with code}] ++ callers)
      [.call 237, .return])) (247 * op + rest) post := by
    simpa only [pending, wrappers, saved, arguments, hr.pointer, hr.length, hr.alignment, Nat.add_assoc, Nat.reduceAdd,
      show 246 * cfg.regularOpCost + (op + rest) = 247 * op + rest by dsimp [op]; omega] using call
  have prefixRun := wp_to237 cfg (fuel + 201) (247 * op + rest) s limits base frame callers code p post hr.vector hv (by omega)
    (hc.mono (by dsimp [op]; omega)) prefixNext
  simpa only [Nat.add_assoc, Nat.reduceAdd,
    show 62 * cfg.regularOpCost + (247 * op + rest) = 309 * cfg.regularOpCost + rest by dsimp [op]; omega] using prefixRun
end WNear.Proofs.VectorDropPositive
