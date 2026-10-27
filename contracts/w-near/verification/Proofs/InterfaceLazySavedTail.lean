import Proofs.InterfaceLazyState

/-! Opaque composition boundary for saving and exiting the real lazy body. -/
namespace WNear.Proofs.InterfaceLazySavedTail
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open WNear.Proofs.InterfaceLazyState
set_option maxRecDepth 16384
set_option maxHeartbeats 600000

def after (s : Store NearState) (op : Nat) (p : Layout) := finalStore (saved s op p) op p

/-- Actual saveOld/result/guard/restore suffix, from an arbitrary pre-store. -/
theorem wp_tail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post)
    (hcell : frame.locals[0]? = some (.i32 p.cell))
    (hs : frame.locals[2]? = some (.i32 p.scratch))
    (hl : frame.locals[3]? = some (.i64 (oldLow p)))
    (hh : frame.locals[4]? = some (.i32 (oldHigh p)))
    (hz : frame.locals[1]? = some (.i32 (oldStatus p)))
    (hempty : oldStatus p = 0) (hn : 5 ≤ frame.locals.size)
    (hm : s.modules[frame.inst]? = some p.mi) (hi : p.mi.memAddrs[0]? = some p.memoryIndex)
    (hgi : p.mi.globalAddrs[0]? = some p.globalIndex) (hg : s.globals[p.globalIndex]? = some p.global)
    (hmem : s.mems[p.memoryIndex]? = some (statusMemory p))
    (hb : ((p.scratch + 16) + 12).toNat + 4 ≤ (statusMemory p).byteSize)
    (hb2 : p.scratch.toNat + 20 ≤ (InterfaceLazySaved.highMemory (statusMemory p) p.scratch (oldHigh p)).byteSize)
    (hb3 : p.scratch.toNat + 28 ≤ (InterfaceLazySaved.statusMemory (statusMemory p) p.scratch (oldStatus p) (oldHigh p)).byteSize)
    (hc : s.host.gas.Credits (25 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost p) limits
      (stack.push (.i32 (p.cell + 4))) (finalFrame frame p) callers code)) rest post) :
    WP cfg (fuel + 26) (.next (atCode s limits stack frame callers
      ((WNear.Binary.InterfaceLazy.saveOld ++ WNear.Binary.InterfaceLazy.result ++
        WNear.Binary.InterfaceLazy.guard ++ WNear.Binary.InterfaceLazy.restore) ++ code)))
      (25 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let written := saved s op p
  have cw : written.host.gas.Credits (12 * op + rest) := saved_credits s op _ p (hc.mono (by dsimp [op]; omega))
  have hm' : written.modules[frame.inst]? = some p.mi := by
    have fields := Resources.modules s written (saved_resources s op p)
    rw [fields]; exact hm
  have hg' : written.globals[p.globalIndex]? = some p.global := by
    have fields := Resources.globals s written (saved_resources s op p)
    rw [fields]; exact hg
  have hz' : frame.locals[1]? = some (.i32 0) := by rw [hempty] at hz; exact hz
  have finishNext : WP cfg fuel (.next (atCode (InterfaceLazyFinish.finalStore written cfg.regularOpCost p.globalIndex p.scratch)
      limits (stack.push (.i32 (p.cell + 4))) {frame with locals := frame.locals.set! 0 (.i32 (p.cell + 4))} callers code)) rest post := by
    simpa only [after, finalStore, written, op, finalFrame] using hnext
  have tail := InterfaceLazyFinish.wp_finish cfg fuel rest written limits stack frame callers code p.cell p.scratch p.mi p.globalIndex p.global post
    hcell hs hz' (by omega) hm' hgi hg' cw finishNext
  have tailNext : WP cfg (fuel + 13) (.next (atCode
      (InterfaceLazySaved.savedStore s cfg.regularOpCost p.memoryIndex p.scratch (oldStatus p) (oldHigh p) (oldLow p) (statusMemory p))
      limits stack frame callers ((WNear.Binary.InterfaceLazy.result ++ WNear.Binary.InterfaceLazy.guard ++ WNear.Binary.InterfaceLazy.restore) ++ code)))
      (12 * cfg.regularOpCost + rest) post := by
    simpa only [written, saved, op, List.append_assoc] using tail
  have result := InterfaceLazySaved.wp_save cfg (fuel + 13) (12 * cfg.regularOpCost + rest) s limits stack frame callers _
    p.scratch (oldStatus p) (oldHigh p) (oldLow p) p.mi p.memoryIndex (statusMemory p) post
    hs hh hl hz hm hi hmem hb hb2 hb3 (hc.mono (by omega)) tailNext
  have gas : 13 * cfg.regularOpCost + (12 * cfg.regularOpCost + rest) = 25 * cfg.regularOpCost + rest := by omega
  rw [gas] at result
  simpa only [Nat.add_assoc, Nat.reduceAdd, List.append_assoc] using result

end WNear.Proofs.InterfaceLazySavedTail
