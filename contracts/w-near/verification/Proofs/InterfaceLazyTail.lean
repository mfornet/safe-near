import Proofs.InterfaceLazySavedTail

/-! Complete actual lazy-body suffix after the initializer has returned. -/
namespace WNear.Proofs.InterfaceLazyTail
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.InterfaceLazyState
set_option maxRecDepth 16384
set_option maxHeartbeats 600000

/-- Native bounds refer to the real sequential memories. No disjointness or
precomputed readback is assumed. Empty refers to the real old-status load. -/
structure Bounds (p : Layout) : Prop where
  highCell : p.cell.toNat + 12 ≤ p.memory.byteSize
  highScratch : p.scratch.toNat + 8 ≤ p.memory.byteSize
  wordCell : (p.cell + 12).toNat + 4 ≤ (highMemory p).byteSize
  wordScratch : (p.scratch + 8).toNat + 4 ≤ (highMemory p).byteSize
  statusCell : p.cell.toNat + 4 ≤ (wordMemory p).byteSize
  saveHigh : ((p.scratch + 16) + 12).toNat + 4 ≤ (statusMemory p).byteSize
  saveStatus : p.scratch.toNat + 20 ≤ (InterfaceLazySaved.highMemory (statusMemory p) p.scratch (oldHigh p)).byteSize
  saveLow : p.scratch.toNat + 28 ≤ (InterfaceLazySaved.statusMemory (statusMemory p) p.scratch (oldStatus p) (oldHigh p)).byteSize
  empty : oldStatus p = 0

def statusAfter (s : Store NearState) (op : Nat) (p : Layout) := InterfaceLazySavedTail.after (status s op p) op p

theorem wp_status_tail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post)
    (hcell : frame.locals[0]? = some (.i32 p.cell)) (hs : frame.locals[2]? = some (.i32 p.scratch))
    (hl : frame.locals[3]? = some (.i64 (oldLow p))) (hh : frame.locals[4]? = some (.i32 (oldHigh p)))
    (hn : 5 ≤ frame.locals.size) (hm : s.modules[frame.inst]? = some p.mi)
    (hi : p.mi.memAddrs[0]? = some p.memoryIndex) (hgi : p.mi.globalAddrs[0]? = some p.globalIndex)
    (hg : s.globals[p.globalIndex]? = some p.global) (hmem : s.mems[p.memoryIndex]? = some (wordMemory p))
    (hb : Bounds p) (hc : s.host.gas.Credits (31 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (statusAfter s cfg.regularOpCost p) limits
      (stack.push (.i32 (p.cell + 4))) (finalFrame (statusFrame frame p) p) callers code)) rest post) :
    WP cfg (fuel + 32) (.next (atCode s limits stack frame callers
      ((WNear.Binary.InterfaceLazy.status ++ WNear.Binary.InterfaceLazy.saveOld ++ WNear.Binary.InterfaceLazy.result ++
        WNear.Binary.InterfaceLazy.guard ++ WNear.Binary.InterfaceLazy.restore) ++ code)))
      (31 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let written := status s op p
  let updated := statusFrame frame p
  have h1 : 1 < frame.locals.size := by omega
  have h0 : updated.locals[0]? = some (.i32 p.cell) := by
    simpa only [updated, statusFrame, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (by decide : 1 ≠ 0)] using hcell
  have h2 : updated.locals[2]? = some (.i32 p.scratch) := by
    simpa only [updated, statusFrame, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (by decide : 1 ≠ 2)] using hs
  have h3 : updated.locals[3]? = some (.i64 (oldLow p)) := by
    simpa only [updated, statusFrame, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (by decide : 1 ≠ 3)] using hl
  have h4 : updated.locals[4]? = some (.i32 (oldHigh p)) := by
    simpa only [updated, statusFrame, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (by decide : 1 ≠ 4)] using hh
  have hz : updated.locals[1]? = some (.i32 (oldStatus p)) := by
    simp only [updated, statusFrame, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt h1]
  have hn' : 5 ≤ updated.locals.size := by simpa only [updated, statusFrame, Array.size_set!] using hn
  have hm' : written.modules[updated.inst]? = some p.mi := by
    have fields := Resources.modules s written (status_resources s op p)
    rw [fields]; simpa only [updated, statusFrame] using hm
  have hg' : written.globals[p.globalIndex]? = some p.global := by
    have fields := Resources.globals s written (status_resources s op p)
    rw [fields]; exact hg
  have mem := status_memory s op p hmem
  have credits := status_credits s op (25 * op + rest) p (hc.mono (by dsimp [op]; omega))
  have tailNext : WP cfg fuel (.next (atCode (InterfaceLazySavedTail.after written cfg.regularOpCost p) limits
      (stack.push (.i32 (p.cell + 4))) (finalFrame updated p) callers code)) rest post := by
    simpa only [statusAfter, written, updated, op] using hnext
  have tail := InterfaceLazySavedTail.wp_tail cfg fuel rest written limits stack updated callers code p post
    h0 h2 h3 h4 hz hb.empty hn' hm' hi hgi hg' mem hb.saveHigh hb.saveStatus hb.saveLow credits tailNext
  have next : WP cfg (fuel + 26) (.next (atCode (InterfaceLazyBody.replacedStatus s cfg.regularOpCost p.memoryIndex p.cell (wordMemory p))
      limits stack {frame with locals := frame.locals.set! 1 (.i32 (readI32 (wordMemory p) p.cell.toNat))} callers
      ((WNear.Binary.InterfaceLazy.saveOld ++ WNear.Binary.InterfaceLazy.result ++ WNear.Binary.InterfaceLazy.guard ++ WNear.Binary.InterfaceLazy.restore) ++ code)))
      (25 * cfg.regularOpCost + rest) post := by
    simpa only [written, status, updated, statusFrame, oldStatus, op] using tail
  have result := InterfaceLazyBody.wp_status cfg (fuel + 26) (25 * cfg.regularOpCost + rest) s limits stack frame callers _
    p.cell p.mi p.memoryIndex (wordMemory p) post hcell hm hi hmem hb.statusCell (hc.mono (by omega)) next
  have gas : 6 * cfg.regularOpCost + (25 * cfg.regularOpCost + rest) = 31 * cfg.regularOpCost + rest := by omega
  rw [gas] at result
  simpa only [Nat.add_assoc, Nat.reduceAdd, List.append_assoc] using result

def wordAfter (s : Store NearState) (op : Nat) (p : Layout) := statusAfter (word s op p) op p

theorem wp_word_tail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post)
    (hcell : frame.locals[0]? = some (.i32 p.cell)) (hs : frame.locals[2]? = some (.i32 p.scratch))
    (hl : frame.locals[3]? = some (.i64 (oldLow p)))
    (hn : 5 ≤ frame.locals.size) (hm : s.modules[frame.inst]? = some p.mi)
    (hi : p.mi.memAddrs[0]? = some p.memoryIndex) (hgi : p.mi.globalAddrs[0]? = some p.globalIndex)
    (hg : s.globals[p.globalIndex]? = some p.global) (hmem : s.mems[p.memoryIndex]? = some (highMemory p))
    (hb : Bounds p) (hc : s.host.gas.Credits (43 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (wordAfter s cfg.regularOpCost p) limits
      (stack.push (.i32 (p.cell + 4))) (finalFrame (statusFrame (wordFrame frame p) p) p) callers code)) rest post) :
    WP cfg (fuel + 44) (.next (atCode s limits stack frame callers
      ((WNear.Binary.InterfaceLazy.exchange32 ++ WNear.Binary.InterfaceLazy.status ++ WNear.Binary.InterfaceLazy.saveOld ++
        WNear.Binary.InterfaceLazy.result ++ WNear.Binary.InterfaceLazy.guard ++ WNear.Binary.InterfaceLazy.restore) ++ code)))
      (43 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let written := word s op p
  let updated := wordFrame frame p
  have h4 : 4 < (frame.locals.set! 1 (.i32 (p.cell + 12))).size := by simpa only [Array.size_set!] using (show 4 < frame.locals.size by omega)
  simp only [Array.set!_eq_setIfInBounds] at h4
  have hh : updated.locals[4]? = some (.i32 (oldHigh p)) := by
    simp only [updated, wordFrame, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt h4]
  have h0 : updated.locals[0]? = some (.i32 (p.cell)) := by
    simpa only [updated, wordFrame, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne (by decide : 4 ≠ 0), Array.getElem?_setIfInBounds_ne (by decide : 1 ≠ 0)] using hcell
  have h2 : updated.locals[2]? = some (.i32 (p.scratch)) := by
    simpa only [updated, wordFrame, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne (by decide : 4 ≠ 2), Array.getElem?_setIfInBounds_ne (by decide : 1 ≠ 2)] using hs
  have h3 : updated.locals[3]? = some (.i64 (oldLow p)) := by
    simpa only [updated, wordFrame, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne (by decide : 4 ≠ 3), Array.getElem?_setIfInBounds_ne (by decide : 1 ≠ 3)] using hl
  have hn' : 5 ≤ updated.locals.size := by simpa only [updated, wordFrame, Array.size_set!] using hn
  have hm' : written.modules[updated.inst]? = some p.mi := by
    have fields := Resources.modules s written (word_resources s op p)
    rw [fields]; simpa only [updated, wordFrame] using hm
  have hg' : written.globals[p.globalIndex]? = some p.global := by
    have fields := Resources.globals s written (word_resources s op p)
    rw [fields]; exact hg
  have mem := word_memory s op p hmem
  have credits := word_credits s op (31 * op + rest) p (hc.mono (by dsimp [op]; omega))
  have tailNext : WP cfg fuel (.next (atCode (statusAfter written cfg.regularOpCost p) limits
      (stack.push (.i32 (p.cell + 4))) (finalFrame (statusFrame updated p) p) callers code)) rest post := by
    simpa only [wordAfter, written, updated, op] using hnext
  have tail := wp_status_tail cfg fuel rest written limits stack updated callers code p post h0 h2 h3 hh hn' hm' hi hgi hg' mem hb credits tailNext
  have next : WP cfg (fuel + 32) (.next (atCode (InterfaceLazyBody.exchanged32 s cfg.regularOpCost p.memoryIndex p.cell p.scratch (highMemory p))
      limits stack {frame with locals := ((frame.locals.set! 1 (.i32 (p.cell + 12))).set! 4 (.i32 (readI32 (highMemory p) (p.cell + 12).toNat)))} callers
      ((WNear.Binary.InterfaceLazy.status ++ WNear.Binary.InterfaceLazy.saveOld ++ WNear.Binary.InterfaceLazy.result ++
        WNear.Binary.InterfaceLazy.guard ++ WNear.Binary.InterfaceLazy.restore) ++ code))) (31 * cfg.regularOpCost + rest) post := by
    simpa only [written, word, updated, wordFrame, oldHigh, op] using tail
  have result := InterfaceLazyBody.wp_exchange32 cfg (fuel + 32) (31 * cfg.regularOpCost + rest) s limits stack frame callers _
    p.cell p.scratch p.mi p.memoryIndex (highMemory p) post hcell hs hn hm hi hmem hb.wordCell hb.wordScratch (hc.mono (by omega)) next
  have gas : 12 * cfg.regularOpCost + (31 * cfg.regularOpCost + rest) = 43 * cfg.regularOpCost + rest := by omega
  rw [gas] at result
  simpa only [Nat.add_assoc, Nat.reduceAdd, List.append_assoc] using result

def after (s : Store NearState) (op : Nat) (p : Layout) := wordAfter (high s op p) op p

def afterFrame (frame : CallFrame) (p : Layout) := finalFrame (statusFrame (wordFrame (highFrame frame p) p) p) p

/-- All actual post-initializer instructions, from an arbitrary pre-store.
The only semantic continuation begins after the complete fifty-one-step suffix. -/
theorem wp_tail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post)
    (hcell : frame.locals[0]? = some (.i32 p.cell)) (hs : frame.locals[2]? = some (.i32 p.scratch))
    (hn : 5 ≤ frame.locals.size) (hm : s.modules[frame.inst]? = some p.mi)
    (hi : p.mi.memAddrs[0]? = some p.memoryIndex) (hgi : p.mi.globalAddrs[0]? = some p.globalIndex)
    (hg : s.globals[p.globalIndex]? = some p.global) (hmem : s.mems[p.memoryIndex]? = some p.memory)
    (hb : Bounds p) (hc : s.host.gas.Credits (50 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost p) limits
      (stack.push (.i32 (p.cell + 4))) (afterFrame frame p) callers code)) rest post) :
    WP cfg (fuel + 51) (.next (atCode s limits stack frame callers
      ((WNear.Binary.InterfaceLazy.exchange64 ++ WNear.Binary.InterfaceLazy.exchange32 ++ WNear.Binary.InterfaceLazy.status ++
        WNear.Binary.InterfaceLazy.saveOld ++ WNear.Binary.InterfaceLazy.result ++ WNear.Binary.InterfaceLazy.guard ++ WNear.Binary.InterfaceLazy.restore) ++ code)))
      (50 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let written := high s op p
  let updated := highFrame frame p
  have h3 : 3 < frame.locals.size := by omega
  have hl : updated.locals[3]? = some (.i64 (oldLow p)) := by
    simp only [updated, highFrame, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt h3]
  have h0 : updated.locals[0]? = some (.i32 (p.cell)) := by
    simpa only [updated, highFrame, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne (by decide : 3 ≠ 0)] using hcell
  have h2 : updated.locals[2]? = some (.i32 (p.scratch)) := by
    simpa only [updated, highFrame, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne (by decide : 3 ≠ 2)] using hs
  have hn' : 5 ≤ updated.locals.size := by simpa only [updated, highFrame, Array.size_set!] using hn
  have hm' : written.modules[updated.inst]? = some p.mi := by
    have fields := Resources.modules s written (high_resources s op p)
    rw [fields]; simpa only [updated, highFrame] using hm
  have hg' : written.globals[p.globalIndex]? = some p.global := by
    have fields := Resources.globals s written (high_resources s op p)
    rw [fields]; exact hg
  have mem := high_memory s op p hmem
  have credits := high_credits s op (43 * op + rest) p (hc.mono (by dsimp [op]; omega))
  have tailNext : WP cfg fuel (.next (atCode (wordAfter written cfg.regularOpCost p) limits
      (stack.push (.i32 (p.cell + 4))) (finalFrame (statusFrame (wordFrame updated p) p) p) callers code)) rest post := by
    simpa only [after, afterFrame, written, updated, op] using hnext
  have tail := wp_word_tail cfg fuel rest written limits stack updated callers code p post h0 h2 hl hn' hm' hi hgi hg' mem hb credits tailNext
  have next : WP cfg (fuel + 44) (.next (atCode (InterfaceLazyBody.exchanged64 s cfg.regularOpCost p.memoryIndex p.cell p.scratch p.memory)
      limits stack {frame with locals := frame.locals.set! 3 (.i64 (readI64 p.memory (p.cell.toNat + 4)))} callers
      ((WNear.Binary.InterfaceLazy.exchange32 ++ WNear.Binary.InterfaceLazy.status ++ WNear.Binary.InterfaceLazy.saveOld ++ WNear.Binary.InterfaceLazy.result ++
        WNear.Binary.InterfaceLazy.guard ++ WNear.Binary.InterfaceLazy.restore) ++ code))) (43 * cfg.regularOpCost + rest) post := by
    simpa only [written, high, updated, highFrame, oldLow, op] using tail
  have result := InterfaceLazyBody.wp_exchange64 cfg (fuel + 44) (43 * cfg.regularOpCost + rest) s limits stack frame callers _
    p.cell p.scratch p.mi p.memoryIndex p.memory post hcell hs hm hi hmem hb.highCell hb.highScratch (hc.mono (by omega)) next
  have gas : 7 * cfg.regularOpCost + (43 * cfg.regularOpCost + rest) = 50 * cfg.regularOpCost + rest := by omega
  rw [gas] at result
  simpa only [Nat.add_assoc, Nat.reduceAdd, List.append_assoc] using result

end WNear.Proofs.InterfaceLazyTail
