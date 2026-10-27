import Binary.InterfaceLazy
import Proofs.InterfaceStack
import NearVM.MeteredI32MemoryRules

/-! Exact scalar phases of deployed lazy interface initialization. Each capsule
keeps arbitrary caller frames, operand prefix and continuation. -/
namespace WNear.Proofs.InterfaceLazyBody
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000

def exchanged64 (s : Store NearState) (op index : Nat) (cell scratch : UInt32) (memory : Memory) :=
  storeI64 (paid s op 7) index (cell.toNat + 4) memory (readI64 memory scratch.toNat)

/-- Save the old two-word payload and copy the initialized eight bytes. -/
theorem wp_exchange64 (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (cell scratch : UInt32) (mi : ModuleInst) (index : Nat)
    (memory : Memory) (post : Post)
    (hcell : frame.locals[0]? = some (.i32 cell))
    (hscratch : frame.locals[2]? = some (.i32 scratch))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory)
    (hb : cell.toNat + 12 ≤ memory.byteSize) (hs : scratch.toNat + 8 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (7 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (exchanged64 s cfg.regularOpCost index cell scratch memory)
      limits stack {frame with locals := frame.locals.set! 3 (.i64 (readI64 memory (cell.toNat + 4)))} callers code)) rest post) :
    WP cfg (fuel + 7) (.next (atCode s limits stack frame callers
      (WNear.Binary.InterfaceLazy.exchange64 ++ code))) (7 * cfg.regularOpCost + rest) post := by
  let updated := {frame with locals := frame.locals.set! 3 (.i64 (readI64 memory (cell.toNat + 4)))}
  have ha : updated.locals[0]? = some (.i32 cell) := by simpa only [updated, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (by decide : 3 ≠ 0)] using hcell
  have hs' : updated.locals[2]? = some (.i32 scratch) := by simpa only [updated, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (by decide : 3 ≠ 2)] using hscratch
  have hs0 : scratch.toNat + 0 + 8 ≤ memory.byteSize := hs
  rw [show 7 * cfg.regularOpCost + rest = cfg.regularOpCost + (6 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 6) (6 * cfg.regularOpCost + rest) s limits stack frame callers _ 0 (.i32 cell) post hcell
  · exact hc.mono (by omega)
  rw [show 6 * cfg.regularOpCost + rest = cfg.regularOpCost + (5 * cfg.regularOpCost + rest) by omega]
  apply wp_i64_load cfg (fuel + 5) (5 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 1) limits stack frame callers _ {align := 2, offset := 4} cell mi index memory post hm hi hmem (by omega)
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_local_set cfg (fuel + 4) (4 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 2) limits stack frame callers _ 3 (.i64 (readI64 memory (cell.toNat + 4))) post
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 3) (3 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 3) limits stack updated callers _ 0 (.i32 cell) post ha
  · exact paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) (2 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 4) limits _ updated callers _ 2 (.i32 scratch) post hs'
  · exact paid_credits s cfg.regularOpCost 4 _ (hc.mono (by omega))
  have hm5 : (paid s cfg.regularOpCost 5).modules[updated.inst]? = some mi := by simpa only [paid, chargedStore, updated] using hm
  have hmem5 : (paid s cfg.regularOpCost 5).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (1 * cfg.regularOpCost + rest) by omega]
  apply wp_i64_load cfg (fuel + 1) (1 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 5) limits (stack.push (.i32 cell)) updated callers (.store .i64 none {align := 2, offset := 4} :: code) {align := 3, offset := 0} scratch mi index memory post hm5 hi hmem5 hs0
  · exact paid_credits s cfg.regularOpCost 5 _ (hc.mono (by omega))
  have hm6 : (paid s cfg.regularOpCost 6).modules[updated.inst]? = some mi := by simpa only [paid, chargedStore, updated] using hm
  have hmem6 : (paid s cfg.regularOpCost 6).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  rw [show 1 * cfg.regularOpCost + rest = cfg.regularOpCost + rest by omega]
  apply wp_i64_store cfg fuel rest (paid s cfg.regularOpCost 6) limits stack updated callers code {align := 2, offset := 4} cell (readI64 memory scratch.toNat) mi index memory post hm6 hi hmem6 (by omega)
  · exact paid_credits s cfg.regularOpCost 6 _ (hc.mono (by omega))
  · exact hnext

def exchanged32 (s : Store NearState) (op index : Nat) (cell scratch : UInt32) (memory : Memory) :=
  storeI32 (paid s op 12) index (cell + 12).toNat memory (readI32 memory (scratch + 8).toNat)

/-- Exact exchange of the third interface word; the source is read as it stands
in the current memory, including any previous aliasing writes. -/
theorem wp_exchange32 (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (cell scratch : UInt32) (mi : ModuleInst) (index : Nat)
    (memory : Memory) (post : Post)
    (hcell : frame.locals[0]? = some (.i32 cell))
    (hscratch : frame.locals[2]? = some (.i32 scratch))
    (hn : 5 ≤ frame.locals.size)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory)
    (hb : (cell + 12).toNat + 4 ≤ memory.byteSize)
    (hs : (scratch + 8).toNat + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (12 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (exchanged32 s cfg.regularOpCost index cell scratch memory)
      limits stack {frame with locals := ((frame.locals.set! 1 (.i32 (cell + 12))).set! 4
        (.i32 (readI32 memory (cell + 12).toNat)))} callers code)) rest post) :
    WP cfg (fuel + 12) (.next (atCode s limits stack frame callers
      (WNear.Binary.InterfaceLazy.exchange32 ++ code))) (12 * cfg.regularOpCost + rest) post := by
  let first := {frame with locals := frame.locals.set! 1 (.i32 (cell + 12))}
  let second := {first with locals := first.locals.set! 4 (.i32 (readI32 memory (cell + 12).toNat))}
  have h1 : 1 < frame.locals.size := by omega
  have hslot : second.locals[1]? = some (.i32 (cell + 12)) := by
    simp only [second, first, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne (by decide : 4 ≠ 1), Array.getElem?_setIfInBounds_self_of_lt h1]
  have hscratch' : second.locals[2]? = some (.i32 scratch) := by
    simpa only [second, first, Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne (by decide : 4 ≠ 2),
      Array.getElem?_setIfInBounds_ne (by decide : 1 ≠ 2)] using hscratch
  have hm4 : (paid s cfg.regularOpCost 4).modules[first.inst]? = some mi := by simpa only [paid, chargedStore, first] using hm
  have hm10 : (paid s cfg.regularOpCost 10).modules[second.inst]? = some mi := by simpa only [paid, chargedStore, first, second] using hm
  have hm11 : (paid s cfg.regularOpCost 11).modules[second.inst]? = some mi := by simpa only [paid, chargedStore, first, second] using hm
  have hmem4 : (paid s cfg.regularOpCost 4).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have hmem10 : (paid s cfg.regularOpCost 10).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  have hmem11 : (paid s cfg.regularOpCost 11).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  rw [show 12 * cfg.regularOpCost + rest = cfg.regularOpCost + (11 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 11) (11 * cfg.regularOpCost + rest) s limits stack frame callers _ 0 (.i32 cell) post hcell
  · exact hc.mono (by omega)
  rw [show 11 * cfg.regularOpCost + rest = cfg.regularOpCost + (10 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 10) (10 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 1) limits _ frame callers _ 12 post
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  rw [show 10 * cfg.regularOpCost + rest = cfg.regularOpCost + (9 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_add cfg (fuel + 9) (9 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 2) limits stack frame callers _ cell 12 post
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  rw [show 9 * cfg.regularOpCost + rest = cfg.regularOpCost + (8 * cfg.regularOpCost + rest) by omega]
  apply wp_local_tee cfg (fuel + 8) (8 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 3) limits stack frame callers _ 1 (.i32 (cell + 12)) post
  · exact paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))
  rw [show 8 * cfg.regularOpCost + rest = cfg.regularOpCost + (7 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_load cfg (fuel + 7) (7 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 4) limits stack first callers _ {align := 2, offset := 0} (cell + 12) mi index memory post hm4 hi hmem4 hb
  · exact paid_credits s cfg.regularOpCost 4 _ (hc.mono (by omega))
  rw [show 7 * cfg.regularOpCost + rest = cfg.regularOpCost + (6 * cfg.regularOpCost + rest) by omega]
  apply wp_local_set cfg (fuel + 6) (6 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 5) limits stack first callers _ 4 (.i32 (readI32 memory (cell + 12).toNat)) post
  · exact paid_credits s cfg.regularOpCost 5 _ (hc.mono (by omega))
  rw [show 6 * cfg.regularOpCost + rest = cfg.regularOpCost + (5 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 5) (5 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 6) limits stack second callers _ 1 (.i32 (cell + 12)) post hslot
  · exact paid_credits s cfg.regularOpCost 6 _ (hc.mono (by omega))
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 4) (4 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 7) limits _ second callers _ 2 (.i32 scratch) post hscratch'
  · exact paid_credits s cfg.regularOpCost 7 _ (hc.mono (by omega))
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 3) (3 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 8) limits _ second callers _ 8 post
  · exact paid_credits s cfg.regularOpCost 8 _ (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_add cfg (fuel + 2) (2 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 9) limits (stack.push (.i32 (cell + 12))) second callers _ scratch 8 post
  · exact paid_credits s cfg.regularOpCost 9 _ (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (1 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_load cfg (fuel + 1) (1 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 10) limits (stack.push (.i32 (cell + 12))) second callers _ {align := 2, offset := 0} (scratch + 8) mi index memory post hm10 hi hmem10 hs
  · exact paid_credits s cfg.regularOpCost 10 _ (hc.mono (by omega))
  rw [show 1 * cfg.regularOpCost + rest = cfg.regularOpCost + rest by omega]
  apply wp_i32_store cfg fuel rest (paid s cfg.regularOpCost 11) limits stack second callers code {align := 2, offset := 0} (cell + 12) (readI32 memory (scratch + 8).toNat) mi index memory post hm11 hi hmem11 hb
  · exact paid_credits s cfg.regularOpCost 11 _ (hc.mono (by omega))
  · exact hnext

def replacedStatus (s : Store NearState) (op index : Nat) (cell : UInt32) (memory : Memory) :=
  storeI32 (paid s op 6) index cell.toNat memory 1

/-- Save the real old status before publishing initialized status one. -/
theorem wp_status (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (cell : UInt32) (mi : ModuleInst) (index : Nat)
    (memory : Memory) (post : Post)
    (hcell : frame.locals[0]? = some (.i32 cell))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory)
    (hb : cell.toNat + 4 ≤ memory.byteSize)
    (hc : s.host.gas.Credits (6 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (replacedStatus s cfg.regularOpCost index cell memory)
      limits stack {frame with locals := frame.locals.set! 1 (.i32 (readI32 memory cell.toNat))}
      callers code)) rest post) :
    WP cfg (fuel + 6) (.next (atCode s limits stack frame callers
      (WNear.Binary.InterfaceLazy.status ++ code))) (6 * cfg.regularOpCost + rest) post := by
  let updated := {frame with locals := frame.locals.set! 1 (.i32 (readI32 memory cell.toNat))}
  have hcell' : updated.locals[0]? = some (.i32 cell) := by
    simpa only [updated, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (by decide : 1 ≠ 0)] using hcell
  have hm5 : (paid s cfg.regularOpCost 5).modules[updated.inst]? = some mi := by simpa only [paid, chargedStore, updated] using hm
  have hmem5 : (paid s cfg.regularOpCost 5).mems[index]? = some memory := by simpa only [paid, chargedStore] using hmem
  rw [show 6 * cfg.regularOpCost + rest = cfg.regularOpCost + (5 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 5) (5 * cfg.regularOpCost + rest) s limits stack frame callers _ 0 (.i32 cell) post hcell
  · exact hc.mono (by omega)
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_load cfg (fuel + 4) (4 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 1) limits stack frame callers _ {align := 2, offset := 0} cell mi index memory post hm hi hmem hb
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_set cfg (fuel + 3) (3 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 2) limits stack frame callers _ 1 (.i32 (readI32 memory cell.toNat)) post
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) (2 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 3) limits stack updated callers _ 0 (.i32 cell) post hcell'
  · exact paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (1 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 1) (1 * cfg.regularOpCost + rest) (paid s cfg.regularOpCost 4) limits _ updated callers _ 1 post
  · exact paid_credits s cfg.regularOpCost 4 _ (hc.mono (by omega))
  rw [show 1 * cfg.regularOpCost + rest = cfg.regularOpCost + rest by omega]
  apply wp_i32_store cfg fuel rest (paid s cfg.regularOpCost 5) limits stack updated callers code {align := 2, offset := 0} cell 1 mi index memory post hm5 hi hmem5 hb
  · exact paid_credits s cfg.regularOpCost 5 _ (hc.mono (by omega))
  · exact hnext

end WNear.Proofs.InterfaceLazyBody
