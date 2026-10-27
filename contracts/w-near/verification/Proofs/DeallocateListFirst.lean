import Proofs.DeallocateListState
import NearVM.MeteredLoopRules

/-! Actual full nonzero predecessor block of f575. -/
namespace WNear.Proofs.DeallocateListFirst
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open DeallocateListState
set_option maxRecDepth 16384
set_option maxHeartbeats 400000
attribute [local irreducible] WP

/-- The full first block, including its free entry and normal label exit. -/
theorem wp_first (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post)
    (hr : Ready s frame p)
    (hc : s.host.gas.Credits (28 * cfg.regularOpCost + rest))
    (hafter : (firstStore s cfg.regularOpCost p).host.gas.Credits rest)
    (hnext : WP cfg fuel (.next (atCode (firstStore s cfg.regularOpCost p) limits stack
      (firstFrame frame p) callers code)) rest post) :
    WP cfg (fuel + 30) (.next (atCode s limits stack frame callers
      (.block .empty WNear.Binary.DeallocateList.previous :: code))) (28 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let bf := emptyBlockFrame frame stack.size code
  let hf := DeallocateListGuards.headerFrame bf (firstRaw p)
  let sf := DeallocateListGuards.selectedFrame hf (firstLink p)
  let label : Label := {arity := 0, height := stack.size, rest := code, loop := none}
  have hend := wp_end_label cfg fuel rest (firstStore s op p) limits stack
    (firstFrame frame p) callers label post hafter hnext
  have he : WP cfg (fuel + 1) (.next (atCode (firstStore s op p) limits stack sf callers [])) rest post := by
    simpa only [sf, hf, bf, firstFrame, DeallocateListGuards.selectedFrame,
      DeallocateListGuards.headerFrame, emptyBlockFrame, label] using hend
  have hlt1 : 1 < frame.locals.size := by have h := hr.locals; omega
  have hlt2 : 2 < frame.locals.size := by have h := hr.locals; omega
  have hsd : sf.locals[1]? = some (.i32 (firstLink p)) := by
    change ((hf.locals.setIfInBounds 1 (.i32 (firstLink p)))[1]?) = _
    exact Array.getElem?_setIfInBounds_self_of_lt (by simpa only [hf, bf, DeallocateListGuards.headerFrame, emptyBlockFrame, Array.size_set!] using hlt1)
  have hss : sf.locals[0]? = some (.i32 p.pointer) := by
    simpa [sf, hf, bf, DeallocateListGuards.selectedFrame, DeallocateListGuards.headerFrame,
      emptyBlockFrame, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (by decide : 1 ≠ 0), Array.getElem?_setIfInBounds_ne (by decide : 2 ≠ 0)] using hr.pointer
  have hm17 : (paid s op 17).modules[sf.inst]? = some p.mi := by
    simpa only [paid, chargedStore, sf, hf, bf, DeallocateListGuards.selectedFrame,
      DeallocateListGuards.headerFrame, emptyBlockFrame] using hr.module
  have hmem17 : (paid s op 17).mems[p.memoryIndex]? = some p.memory := by
    simpa only [paid, chargedStore] using hr.memory
  have wr := DeallocateListWrite.wp_write cfg (fuel + 1) rest (paid s op 17) limits stack sf callers []
    1 0 4 4 (firstLink p) p.pointer p.mi p.memoryIndex p.memory post hsd hss hm17 hr.memoryIndex hmem17
    (by have h := hr.firstBound; omega) (by have h := hr.nodeBound; omega)
    (paid_credits s op 17 _ (hc.mono (by dsimp [op]; omega))) he
  have h1 : hf.locals[1]? = some (.i32 (firstRaw p)) := by
    simp [hf, bf, DeallocateListGuards.headerFrame, emptyBlockFrame, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (by decide : 2 ≠ 1), Array.getElem?_setIfInBounds_self_of_lt hlt1]
  have h2 : hf.locals[2]? = some (.i32 (firstLink p)) := by
    change (((bf.locals.set! 1 (.i32 (firstRaw p))).setIfInBounds 2 (.i32 (firstLink p)))[2]?) = _
    exact Array.getElem?_setIfInBounds_self_of_lt (by simpa only [bf, emptyBlockFrame, Array.size_set!] using hlt2)
  have se := DeallocateListGuards.wp_select_guard cfg (fuel + 12) (11 * op + rest) (paid s op 8) limits stack hf callers
    (WNear.Binary.DeallocateList.previous.drop 17) (firstRaw p) (firstLink p) post h1 h2 hr.firstFlag hr.firstNonzero
    (paid_credits s op 8 _ (hc.mono (by dsimp [op]; omega))) (by simpa only [paid, op, sf, WNear.Binary.DeallocateList.previous, List.drop, List.append_nil, Nat.add_assoc, Nat.reduceAdd] using wr)
  have ge9 : 9 * cfg.regularOpCost + (11 * op + rest) = 20 * op + rest := by dsimp [op]; omega
  rw [ge9] at se
  have hd := DeallocateListGuards.wp_header cfg (fuel + 21) (20 * op + rest) s limits stack bf callers
    (WNear.Binary.DeallocateList.previous.drop 8) 0 p.pointer p.mi p.memoryIndex p.memory post hr.pointer hr.locals
    hr.module hr.memoryIndex hr.memory (by have h := hr.nodeBound; omega) hr.firstNonzero
    (hc.mono (by dsimp [op]; omega)) (by simpa only [Nat.add_zero, Nat.zero_add, firstRaw, firstLink, paid, op, hf, WNear.Binary.DeallocateList.previous, List.drop, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd] using se)
  have ge8 : 8 * cfg.regularOpCost + (20 * op + rest) = 28 * cfg.regularOpCost + rest := by dsimp [op]; omega
  rw [ge8] at hd
  have hin : WP cfg (fuel + 29) (.next (atCode s limits stack bf callers WNear.Binary.DeallocateList.previous))
      (28 * cfg.regularOpCost + rest) post := by
    simpa only [WNear.Binary.DeallocateList.previous, List.drop, List.cons_append, List.nil_append,
      Nat.reduceAdd, Nat.reduceSub, Nat.zero_add, Nat.add_assoc, op] using hd
  exact wp_block_empty cfg (fuel + 29) _ s limits stack frame callers _ code post hc hin

end WNear.Proofs.DeallocateListFirst
