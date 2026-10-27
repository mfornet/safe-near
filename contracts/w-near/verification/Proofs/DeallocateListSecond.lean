import Proofs.DeallocateListFrame
import Proofs.DeallocateListRead
import NearVM.MeteredLoopRules

/-! Actual second f575 block, with current-memory sequential reread. -/
namespace WNear.Proofs.DeallocateListSecond
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open DeallocateListState
set_option maxRecDepth 16384
set_option maxHeartbeats 400000
attribute [local irreducible] WP readI32 writeI32 firstStore secondStore secondAfter firstMemory secondMemory

theorem wp_second (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post) (hr : Ready s frame p)
    (hc : s.host.gas.Credits (50 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (secondAfter s cfg.regularOpCost p) limits stack
      (finalFrame frame p) callers code)) rest post) :
    WP cfg (fuel + 24) (.next (atCode (firstStore s cfg.regularOpCost p) limits stack
      (firstFrame frame p) callers (.block .empty WNear.Binary.DeallocateList.next :: code)))
      (22 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let ff := firstFrame frame p
  let bf := emptyBlockFrame ff stack.size code
  let hf := DeallocateListGuards.headerFrame bf (secondRaw p)
  let rf := {hf with locals := hf.locals.set! 1 (.i32 (finalRaw p))}
  let label : Label := {arity := 0, height := stack.size, rest := code, loop := none}
  have spec := memory_specs p hr.wf hr.firstBound hr.secondBound
  have cf := (first_gas s op (22 * op + rest) p (hc.mono (by dsimp [op]; omega))).2.2
  have cs := (second_gas s op (3 * op + rest) p (hc.mono (by dsimp [op]; omega))).2.2
  have ce := (secondAfter_gas s op rest p hc).2.2
  have hend := wp_end_label cfg fuel rest (secondAfter s op p) limits stack (finalFrame frame p) callers label post ce hnext
  have he : WP cfg (fuel + 1) (.next (atCode (secondAfter s op p) limits stack rf callers [])) rest post := by
    simpa only [rf, hf, bf, ff, finalFrame, secondFrame, emptyBlockFrame, DeallocateListGuards.headerFrame, label] using hend
  have hpH : hf.locals[0]? = some (.i32 p.pointer) := by
    simpa [hf, bf, ff, firstFrame, DeallocateListGuards.headerFrame, DeallocateListGuards.selectedFrame,
      emptyBlockFrame, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (by decide : 1 ≠ 0),
      Array.getElem?_setIfInBounds_ne (by decide : 2 ≠ 0)] using hr.pointer
  have hmS : (secondStore s op p).modules[hf.inst]? = some p.mi := by
    rw [(second_fields s op p).2.1]
    exact hr.module
  have rd := DeallocateListRead.wp_read cfg (fuel + 1) rest (secondStore s op p) limits stack hf callers []
    p.pointer p.mi p.memoryIndex (secondMemory p) post hpH hmS hr.memoryIndex (second_memory s op p hr.memory)
    (by have h := hr.nodeBound; rw [spec.2.2.2]; exact h) cs (by simpa only [secondAfter, rf, finalRaw, op] using he)
  have hn : 3 ≤ bf.locals.size := by simpa only [bf, ff, firstFrame, DeallocateListGuards.headerFrame,
    DeallocateListGuards.selectedFrame, emptyBlockFrame, Array.size_set!] using hr.locals
  have h2 : hf.locals[2]? = some (.i32 (secondLink p)) := by
    have hlt : 2 < (bf.locals.set! 1 (.i32 (secondRaw p))).size := by simpa only [Array.size_set!] using (show 2 < bf.locals.size by omega)
    simpa only [hf, DeallocateListGuards.headerFrame, secondLink, Array.set!_eq_setIfInBounds] using (Array.getElem?_setIfInBounds_self_of_lt (xs := bf.locals.set! 1 (.i32 (secondRaw p))) (a := Value.i32 (secondRaw p &&& 4294967292)) hlt)
  have hm8 : (paid (firstStore s op p) op 8).modules[hf.inst]? = some p.mi := by
    simpa only [paid, chargedStore, hf, bf, ff, DeallocateListGuards.headerFrame, emptyBlockFrame,
      firstFrame, DeallocateListGuards.selectedFrame, (first_fields s op p).2.1] using hr.module
  have hmem8 : (paid (firstStore s op p) op 8).mems[p.memoryIndex]? = some (firstMemory p) := by
    simpa only [paid, chargedStore] using first_memory s op p hr.memory
  have wr := DeallocateListWrite.wp_write cfg (fuel + 4) (3 * op + rest) (paid (firstStore s op p) op 8)
    limits stack hf callers [.local_get 0, .load .i32 none {align := 2, offset := 4}, .local_set 1]
    2 0 0 0 (secondLink p) p.pointer p.mi p.memoryIndex (firstMemory p) post h2 hpH hm8 hr.memoryIndex hmem8
    (by simpa only [Nat.add_zero] using hr.secondBound) (by have h := hr.nodeBound; rw [spec.2.1]; omega)
    (paid_credits (firstStore s op p) op 8 _ (cf.mono (by omega)))
    (by simpa only [List.append_nil, secondStore, Nat.add_zero, finalRaw, Nat.add_assoc, Nat.reduceAdd, op] using rd)
  have ge : 11 * cfg.regularOpCost + (3 * op + rest) = 14 * op + rest := by dsimp [op]; omega
  rw [ge] at wr
  have hmF : (firstStore s op p).modules[bf.inst]? = some p.mi := by
    rw [(first_fields s op p).2.1]; exact hr.module
  have hpF : bf.locals[0]? = some (.i32 p.pointer) := by
    simpa [bf, ff, firstFrame, DeallocateListGuards.headerFrame, DeallocateListGuards.selectedFrame,
      emptyBlockFrame, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (by decide : 1 ≠ 0),
      Array.getElem?_setIfInBounds_ne (by decide : 2 ≠ 0)] using hr.pointer
  have hd := DeallocateListGuards.wp_header cfg (fuel + 15) (14 * op + rest) (firstStore s op p) limits stack bf callers
    (WNear.Binary.DeallocateList.next.drop 8) 4 p.pointer p.mi p.memoryIndex (firstMemory p) post hpF hn hmF hr.memoryIndex
    (first_memory s op p hr.memory) (by have h := hr.nodeBound; rw [spec.2.1]; omega) hr.secondNonzero
    (cf.mono (by omega)) (by simpa only [hf, secondRaw, secondLink, Nat.add_zero, WNear.Binary.DeallocateList.next,
      List.drop, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd, op] using wr)
  have ge8 : 8 * cfg.regularOpCost + (14 * op + rest) = 22 * cfg.regularOpCost + rest := by dsimp [op]; omega
  rw [ge8] at hd
  have hi : WP cfg (fuel + 23) (.next (atCode (firstStore s op p) limits stack bf callers WNear.Binary.DeallocateList.next))
      (22 * cfg.regularOpCost + rest) post := by
    simpa only [WNear.Binary.DeallocateList.next, List.drop, List.cons_append, List.nil_append,
      Nat.add_assoc, Nat.reduceAdd] using hd
  exact wp_block_empty cfg (fuel + 23) _ (firstStore s op p) limits stack ff callers _ code post cf hi

end WNear.Proofs.DeallocateListSecond
