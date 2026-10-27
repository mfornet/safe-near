import Proofs.AllocateLayoutGuard
import Proofs.AllocateLayoutReads
import Proofs.AllocateLayoutFrame

/-! Complete accepted leaf execution for both deployed alignment-layout copies. -/
namespace WNear.Proofs.AllocateLayout
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 400000
attribute [local irreducible] WP readI32 writeI32 reserved guarded loaded high low after

theorem wp_tail (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post) (hr : Ready s frame p)
    (hc : s.host.gas.Credits (33 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost p) limits stack (finalFrame frame p) callers code)) rest post) :
    WP cfg (fuel + 21) (.next (atCode (guarded s cfg.regularOpCost p) limits stack (guardedFrame frame p) callers
      (WNear.Binary.AllocateLayout.tail ++ code))) (21 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let ff := finalFrame frame p
  have hn1 : 1 < (guardedFrame frame p).locals.size := by
    simpa only [guardedFrame,reservedFrame,Array.size_set!] using (show 1 < frame.locals.size by have h := hr.locals; omega)
  have h0 : ff.locals[0]? = some (.i32 p.out) := by
    simpa only [ff,finalFrame,guardedFrame,reservedFrame,Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne (by decide : 1 ≠ 0),Array.getElem?_setIfInBounds_ne (by decide : 2 ≠ 0),Array.getElem?_setIfInBounds_ne (by decide : 3 ≠ 0)] using hr.out
  have h1 : ff.locals[1]? = some (.i32 (size p)) := by
    simpa only [ff,finalFrame,Array.set!_eq_setIfInBounds] using (Array.getElem?_setIfInBounds_self_of_lt (a := Value.i32 (size p)) hn1)
  have h2 : ff.locals[2]? = some (.i32 (scratch p)) := by
    have hn : 2 < frame.locals.size := by have h := hr.locals; omega
    simp only [ff,finalFrame,guardedFrame,reservedFrame,Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne (by decide : 1 ≠ 2),Array.getElem?_setIfInBounds_ne (by decide : 3 ≠ 2),Array.getElem?_setIfInBounds_self_of_lt hn]
  have h3 : ff.locals[3]? = some (.i32 1) := by
    have hn : 3 < (reservedFrame frame p).locals.size := by simpa only [reservedFrame,Array.size_set!] using (show 3 < frame.locals.size by have h := hr.locals; omega)
    simp only [ff,finalFrame,guardedFrame,Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne (by decide : 1 ≠ 3),Array.getElem?_setIfInBounds_self_of_lt hn]
  have ml : (low s op p).modules[ff.inst]? = some p.mi := by
    rw [(low_fields s op p).2.1]
    simpa only [ff,finalFrame,guardedFrame,reservedFrame] using hr.module
  have cl : (low s op p).host.gas.Credits (4 * op + rest) := by
    rw [low_host]
    exact paid_credits s op 29 _ (hc.mono (by dsimp [op]; omega))
  have restore := InterfaceStack.wp_restore cfg fuel rest (low s op p) limits stack ff callers code p.mi p.globalIndex
    {p.global with value := .i32 (scratch p)} (scratch p) 2 16 post h2 ml hr.globalIndex (low_global s op p hr.global) cl (by simpa only [after,ff,op] using hnext)
  have mh : (high s op p).modules[ff.inst]? = some p.mi := by
    rw [(high_fields s op p).2.1]
    simpa only [ff,finalFrame,guardedFrame,reservedFrame] using hr.module
  have hs := writeI32_spec p.memory (p.out.toNat + 4) 1 hr.wf (by have h := hr.outBound; omega)
  have ch : (high s op p).host.gas.Credits (11 * op + (4 * op + rest)) := by
    rw [high_host]
    exact paid_credits s op 18 _ (hc.mono (by dsimp [op]; omega))
  have rn := wp_rounded cfg (fuel + 4) (4 * op + rest) (high s op p) limits stack ff callers
    ([.local_get 2,.i32_const 16,.i32_binop .add,.global_set 0] ++ code) p.out (size p) p.mi p.memoryIndex (highMemory p) post
    h0 h1 h3 mh hr.memoryIndex (high_memory s op p hr.memory)
    (by rw [show (highMemory p).byteSize = p.memory.byteSize from hs.2.1]; have h := hr.outBound; omega) ch
    (by simpa only [low,Nat.add_assoc,Nat.reduceAdd,op] using restore)
  have mload : (loaded s op p).modules[ff.inst]? = some p.mi := by
    rw [(loaded_fields s op p).2.1]
    simpa only [ff,finalFrame,guardedFrame,reservedFrame] using hr.module
  have cLoad : (loaded s op p).host.gas.Credits (3 * op + (15 * op + rest)) := by
    rw [loaded_host]
    exact paid_credits s op 15 _ (hc.mono (by dsimp [op]; omega))
  have hw := wp_high cfg (fuel + 15) (15 * op + rest) (loaded s op p) limits stack ff callers
    (roundedCode ++ [.local_get 2,.i32_const 16,.i32_binop .add,.global_set 0] ++ code) p.out p.mi p.memoryIndex p.memory post h0 h3
    mload hr.memoryIndex (loaded_memory s op p hr.memory) hr.outBound cLoad
    (by
      have ge : 11 * cfg.regularOpCost + (4 * op + rest) = 15 * op + rest := by dsimp [op]; omega
      rw [ge] at rn
      simpa only [highStore,high,Nat.add_assoc,Nat.reduceAdd,op,List.cons_append,List.nil_append,List.append_assoc] using rn)
  have mg : (guarded s op p).modules[(guardedFrame frame p).inst]? = some p.mi := by
    rw [(guarded_fields s op p).2.1]
    simpa only [guardedFrame,reservedFrame] using hr.module
  have input : (guardedFrame frame p).locals[1]? = some (.i32 p.input) := by
    simpa only [guardedFrame,reservedFrame,Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne (by decide : 3 ≠ 1),Array.getElem?_setIfInBounds_ne (by decide : 2 ≠ 1)] using hr.input
  have cg : (guarded s op p).host.gas.Credits (3 * op + (18 * op + rest)) := by
    rw [guarded_host]
    exact paid_credits s op 12 _ (hc.mono (by dsimp [op]; omega))
  have read := wp_size_read cfg (fuel + 18) (18 * op + rest) (guarded s op p) limits stack (guardedFrame frame p) callers
    ([.local_get 0,.local_get 3,.store .i32 none {align := 2,offset := 4}] ++ roundedCode ++ [.local_get 2,.i32_const 16,.i32_binop .add,.global_set 0] ++ code)
    p.input p.mi p.memoryIndex p.memory post input mg hr.memoryIndex (guarded_memory s op p hr.memory)
    (by have h := hr.inputBound; omega) cg
    (by
      have ge : 3 * cfg.regularOpCost + (15 * op + rest) = 18 * op + rest := by dsimp [op]; omega
      rw [ge] at hw
      simpa only [sizeFrame,finalFrame,size,ff,loaded,op,Nat.add_assoc,Nat.reduceAdd,List.append_assoc] using hw)
  have ge : 3 * cfg.regularOpCost + (18 * op + rest) = 21 * cfg.regularOpCost + rest := by dsimp [op]; omega
  rw [ge] at read
  simpa only [WNear.Binary.AllocateLayout.tail,roundedCode,List.cons_append,List.nil_append,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,op] using read

/-- Every accepted instruction of deployed f751/f684 is executed from original
alignment-one input data. The panic code is bypassed by the proved popcount test. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (message location previous : UInt32) (p : Layout) (post : Post)
    (hr : Ready s frame p) (hc : s.host.gas.Credits (33 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost p) limits stack (finalFrame frame p) callers code)) rest post) :
    WP cfg (fuel + 34) (.next (atCode s limits stack frame callers
      (WNear.Binary.AllocateLayout.body message location previous ++ code))) (33 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have tail := wp_tail cfg fuel rest s limits stack frame callers code p post hr hc hnext
  have mr : (reserved s op p).modules[(reservedFrame frame p).inst]? = some p.mi := by
    rw [(reserved_fields s op p).2.1]
    simpa only [reservedFrame] using hr.module
  have input : (reservedFrame frame p).locals[1]? = some (.i32 p.input) := by
    simpa only [reservedFrame,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_ne (by decide : 2 ≠ 1)] using hr.input
  have cr : (reserved s op p).host.gas.Credits (7 * op + (21 * op + rest)) := by
    rw [reserved_host]
    exact paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  have guard := wp_guard cfg (fuel + 21) (21 * op + rest) (reserved s op p) limits stack (reservedFrame frame p) callers
    (WNear.Binary.AllocateLayout.tail ++ code) (WNear.Binary.AllocateLayout.panic message location previous)
    p.input p.mi p.memoryIndex p.memory post input mr hr.memoryIndex (reserved_memory s op p hr.memory) hr.inputBound hr.alignment cr
    (by simpa only [guarded,alignmentFrame,guardedFrame,Nat.add_assoc,Nat.reduceAdd,op] using tail)
  have cg : WP cfg (fuel + 29) (.next (atCode (reserved s op p) limits stack (reservedFrame frame p) callers
      (.block .empty (WNear.Binary.AllocateLayout.guard ++ WNear.Binary.AllocateLayout.panic message location previous) :: WNear.Binary.AllocateLayout.tail ++ code)))
      (28 * op + rest) post := by
    simpa only [List.cons_append,Nat.add_assoc,Nat.reduceAdd,
      show 7 * cfg.regularOpCost + (21 * op + rest) = 28 * op + rest by dsimp [op]; omega] using guard
  have reserve := InterfaceStack.wp_reserve cfg (fuel + 29) (28 * op + rest) s limits stack frame callers
    (.block .empty (WNear.Binary.AllocateLayout.guard ++ WNear.Binary.AllocateLayout.panic message location previous) :: WNear.Binary.AllocateLayout.tail ++ code)
    p.mi p.globalIndex p.global p.sp 2 16 post hr.module hr.globalIndex hr.global hr.sp (hc.mono (by dsimp [op]; omega)) (by simpa only [reserved,reservedFrame,scratch,op] using cg)
  simpa only [WNear.Binary.AllocateLayout.body,WNear.Binary.AllocateLayout.reserve,List.append_assoc,List.cons_append,List.nil_append,
    Nat.add_assoc,Nat.reduceAdd,show 5 * cfg.regularOpCost + (28 * op + rest) = 33 * cfg.regularOpCost + rest by dsimp [op]; omega] using reserve

end WNear.Proofs.AllocateLayout
