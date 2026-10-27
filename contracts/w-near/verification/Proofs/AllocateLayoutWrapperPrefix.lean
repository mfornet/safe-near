import Proofs.AllocateLayoutWrapperFrame

/-! The actual fifteen-opcode wrapper prefix, stopping at its concrete leaf call. -/
namespace WNear.Proofs.AllocateLayoutWrapper
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP readI32 writeI32 reserved alignmentStore setupStore arguments

def prefixCode : Expr := WNear.Binary.AllocateLayout.reserve ++ [.local_get 2,.i32_const 1,.store .i32 none {align := 2,offset := 12},
  .local_get 2,.local_get 1,.store .i32 none {align := 2,offset := 8},.local_get 2,.local_get 2,.i32_const 8,.i32_binop .add]

theorem wp_prefix (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post) (hr : Ready s frame p)
    (hc : s.host.gas.Credits (15 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (arguments s cfg.regularOpCost p) limits
      ((stack.push (.i32 (scratch p))).push (.i32 (scratch p + 8))) (afterFrame frame p) callers code)) rest post) :
    WP cfg (fuel + 15) (.next (atCode s limits stack frame callers (prefixCode ++ code))) (15 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let ff := afterFrame frame p
  have hn : 2 < frame.locals.size := by have h := hr.locals; omega
  have hs : ff.locals[2]? = some (.i32 (scratch p)) := by simp only [ff,afterFrame,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt hn]
  have hz : ff.locals[1]? = some (.i32 p.size) := by simpa only [ff,afterFrame,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_ne (by decide : 2 ≠ 1)] using hr.size
  have cs : (setupStore s op p).host.gas.Credits (4 * op + rest) := by rw [setup_host]; exact paid_credits s op 11 _ (hc.mono (by dsimp [op]; omega))
  have args := wp_arguments cfg fuel rest (setupStore s op p) limits stack ff callers code (scratch p) post hs cs
    (by simpa only [arguments,op] using hnext)
  have ma : (alignmentStore s op p).modules[ff.inst]? = some p.mi := by
    rw [(alignment_fields s op p).2.1]; simpa only [ff,afterFrame] using hr.module
  have asp := writeI32_spec p.memory ((scratch p).toNat + 12) 1 hr.wf (by have h := hr.scratchBound; omega)
  have ca : (alignmentStore s op p).host.gas.Credits (3 * op + (4 * op + rest)) := by rw [alignment_host]; exact paid_credits s op 8 _ (hc.mono (by dsimp [op]; omega))
  have sz := InterfaceSetBody.wp_store_word cfg (fuel + 4) (4 * op + rest) (alignmentStore s op p) limits stack ff callers
    ([.local_get 2,.local_get 2,.i32_const 8,.i32_binop .add] ++ code) 2 1 8 (scratch p) p.size p.mi p.memoryIndex (alignmentMemory p) post hs hz ma hr.memoryIndex
    (alignment_memory s op p hr.memory) (by rw [show (alignmentMemory p).byteSize = p.memory.byteSize from asp.2.1]; have h := hr.scratchBound; omega) ca
    (by simpa only [setupStore,op] using args)
  have mr : (reserved s op p).modules[ff.inst]? = some p.mi := by
    rw [(reserved_fields s op p).2.1]; simpa only [ff,afterFrame] using hr.module
  have cr : (reserved s op p).host.gas.Credits (3 * op + (7 * op + rest)) := by rw [reserved_host]; exact paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  have al := wp_constant cfg (fuel + 7) (7 * op + rest) (reserved s op p) limits stack ff callers
    ([.local_get 2,.local_get 1,.store .i32 none {align := 2,offset := 8},.local_get 2,.local_get 2,.i32_const 8,.i32_binop .add] ++ code)
    2 12 (scratch p) 1 p.mi p.memoryIndex p.memory post hs mr hr.memoryIndex (reserved_memory s op p hr.memory)
    (by have h := hr.scratchBound; omega) cr
    (by
      have ge : 3 * cfg.regularOpCost + (4 * op + rest) = 7 * op + rest := by dsimp [op]; omega
      rw [ge] at sz
      simpa only [alignmentStore,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,op] using sz)
  have cn : WP cfg (fuel + 10) (.next (atCode (reserved s op p) limits stack ff callers
      ([.local_get 2,.i32_const 1,.store .i32 none {align := 2,offset := 12},.local_get 2,.local_get 1,.store .i32 none {align := 2,offset := 8},
        .local_get 2,.local_get 2,.i32_const 8,.i32_binop .add] ++ code))) (10 * op + rest) post := by
    simpa only [List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
      show 3 * cfg.regularOpCost + (7 * op + rest) = 10 * op + rest by dsimp [op]; omega] using al
  have res := InterfaceStack.wp_reserve cfg (fuel + 10) (10 * op + rest) s limits stack frame callers _ p.mi p.globalIndex p.global p.sp 2 16 post
    hr.module hr.globalIndex hr.global hr.sp (hc.mono (by dsimp [op]; omega))
    (by simpa only [reserved,ff,afterFrame,scratch,op] using cn)
  simpa only [prefixCode,WNear.Binary.AllocateLayout.reserve,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 5 * cfg.regularOpCost + (10 * op + rest) = 15 * cfg.regularOpCost + rest by dsimp [op]; omega] using res

end WNear.Proofs.AllocateLayoutWrapper
