import Proofs.AllocateLayoutWrapperPrefix

/-! Complete actual f752/f685 wrapper body through the real layout leaf. -/
namespace WNear.Proofs.AllocateLayoutWrapper
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 400000
attribute [local irreducible] WP readI32 writeI32 reserved alignmentStore setupStore arguments laidOut copied after

def epilogueCode : Expr := [.local_get 0,.local_get 2,.load .i64 none {align := 3,offset := 0},.store .i64 none {align := 3,offset := 0},
  .local_get 2,.i32_const 16,.i32_binop .add,.global_set 0]

theorem wp_epilogue (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post) (hr : Ready s frame p)
    (hc : s.host.gas.Credits (67 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost p) limits stack (afterFrame frame p) callers code)) rest post) :
    WP cfg (fuel + 8) (.next (atCode (laidOut s cfg.regularOpCost p) limits stack (afterFrame frame p) callers (epilogueCode ++ code)))
      (8 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let ff := afterFrame frame p
  have hn : 2 < frame.locals.size := by have h := hr.locals; omega
  have hs : ff.locals[2]? = some (.i32 (scratch p)) := by simp only [ff,afterFrame,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt hn]
  have ho : ff.locals[0]? = some (.i32 p.out) := by simpa only [ff,afterFrame,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_ne (by decide : 2 ≠ 0)] using hr.out
  have mc : (copied s op p).modules[ff.inst]? = some p.mi := by rw [(copied_fields s op p).2.1]; simpa only [ff,afterFrame] using hr.module
  have restore := InterfaceStack.wp_restore cfg fuel rest (copied s op p) limits stack ff callers code p.mi p.globalIndex
    {p.global with value := .i32 (scratch p)} (scratch p) 2 16 post hs mc hr.globalIndex (copied_global s op p hr.global)
    (copied_credits s op (4 * op + rest) p (hc.mono (by dsimp [op]; omega)))
    (by simpa only [after,ff,op] using hnext)
  have ml : (laidOut s op p).modules[ff.inst]? = some p.mi := by rw [(laidOut_fields s op p).2.1]; simpa only [ff,afterFrame] using hr.module
  have setup := setup_spec p hr.wf hr.scratchBound
  have lb : (scratch p).toNat + 8 ≤ (setupMemory p).byteSize := by rw [setup.2.1]; have h := hr.scratchBound; omega
  have ls := AllocateLayout.final_spec (leafLayout p) setup.1 lb
  have sizeEq : (laidOutMemory p).byteSize = p.memory.byteSize := ls.2.1.trans setup.2.1
  have copy := wp_copy cfg (fuel + 4) (4 * op + rest) (laidOut s op p) limits stack ff callers
    ([.local_get 2,.i32_const 16,.i32_binop .add,.global_set 0] ++ code) p.out (scratch p) p.mi p.memoryIndex (laidOutMemory p) post ho hs ml hr.memoryIndex
    (laidOut_memory s op p hr.memory) (by rw [sizeEq]; have h := hr.scratchBound; omega) (by rw [sizeEq]; exact hr.outBound)
    ((laidOut_credits s op (8 * op + rest) p (hc.mono (by dsimp [op]; omega))).mono (by dsimp [op]; omega))
    (by simpa only [copied,Nat.add_assoc,Nat.reduceAdd,op] using restore)
  simpa only [epilogueCode,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 4 * cfg.regularOpCost + (4 * op + rest) = 8 * cfg.regularOpCost + rest by dsimp [op]; omega] using copy

/-- Original stack and output spans, original installed code, and credits
suffice for the complete body. No leaf execution or future heap fact is assumed. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post) (hr : Ready s frame p)
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (67 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost p) limits base.toArray (afterFrame frame p) callers code)) rest post) :
    WP cfg (fuel + 59) (.next (atCode s limits base.toArray frame callers (WNear.Binary.AllocateLayout.wrapperBody p.calleeIndex ++ code)))
      (67 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let ff := afterFrame frame p
  have ep := wp_epilogue cfg fuel rest s limits base.toArray frame callers code p post hr hc hnext
  have ma : (arguments s op p).modules[ff.inst]? = some p.mi := by rw [(arguments_fields s op p).2.1]; simpa only [ff,afterFrame] using hr.module
  have fa : (arguments s op p).funcs[p.calleeAddress]? = some (.wasm WNear.Binary.AllocateLayout.signature ff.inst
      (WNear.Binary.AllocateLayout.function p.message p.location p.previous)) := by
    rw [(arguments_fields s op p).1]; simpa only [ff,afterFrame] using hr.function
  have ss := setup_spec p hr.wf hr.scratchBound
  have plus := StorePairAddresses.add_eight_memory p.memory (scratch p) hr.width hr.scratchBound
  have ib : (scratch p + 8).toNat + 8 ≤ (setupMemory p).byteSize := by rw [plus,ss.2.1]; have h := hr.scratchBound; omega
  have ob : (scratch p).toNat + 8 ≤ (setupMemory p).byteSize := by rw [ss.2.1]; have h := hr.scratchBound; omega
  have alignment : readI32 (setupMemory p) ((scratch p + 8).toNat + 4) = 1 := by
    rw [plus,show (scratch p).toNat + 8 + 4 = (scratch p).toNat + 12 by omega]
    exact ss.2.2.2.2
  have call := AllocateLayout.wp_call cfg (fuel + 8) (8 * op + rest) (arguments s op p) limits base ff callers (epilogueCode ++ code)
    p.message p.location p.previous (leafLayout p) p.calleeIndex p.calleeAddress post ma hr.globalIndex (arguments_global s op p hr.global) rfl
    hr.memoryIndex (arguments_memory s op p hr.memory) hr.functionIndex fa ss.1 ib ob alignment hd
    (arguments_credits s op (44 * op + (8 * op + rest)) p (hc.mono (by dsimp [op]; omega)))
    (by simpa only [laidOut,Nat.add_assoc,Nat.reduceAdd,op] using ep)
  have pn : WP cfg (fuel + 44) (.next (atCode (arguments s op p) limits
      ((base.toArray.push (.i32 (scratch p))).push (.i32 (scratch p + 8))) ff callers (.call p.calleeIndex :: epilogueCode ++ code)))
      (52 * op + rest) post := by
    have array : (base ++ [Value.i32 (scratch p),.i32 (scratch p + 8)]).toArray = (base.toArray.push (.i32 (scratch p))).push (.i32 (scratch p + 8)) := by
      apply Array.toList_inj.mp; simp
    simpa only [AllocateLayout.called,leafLayout,ff,array,List.cons_append,Nat.add_assoc,Nat.reduceAdd,
      show 44 * cfg.regularOpCost + (8 * op + rest) = 52 * op + rest by dsimp [op]; omega] using call
  have prefixRun := wp_prefix cfg (fuel + 44) (52 * op + rest) s limits base.toArray frame callers
    (.call p.calleeIndex :: epilogueCode ++ code) p post hr (hc.mono (by dsimp [op]; omega)) pn
  simpa only [prefixCode,epilogueCode,WNear.Binary.AllocateLayout.wrapperBody,WNear.Binary.AllocateLayout.reserve,
    List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 15 * cfg.regularOpCost + (52 * op + rest) = 67 * cfg.regularOpCost + rest by dsimp [op]; omega] using prefixRun

end WNear.Proofs.AllocateLayoutWrapper
