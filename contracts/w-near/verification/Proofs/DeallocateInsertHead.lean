import Proofs.DeallocateInsertState
import Proofs.DeallocateCoreMark
import Proofs.DeallocateCoreCredits
import Proofs.DeallocateCoreFrame
import Proofs.DeallocateListSizeFrame

/-! The actual pre-neighbor instructions depend only on their original guard,
width and memory premises, also valid on the insertion branch. -/
namespace WNear.Proofs.DeallocateInsert
open Wasm Wasm.Near MeteredLogic DeallocateCore
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32 writeI32

def headBeforeCode : Expr := WNear.Binary.Deallocate.guard ++ WNear.Binary.Deallocate.alignCall ++ WNear.Binary.Deallocate.saveHead
def headAfterCode : Expr := WNear.Binary.Deallocate.markFree ++ WNear.Binary.Deallocate.sizeCall ++ WNear.Binary.Deallocate.zeroLink
def markedFrom (s : Store NearState) (op : Nat) (p : Layout) :=
  storeI32 (paid s op 9) p.memoryIndex p.header.toNat p.memory (readI32 p.memory p.header.toNat &&& 4294967294)
def sizedFrom (s : Store NearState) (op : Nat) (p : Layout) := Deallocate.sized (markedFrom s op p) op
def headAfter (s : Store NearState) (op : Nat) (p : Layout) :=
  Deallocate.zeroStore (sizedFrom s op p) op p.memoryIndex (markedMemory p) p.pointer

private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems = s.mems := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih
private theorem paid_funcs (s : Store NearState) (op n : Nat) : (paid s op n).funcs = s.funcs := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih
private theorem paid_modules (s : Store NearState) (op n : Nat) : (paid s op n).modules = s.modules := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih
private theorem aligned_mems (s : Store NearState) (op : Nat) : (Deallocate.aligned s op).mems = s.mems := by
  have hr := congrArg (fun t => t.mems) (DeallocateAlign.after570_resources (paid s op 1) op)
  simp only at hr
  unfold Deallocate.aligned
  rw [paid_mems,hr,paid_mems]
private theorem sized_mems (s : Store NearState) (op : Nat) : (Deallocate.sized s op).mems = s.mems := by
  have hr := congrArg (fun t => t.mems) (DeallocateListSize.after_resources (paid s op 1) op)
  simp only at hr
  unfold Deallocate.sized
  rw [paid_mems,hr,paid_mems]
private theorem sized_funcs (s : Store NearState) (op : Nat) : (Deallocate.sized s op).funcs = s.funcs := by
  have hr := congrArg (fun t => t.funcs) (DeallocateListSize.after_resources (paid s op 1) op)
  simp only at hr
  unfold Deallocate.sized
  rw [paid_funcs,hr,paid_funcs]
private theorem sized_modules (s : Store NearState) (op : Nat) : (Deallocate.sized s op).modules = s.modules := by
  have hr := congrArg (fun t => t.modules) (DeallocateListSize.after_resources (paid s op 1) op)
  simp only at hr
  unfold Deallocate.sized
  rw [paid_modules,hr,paid_modules]

/-- The nonzero guards and real alignment call run before the original list
head is saved. Every callee is the deployed function. -/
theorem wp_head_before (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post) (hr : Ready s frame p)
    (hd : callers.length + 2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (52 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (saved s cfg.regularOpCost) limits base.toArray
      (savedFrame frame p) callers code)) rest post) :
    WP cfg (fuel + 36) (.next (atCode s limits base.toArray frame callers (headBeforeCode ++ code)))
      (52 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have cg := guarded_credits s op (46 * op + rest) (hc.mono (by dsimp [op]; omega))
  have ca := aligned_credits s op (3 * op + rest) (hc.mono (by dsimp [op]; omega))
  have codeGuard := guarded_code s op frame.inst p hr.code
  have codeAligned := aligned_code s op frame.inst p hr.code
  have ma : (aligned s op).mems[p.memoryIndex]? = some p.memory := by
    rw [aligned,aligned_mems,guarded,paid_mems]; exact hr.memory
  have hn : WP cfg fuel (.next (atCode (paid (aligned s op) op 3) limits base.toArray
      {frame with locals := frame.locals.set! 4 (.i32 (readI32 p.memory p.allocator.toNat))} callers code)) rest post := by
    simpa only [saved,savedFrame,oldHead,op] using hnext
  have save := Deallocate.wp_save_head cfg fuel rest (aligned s op) limits base.toArray frame callers code p.allocator
    p.mi p.memoryIndex p.memory post hr.allocator codeAligned.module hr.code.memoryIndex ma hr.native.allocatorBound
    (ca.mono (by dsimp [op]; omega)) hn
  have nextAlign : WP cfg (fuel + 3) (.next (atCode (Deallocate.aligned (guarded s op) cfg.regularOpCost) limits
      base.toArray frame callers (WNear.Binary.Deallocate.saveHead ++ code))) (3 * cfg.regularOpCost + rest) post := by
    simpa only [aligned,op] using save
  have align := Deallocate.wp_align_call cfg (fuel + 3) (3 * cfg.regularOpCost + rest) (guarded s op)
    limits base frame callers (WNear.Binary.Deallocate.saveHead ++ code) p.length p.mi p.address568 p.address570 post
    hr.length codeGuard.module hr.code.index568 codeGuard.function568 hr.code.index570 codeGuard.function570
    hr.native.lengthBound hd (cg.mono (by dsimp [op]; omega)) nextAlign
  have nextGuard : WP cfg (fuel + 30) (.next (atCode (paid s cfg.regularOpCost 6) limits base.toArray frame callers
      (WNear.Binary.Deallocate.alignCall ++ WNear.Binary.Deallocate.saveHead ++ code))) (46 * cfg.regularOpCost + rest) post := by
    simpa only [guarded,op,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
      show 43 * cfg.regularOpCost + (3 * cfg.regularOpCost + rest) = 46 * cfg.regularOpCost + rest by omega] using align
  have result := Deallocate.wp_core_guards cfg (fuel + 30) (46 * cfg.regularOpCost + rest) s limits base.toArray frame callers _
    p.pointer p.length post hr.pointer hr.length hr.native.pointerNonzero hr.native.lengthNonzero (hc.mono (by omega)) nextGuard
  simpa only [headBeforeCode,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
    show 6 * cfg.regularOpCost + (46 * cfg.regularOpCost + rest) = 52 * cfg.regularOpCost + rest by omega] using result

/-- The mark, checked size, and zero-link writes execute from an arbitrary
pre-store; all pointer calculations have already been named in the layout. -/
theorem wp_head_after (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post)
    (hcde : Code s frame.inst p) (hm : s.mems[p.memoryIndex]? = some p.memory)
    (hp : frame.locals[1]? = some (.i32 p.pointer)) (hs : 3 ≤ frame.locals.size) (hnative : Native p)
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (39 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (headAfter s cfg.regularOpCost p) limits base.toArray
      (markedFrame frame p) callers code)) rest post) :
    WP cfg (fuel + 31) (.next (atCode s limits base.toArray frame callers (headAfterCode ++ code)))
      (39 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let f := markedFrame frame p
  have h2 : 2 < frame.locals.size := by omega
  have hl : f.locals[2]? = some (.i32 p.header) := by simp only [f,markedFrame,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt h2]
  have hp' : f.locals[1]? = some (.i32 p.pointer) := by simpa only [f,markedFrame,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_ne (by decide : 2 ≠ 1)] using hp
  have c9 : (markedFrom s op p).host.gas.Credits (30 * op + rest) := paid_credits s op 9 _ (hc.mono (by dsimp [op]; omega))
  have c36 : (sizedFrom s op p).host.gas.Credits (3 * op + rest) :=
    Deallocate.sized_credits (markedFrom s op p) op _ (c9.mono (by omega))
  have codeMark : Code (markedFrom s op p) f.inst p := by
    apply Code.transport s (markedFrom s op p) frame.inst p hcde
    · simp only [markedFrom,storeI32_funcs,paid_funcs]
    · simp only [markedFrom,storeI32_modules,paid_modules]
  have codeSize : Code (sizedFrom s op p) f.inst p := by
    apply Code.transport (markedFrom s op p) (sizedFrom s op p) frame.inst p codeMark
    · exact sized_funcs (markedFrom s op p) op
    · exact sized_modules (markedFrom s op p) op
  have m9initial : (paid s op 9).mems[p.memoryIndex]? = some p.memory := by simpa only [paid,chargedStore] using hm
  have m9 : (markedFrom s op p).mems[p.memoryIndex]? = some (markedMemory p) :=
    storeI32_memory (paid s op 9) p.memoryIndex p.header.toNat p.memory (readI32 p.memory p.header.toNat &&& 4294967294) m9initial
  have m36 : (sizedFrom s op p).mems[p.memoryIndex]? = some (markedMemory p) := by
    rw [sizedFrom,sized_mems]; exact m9
  have spec := writeI32_spec p.memory p.header.toNat (readI32 p.memory p.header.toNat &&& 4294967294)
    hnative.wf hnative.headerBound
  have hn : WP cfg fuel (.next (atCode (Deallocate.zeroStore (sizedFrom s op p) op p.memoryIndex (markedMemory p) p.pointer)
      limits base.toArray f callers code)) rest post := by simpa only [headAfter,f,op] using hnext
  have zero := Deallocate.wp_zero_link cfg fuel rest (sizedFrom s op p) limits base.toArray f callers code p.pointer p.mi
    p.memoryIndex (markedMemory p) post hp' codeSize.module hcde.memoryIndex m36
    (by rw [show (markedMemory p).byteSize = p.memory.byteSize from spec.2.1]; exact hnative.pointerBound)
    (c36.mono (by dsimp [op]; omega)) hn
  have hnSize : WP cfg (fuel + 3) (.next (atCode (Deallocate.sized (markedFrom s op p) cfg.regularOpCost) limits
      base.toArray f callers (WNear.Binary.Deallocate.zeroLink ++ code))) (3 * cfg.regularOpCost + rest) post := by
    simpa only [sizedFrom,op] using zero
  have size := Deallocate.wp_size_call cfg (fuel + 3) (3 * cfg.regularOpCost + rest) (markedFrom s op p) limits base f callers
    (WNear.Binary.Deallocate.zeroLink ++ code) p.header p.mi p.address576 p.memoryIndex (markedMemory p) post hl codeMark.module
    hcde.index576 codeMark.function576 hcde.memoryIndex m9 (by rw [show (markedMemory p).byteSize = p.memory.byteSize from spec.2.1]; exact hnative.headerBound)
    hnative.currentSize hd (c9.mono (by dsimp [op]; omega)) hnSize
  have next : WP cfg (fuel + 22) (.next (atCode (storeI32 (paid s cfg.regularOpCost 9) p.memoryIndex p.header.toNat
      p.memory (readI32 p.memory p.header.toNat &&& 4294967294)) limits base.toArray (markedFrame frame p) callers
      (WNear.Binary.Deallocate.sizeCall ++ WNear.Binary.Deallocate.zeroLink ++ code))) (30 * cfg.regularOpCost + rest) post := by
    simpa only [markedFrom,f,op,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
      show 27 * cfg.regularOpCost + (3 * cfg.regularOpCost + rest) = 30 * cfg.regularOpCost + rest by omega] using size
  have result := wp_mark_at cfg (fuel + 22) (30 * cfg.regularOpCost + rest) s limits base.toArray frame callers _ p post
    hp hs hcde.module hcde.memoryIndex hm hnative.headerEq hnative.headerBound (hc.mono (by omega)) next
  simpa only [headAfterCode,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
    show 9 * cfg.regularOpCost + (30 * cfg.regularOpCost + rest) = 39 * cfg.regularOpCost + rest by omega] using result

def headCode : Expr := headBeforeCode ++ headAfterCode

/-- All actual pre-neighbor work, including real alignment and size callees. -/
theorem wp_head (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post) (hr : Ready s frame p)
    (hd : callers.length + 2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (91 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (zeroed s cfg.regularOpCost p) limits base.toArray
      (headFrame frame p) callers code)) rest post) :
    WP cfg (fuel + 67) (.next (atCode s limits base.toArray frame callers (headCode ++ code)))
      (91 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have codes := saved_code s op frame.inst p hr.code
  have hm : (saved s op).mems[p.memoryIndex]? = some p.memory := by
    rw [saved,paid_mems,aligned,aligned_mems,guarded,paid_mems]; exact hr.memory
  have hp : (savedFrame frame p).locals[1]? = some (.i32 p.pointer) := by
    simpa only [savedFrame,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_ne (by decide : 4 ≠ 1)] using hr.pointer
  have hsize : 3 ≤ (savedFrame frame p).locals.size := by
    simp only [savedFrame,Array.size_set!]; have h := hr.locals; omega
  have hn : WP cfg fuel (.next (atCode (headAfter (saved s op) op p) limits base.toArray
      (markedFrame (savedFrame frame p) p) callers code)) rest post := by
    simpa only [headAfter,sizedFrom,markedFrom,Deallocate.zeroStore,zeroed,sized,marked,headFrame,op] using hnext
  have tail := wp_head_after cfg fuel rest (saved s op) limits base (savedFrame frame p) callers code p post codes hm hp hsize
    hr.native (by omega) (saved_credits s op (39 * op + rest) (hc.mono (by dsimp [op]; omega))) hn
  have next : WP cfg (fuel + 31) (.next (atCode (saved s cfg.regularOpCost) limits base.toArray
      (savedFrame frame p) callers (headAfterCode ++ code))) (39 * cfg.regularOpCost + rest) post := by simpa only [op] using tail
  have result := wp_head_before cfg (fuel + 31) (39 * cfg.regularOpCost + rest) s limits base frame callers
    (headAfterCode ++ code) p post hr hd (hc.mono (by omega)) next
  simpa only [headCode,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
    show 52 * cfg.regularOpCost + (39 * cfg.regularOpCost + rest) = 91 * cfg.regularOpCost + rest by omega] using result

end WNear.Proofs.DeallocateInsert
