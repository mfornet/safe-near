import Proofs.PanicAllocateState

/-! Complete actual zero-size f508 body. -/
namespace WNear.Proofs.PanicAllocateBody
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open WNear.Proofs.PanicAllocateState
set_option maxRecDepth 16384
set_option maxHeartbeats 400000
attribute [local irreducible] WP readI32 writeI32 PanicAllocateZero.calledStore

private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems = s.mems := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- All24instructions of f508, including its actual zero-size509 invocation. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post) (hr : Ready s limits frame callers p)
    (hc : s.host.gas.Credits (45 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost p) limits base.toArray
      (afterFrame frame p) callers code)) rest post) :
    WP cfg (fuel + 39) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.PanicAllocate.body508 ++ code))) (45 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let f := afterFrame frame p
  have hs : f.locals[3]? = some (.i32 (scratch p)) := by simp [f, afterFrame, show 3 < frame.locals.size by have h := hr.localSize; omega]
  have hout : f.locals[0]? = some (.i32 p.out) := by simpa [f, afterFrame] using hr.out
  have hz : f.locals[1]? = some (.i32 0) := by simpa [f, afterFrame] using hr.size
  have hal : f.locals[2]? = some (.i32 p.alignment) := by simpa [f, afterFrame] using hr.alignment
  have hs8 : (scratch p + 8).toNat = (scratch p).toNat + 8 := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat]
    rw [Nat.mod_eq_of_lt]
    have hb := hr.scratchBound; have hw := hr.width; omega
  have hb509 : (scratch p + 8).toNat + 8 ≤ p.memory.byteSize := by rw [hs8]; exact hr.scratchBound
  have spec := PanicAllocateZero.zeroMemory_spec p.memory (scratch p + 8).toNat p.alignment hr.wf hb509
  have hbLow : p.out.toNat + 4 ≤ (allocatedMemory p).byteSize := by rw [show (allocatedMemory p).byteSize = p.memory.byteSize from spec.2.1]; have h := hr.outBound; omega
  have specLow := writeI32_spec (allocatedMemory p) p.out.toNat (readI32 (allocatedMemory p) ((scratch p).toNat + 8)) spec.1 hbLow
  have mLowSize : (lowMemory p).byteSize = p.memory.byteSize := specLow.2.1.trans spec.2.1
  have cR : (reserved s op p).host.gas.Credits (40 * op + rest) := paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  have cArgs : (arguments s op p).host.gas.Credits (22 * op + (12 * op + rest)) :=
    paid_credits (reserved s op p) op 6 _ (cR.mono (by omega))
  have cAlloc : (allocated s op p).host.gas.Credits (12 * op + rest) :=
    PanicAllocateZero.calledStore_credits (arguments s op p) op p.memoryIndex _ (scratch p + 8) p.alignment p.memory cArgs
  have cLow : (low s op p).host.gas.Credits (8 * op + rest) :=
    PanicAllocateCopy.copyStore_credits (allocated s op p) op p.memoryIndex 8 0 _ (scratch p) p.out (allocatedMemory p) (cAlloc.mono (by omega))
  have cHigh : (high s op p).host.gas.Credits (4 * op + rest) :=
    PanicAllocateCopy.copyStore_credits (low s op p) op p.memoryIndex 12 4 _ (scratch p) p.out (lowMemory p) (cLow.mono (by omega))
  have hmArgs : (arguments s op p).modules[f.inst]? = some p.mi := by simpa only [arguments, reserved, paid, chargedStore, setGlobal, f, afterFrame] using hr.module
  have hfArgs : (arguments s op p).funcs[509]? = some (.wasm WNear.Binary.PanicAllocateZero.signature f.inst WNear.Binary.PanicAllocateZero.function) := by
    simpa only [arguments, reserved, paid, chargedStore, setGlobal, f, afterFrame] using hr.function
  have hmemArgs : (arguments s op p).mems[p.memoryIndex]? = some p.memory := by simpa only [arguments, reserved, paid_mems, setGlobal] using hr.memory
  have res := PanicAllocateZero.calledStore_resources (arguments s op p) op p.memoryIndex (scratch p + 8) p.alignment p.memory
  have mods := congrArg (fun t : Store NearState => t.modules) res
  have globs := congrArg (fun t : Store NearState => t.globals) res
  have hmAlloc : (allocated s op p).modules[f.inst]? = some p.mi := by
    change (allocated s op p).modules = (arguments s op p).modules at mods
    rw [mods]; exact hmArgs
  have hmemAlloc : (allocated s op p).mems[p.memoryIndex]? = some (allocatedMemory p) :=
    PanicAllocateZero.calledStore_memory (arguments s op p) op p.memoryIndex (scratch p + 8) p.alignment p.memory hmemArgs
  have hmemLow : (low s op p).mems[p.memoryIndex]? = some (lowMemory p) := by
    have hp : (paid (allocated s op p) op 4).mems[p.memoryIndex]? = some (allocatedMemory p) := by rw [paid_mems]; exact hmemAlloc
    simpa only [low, PanicAllocateCopy.copyStore, lowMemory, Nat.add_zero] using
      storeI32_memory (paid (allocated s op p) op 4) p.memoryIndex p.out.toNat (allocatedMemory p) (readI32 (allocatedMemory p) ((scratch p).toNat + 8)) hp
  have hmLow : (low s op p).modules[f.inst]? = some p.mi := by simpa only [low, PanicAllocateCopy.copyStore, storeI32_modules, paid, chargedStore] using hmAlloc
  have hmHigh : (high s op p).modules[f.inst]? = some p.mi := by simpa only [high, PanicAllocateCopy.copyStore, storeI32_modules, paid, chargedStore] using hmLow
  have hgArgs : (arguments s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
    simp only [arguments, reserved, paid, chargedStore, setGlobal]
    simp [Array.getElem?_modify, hr.global]
  have hgAlloc : (allocated s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
    change (allocated s op p).globals = (arguments s op p).globals at globs
    rw [globs]; exact hgArgs
  have hgHigh : (high s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
    simpa only [high, low, PanicAllocateCopy.copyStore, storeI32_globals, paid, chargedStore] using hgAlloc
  have restore := InterfaceStack.wp_restore cfg fuel rest (high s op p) limits base.toArray f callers code p.mi p.globalIndex
    {p.global with value := .i32 (scratch p)} (scratch p) 3 16 post hs hmHigh hr.globalIndex hgHigh cHigh hnext
  let highCode := [.local_get 0, .local_get 3, .load .i32 none {align := 2, offset := 12}, .store .i32 none {align := 2, offset := 4}] ++
    WNear.Binary.PanicAllocate.epilogue508 ++ code
  have hReadHigh : (scratch p).toNat + 12 + 4 ≤ (lowMemory p).byteSize := by rw [mLowSize]; exact hr.scratchBound
  have hWriteHigh : p.out.toNat + 4 + 4 ≤ (lowMemory p).byteSize := by rw [mLowSize]; exact hr.outBound
  have copiedHigh := PanicAllocateCopy.wp_copy cfg (fuel + 4) (4 * op + rest) (low s op p) limits base.toArray f callers
    (WNear.Binary.PanicAllocate.epilogue508 ++ code) 3 0 12 4 (scratch p) p.out p.mi p.memoryIndex (lowMemory p) post
    hs hout hmLow hr.memoryIndex hmemLow hReadHigh hWriteHigh (cLow.mono (by omega)) restore
  have hReadLow : (scratch p).toNat + 8 + 4 ≤ (allocatedMemory p).byteSize := by rw [show (allocatedMemory p).byteSize = p.memory.byteSize from spec.2.1]; have h := hr.scratchBound; omega
  have lowNext : WP cfg (fuel + 4 + 4) (.next (atCode (low s op p) limits base.toArray f callers highCode)) (8 * op + rest) post := by
    have ge : 4 * cfg.regularOpCost + (4 * op + rest) = 8 * op + rest := by dsimp [op]; omega
    simpa only [ge, highCode, List.append_assoc] using copiedHigh
  have copiedLow := PanicAllocateCopy.wp_copy cfg (fuel + 4 + 4) (8 * op + rest) (allocated s op p) limits base.toArray f callers
    highCode 3 0 8 0 (scratch p) p.out p.mi p.memoryIndex (allocatedMemory p) post hs hout hmAlloc hr.memoryIndex hmemAlloc
    hReadLow (by simpa only [Nat.add_zero] using hbLow) (cAlloc.mono (by omega)) lowNext
  let callCode := WNear.Binary.PanicAllocate.copies508 ++ WNear.Binary.PanicAllocate.epilogue508 ++ code
  have callNext : WP cfg (fuel + 12) (.next (atCode (allocated s op p) limits base.toArray f callers callCode)) (12 * op + rest) post := by
    have ge : 4 * cfg.regularOpCost + (8 * op + rest) = 12 * op + rest := by dsimp [op]; omega
    simpa only [ge, callCode, highCode, WNear.Binary.PanicAllocate.copies508, List.append_assoc, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd] using copiedLow
  have called := PanicAllocateZero.wp_call cfg (fuel + 12) (12 * op + rest) (arguments s op p) limits base f callers callCode
    (scratch p + 8) p.alignment 0 p.mi 509 p.memoryIndex p.memory post hmArgs hr.functionIndex hfArgs hr.memoryIndex hmemArgs hr.wf hb509 hr.depth cArgs callNext
  have stackEq : (base ++ [Value.i32 (scratch p + 8), .i32 0, .i32 p.alignment, .i32 0]).toArray =
      ((((base.toArray.push (.i32 (scratch p + 8))).push (.i32 0)).push (.i32 p.alignment)).push (.i32 0)) := by apply Array.toList_inj.mp; simp
  have argsNext : WP cfg (fuel + 12 + 16) (.next (atCode (paid (reserved s op p) op 6) limits
      ((((base.toArray.push (.i32 (scratch p + 8))).push (.i32 0)).push (.i32 p.alignment)).push (.i32 0)) f callers (.call 509 :: callCode)))
      (22 * op + (12 * op + rest)) post := by simpa only [stackEq, arguments, op] using called
  have args := PanicAllocateArguments.wp_arguments508 cfg (fuel + 12 + 16) (22 * op + (12 * op + rest)) (reserved s op p)
    limits base.toArray f callers (.call 509 :: callCode) (scratch p) 0 p.alignment post hs hz hal (cR.mono (by omega)) argsNext
  have reserveNext : WP cfg (fuel + 12 + 16 + 6) (.next (atCode (reserved s op p) limits base.toArray f callers
      (WNear.Binary.PanicAllocate.arguments508 ++ .call 509 :: callCode))) (40 * op + rest) post := by
    have ge : 6 * cfg.regularOpCost + (22 * op + (12 * op + rest)) = 40 * op + rest := by dsimp [op]; omega
    simpa only [ge] using args
  have result := InterfaceStack.wp_reserve cfg (fuel + 12 + 16 + 6) (40 * op + rest) s limits base.toArray frame callers
    (WNear.Binary.PanicAllocate.arguments508 ++ .call 509 :: callCode) p.mi p.globalIndex p.global p.sp 3 16 post
    hr.module hr.globalIndex hr.global hr.sp (hc.mono (by dsimp [op]; omega)) reserveNext
  have fe : fuel + 12 + 16 + 6 + 5 = fuel + 39 := by omega
  have ge : 5 * cfg.regularOpCost + (40 * op + rest) = 45 * cfg.regularOpCost + rest := by dsimp [op]; omega
  have ce : [.global_get 0, .i32_const 16, .i32_binop .sub, .local_tee 3, .global_set 0] ++
      (WNear.Binary.PanicAllocate.arguments508 ++ .call 509 :: callCode) = WNear.Binary.PanicAllocate.body508 ++ code := by
    simp only [WNear.Binary.PanicAllocate.body508, WNear.Binary.PanicAllocate.prologue508, callCode,
      List.append_assoc, List.cons_append, List.nil_append]
  exact ValueReturnOuterBody.cast_phase cfg _ _ _ _ s limits base.toArray frame callers _ _ post fe ge ce result

end WNear.Proofs.PanicAllocateBody
