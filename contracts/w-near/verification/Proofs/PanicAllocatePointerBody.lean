import Proofs.PanicAllocatePointerGuard
import Proofs.PanicAllocatePointerFrame

/-! Complete actual f503 zero-size path, returning its proved allocation pointer. -/
namespace WNear.Proofs.PanicAllocatePointerBody
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open WNear.Proofs.PanicAllocatePointerState
set_option maxRecDepth 16384
set_option maxHeartbeats 400000
attribute [local irreducible] WP PanicAllocateZero.calledStore

theorem native_bounds (p : Layout) (hl : 32 ≤ p.sp.toNat) (hb : p.sp.toNat ≤ p.memory.byteSize) :
    (PanicAllocateState.scratch (inner p)).toNat + 16 ≤ p.memory.byteSize ∧
    (inner p).out.toNat + 8 ≤ p.memory.byteSize := by
  have hs : (scratch p).toNat = p.sp.toNat - 16 := StorePairAddresses.sub_sixteen p.sp (by omega)
  have hn : 16 ≤ (scratch p).toNat := by omega
  have hs2 := StorePairAddresses.sub_sixteen (scratch p) hn
  have ha : (scratch p + 8).toNat = (scratch p).toNat + 8 := by
    rw [UInt32.toNat_add]
    change ((scratch p).toNat + 8) % 2 ^ 32 = (scratch p).toNat + 8
    have hw := UInt32.toNat_lt p.sp
    rw [Nat.mod_eq_of_lt (by omega)]
  constructor
  · change (scratch p - 16).toNat + 16 ≤ p.memory.byteSize
    rw [hs2]; omega
  · change (scratch p + 8).toNat + 8 ≤ p.memory.byteSize
    rw [ha]; omega

/-- Native initial stack bounds imply the actual post-memory and pointerone. -/
theorem final_spec (p : Layout) (hw : p.memory.wf) (hwidth : p.memory.byteSize ≤ 2 ^ 32)
    (hl : 32 ≤ p.sp.toNat) (hb : p.sp.toNat ≤ p.memory.byteSize) :
    (finalMemory p).wf ∧ (finalMemory p).byteSize = p.memory.byteSize ∧
    (finalMemory p).max = p.memory.max ∧ readI32 (finalMemory p) (scratch p + 8).toNat = 1 := by
  have hn := native_bounds p hl hb
  exact PanicAllocateNative.final_spec (inner p) hw hwidth hn.1 hn.2

/-- The full real503body follows the nonzero pointer produced by508, bypassing842. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post) (hr : Ready s limits frame callers p)
    (hc : s.host.gas.Credits (75 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost p) limits (base.toArray.push (.i32 1))
      (finalFrame frame p) callers code)) rest post) :
    WP cfg (fuel + 61) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.PanicAllocate.body503 ++ code))) (75 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let f := preparedFrame frame p
  let ff := finalFrame frame p
  let q := inner p
  have hsNat : (scratch p).toNat = p.sp.toNat - 16 := StorePairAddresses.sub_sixteen p.sp (by have h := hr.spLower; omega)
  have hs8 : (scratch p + 8).toNat = (scratch p).toNat + 8 := by
    rw [UInt32.toNat_add]
    change ((scratch p).toNat + 8) % 2 ^ 32 = (scratch p).toNat + 8
    have hu := UInt32.toNat_lt p.sp; have hl := hr.spLower
    rw [Nat.mod_eq_of_lt (by omega)]
  have hb := native_bounds p hr.spLower hr.stackBound
  have spec := final_spec p hr.wf hr.width hr.spLower hr.stackBound
  have hs : f.locals[2]? = some (.i32 (scratch p)) := by simp [f, preparedFrame, show 2 < frame.locals.size by have h := hr.localSize; omega]
  have hz : f.locals[0]? = some (.i32 0) := by simpa [f, preparedFrame] using hr.size
  have hal : f.locals[1]? = some (.i32 1) := by simpa [f, preparedFrame] using hr.alignment
  have h3 : ff.locals[3]? = some (.i32 1) := by simp [ff, finalFrame, preparedFrame, show 3 < frame.locals.size by have h := hr.localSize; omega]
  have hsFinal : ff.locals[2]? = some (.i32 (scratch p)) := by simpa [ff, finalFrame] using hs
  have cArg := (arguments_gas s op (65 * op + rest) p (hc.mono (by dsimp [op]; omega))).2.2
  have cAlloc := (allocated_gas s op (9 * op + rest) p (hc.mono (by dsimp [op]; omega))).2.2
  have cChecked := (checked_gas s op (5 * op + rest) p (hc.mono (by dsimp [op]; omega))).2.2
  have cRestored := (restored_gas s op (op + rest) p (hc.mono (by dsimp [op]; omega))).2.2
  have af := arguments_fields s op p
  have allocf := allocated_fields s op p
  have hmArg : (arguments s op p).modules[f.inst]? = some p.mi := by rw [af.2.1]; exact hr.module
  have hfArg : (arguments s op p).funcs[508]? = some (.wasm WNear.Binary.PanicAllocate.signature508 f.inst WNear.Binary.PanicAllocate.function508) := by rw [af.1]; exact hr.function508
  have hmemArg := arguments_memory s op p hr.memory
  have hgArg := arguments_global s op p hr.global
  have enteredReady : PanicAllocateState.Ready (PanicAllocateCall.entered (arguments s op p) op) limits
      (PanicAllocateCall.leaf f.inst base.length q) ({f with code := .block .empty WNear.Binary.PanicAllocate.guard503 :: (WNear.Binary.PanicAllocate.epilogue503 ++ code)} :: callers) q := by
    constructor
    · simpa only [PanicAllocateCall.entered, chargedStore, PanicAllocateCall.leaf, q, inner] using hmArg
    · exact hr.globalIndex
    · simpa only [PanicAllocateCall.entered, chargedStore, q, inner] using hgArg
    · rfl
    · exact hr.memoryIndex
    · simpa only [PanicAllocateCall.entered, chargedStore, q, inner] using hmemArg
    · exact hr.function509Index
    · have hf509 : (arguments s op p).funcs[509]? = some (.wasm WNear.Binary.PanicAllocateZero.signature frame.inst WNear.Binary.PanicAllocateZero.function) := by
        rw [af.1]; exact hr.function509
      simpa only [PanicAllocateCall.entered, chargedStore, PanicAllocateCall.leaf, q, inner, f, preparedFrame] using hf509
    · rfl
    · rfl
    · rfl
    · simp [PanicAllocateCall.leaf]
    · exact hr.wf
    · exact hr.width
    · exact hb.1
    · exact hb.2
    · have h := hr.depth; simp only [List.length_cons]; omega
  have hmAlloc : (allocated s op p).modules[ff.inst]? = some p.mi := by rw [allocf.2.1]; exact hr.module
  have hmChecked : (checked s op p).modules[ff.inst]? = some p.mi := by simpa only [checked, paid, chargedStore] using hmAlloc
  have hgChecked : (checked s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
    simpa only [checked, paid, chargedStore] using allocated_global s op p hr.global
  have get := wp_local_get cfg fuel rest (restored s op p) limits base.toArray ff callers code 3 (.i32 1) post h3 cRestored hnext
  have restore := InterfaceStack.wp_restore cfg (fuel + 1) (op + rest) (checked s op p) limits base.toArray ff callers
    (.local_get 3 :: code) p.mi p.globalIndex {p.global with value := .i32 (scratch p)} (scratch p) 2 16 post
    hsFinal hmChecked hr.globalIndex hgChecked (cChecked.mono (by dsimp [op]; omega)) get
  have hRead : readI32 (finalMemory p) ((scratch p).toNat + 8) = 1 := by rw [← hs8]; exact spec.2.2.2
  have hReadBound : (scratch p).toNat + 8 + 4 ≤ (finalMemory p).byteSize := by
    rw [spec.2.1]; have h := hr.spLower; have hb := hr.stackBound; omega
  have hmAllocF : (allocated s op p).modules[f.inst]? = some p.mi := by rw [allocf.2.1]; exact hr.module
  have guardNext : WP cfg (fuel + 1 + 4) (.next (atCode (paid (allocated s op p) op 4) limits base.toArray
      (PanicAllocatePointerGuard.guardFrame f 1) callers (WNear.Binary.PanicAllocate.epilogue503 ++ code))) (5 * op + rest) post := by
    have ge : 4 * cfg.regularOpCost + (op + rest) = 5 * op + rest := by dsimp [op]; omega
    simpa only [ge, WNear.Binary.PanicAllocate.epilogue503, checked, restored, ff, finalFrame,
      PanicAllocatePointerGuard.guardFrame, f, List.cons_append, List.nil_append] using restore
  have guarded := PanicAllocatePointerGuard.wp_guard cfg (fuel + 1 + 4) (5 * op + rest) (allocated s op p) limits base.toArray f callers
    (WNear.Binary.PanicAllocate.epilogue503 ++ code) (scratch p) 1 p.mi p.memoryIndex (finalMemory p) post hs hmAllocF hr.memoryIndex
    (allocated_memory s op p hr.memory) hReadBound hRead (by decide) (cAlloc.mono (by dsimp [op]; omega)) guardNext
  let callCode := .block .empty WNear.Binary.PanicAllocate.guard503 :: (WNear.Binary.PanicAllocate.epilogue503 ++ code)
  have guardStart : WP cfg (fuel + 10) (.next (atCode (allocated s op p) limits base.toArray f callers callCode)) (9 * op + rest) post := by
    have ge : 4 * cfg.regularOpCost + (5 * op + rest) = 9 * op + rest := by dsimp [op]; omega
    simpa only [ge, callCode, Nat.add_assoc, Nat.reduceAdd] using guarded
  have called := PanicAllocateCall.wp_call cfg (fuel + 10) (9 * op + rest) (arguments s op p) limits base f callers callCode q 508 post
    hmArg hr.function508Index hfArg enteredReady (cArg.mono (by omega)) guardStart
  have stackEq : (base ++ [Value.i32 (scratch p + 8), .i32 0, .i32 1]).toArray =
      (((base.toArray.push (.i32 (scratch p + 8))).push (.i32 0)).push (.i32 1)) := by apply Array.toList_inj.mp; simp
  have argsNext : WP cfg (fuel + 10 + 41) (.next (atCode (paid (reserved s op p) op 5) limits
      (((base.toArray.push (.i32 (scratch p + 8))).push (.i32 0)).push (.i32 1)) f callers (.call 508 :: callCode)))
      (56 * op + (9 * op + rest)) post := by simpa only [stackEq, allocated, arguments, q, inner, op] using called
  have cReserved : (reserved s op p).host.gas.Credits (70 * op + rest) := paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  have args := PanicAllocateArguments.wp_arguments5 cfg (fuel + 10 + 41) (56 * op + (9 * op + rest)) (reserved s op p)
    limits base.toArray f callers (.call 508 :: callCode) 2 0 1 (scratch p) 0 1 post hs hz hal (cReserved.mono (by omega)) argsNext
  have reserveNext : WP cfg (fuel + 10 + 41 + 5) (.next (atCode (reserved s op p) limits base.toArray f callers
      (WNear.Binary.PanicAllocate.arguments503 ++ .call 508 :: callCode))) (70 * op + rest) post := by
    have ge : 5 * cfg.regularOpCost + (56 * op + (9 * op + rest)) = 70 * op + rest := by dsimp [op]; omega
    simpa only [ge, WNear.Binary.PanicAllocate.arguments503] using args
  have result := InterfaceStack.wp_reserve cfg (fuel + 10 + 41 + 5) (70 * op + rest) s limits base.toArray frame callers
    (WNear.Binary.PanicAllocate.arguments503 ++ .call 508 :: callCode) p.mi p.globalIndex p.global p.sp 2 16 post
    hr.module hr.globalIndex hr.global hr.sp (hc.mono (by dsimp [op]; omega)) reserveNext
  have fe : fuel + 10 + 41 + 5 + 5 = fuel + 61 := by omega
  have ge : 5 * cfg.regularOpCost + (70 * op + rest) = 75 * cfg.regularOpCost + rest := by dsimp [op]; omega
  have ce : [.global_get 0, .i32_const 16, .i32_binop .sub, .local_tee 2, .global_set 0] ++
      (WNear.Binary.PanicAllocate.arguments503 ++ .call 508 :: callCode) = WNear.Binary.PanicAllocate.body503 ++ code := by
    simp only [WNear.Binary.PanicAllocate.body503, WNear.Binary.PanicAllocate.prologue503, callCode,
      List.append_assoc, List.cons_append, List.nil_append]
  exact ValueReturnOuterBody.cast_phase cfg _ _ _ _ s limits base.toArray frame callers _ _ post fe ge ce result

end WNear.Proofs.PanicAllocatePointerBody
