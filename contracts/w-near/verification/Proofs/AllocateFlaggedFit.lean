import Proofs.AllocateFlaggedNative

/-! Actual pure fit prefix, including the real layout callback and byte scaling. -/
namespace WNear.Proofs.AllocateFlagged
open Wasm Wasm.Near MeteredLogic
open AllocateSearch
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 900000
attribute [local irreducible] WP atCode readI32 Allocate.callbackAfter AllocateUnits.unitsAfter AllocateUnits.quantumAfter

/-- Actual end/overflow checks, indirect578,572, and all five split guards.
Only original code/native heap/local facts are supplied. -/
theorem wp_fit_prefix (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hr : FitReady frame p)
    (hcode : Code s p frame.inst) (hmem : s.mems[p.memoryIndex]? = some p.memory)
    (hd : callers.length+1 < limits.maxCallDepth) (hc : s.host.gas.Credits (83*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (arithmeticDone s cfg.regularOpCost) limits stack (splitFrame frame p) callers code)) rest post) :
    WP cfg (fuel+68) (.next (atCode s limits stack frame callers
      (WNear.Binary.Allocate.fitHeader++WNear.Binary.Allocate.callbackCode++WNear.Binary.Allocate.splitArithmetic++code)))
      (83*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let subtracted := endSubtracted s op
  let callback := callbackDone s op
  let f1 := Allocate.fitFrame frame p.memory (head p) p.words
  let f2 := Allocate.callbackFrame f1
  have v11 : 11 < frame.locals.size := by have := hr.localSize; omega
  have v12 : 12 < frame.locals.size := by have := hr.localSize; omega
  have v13 : 13 < frame.locals.size := by have := hr.localSize; omega
  have base : f2.locals[9]? = some (.i32 (head p+8)) := by simp [f2,f1,Allocate.callbackFrame,Allocate.fitFrame,hr.dataBase]
  have quantum : f2.locals[13]? = some (.i32 64) := by simp [f2,f1,Allocate.callbackFrame,Allocate.fitFrame,v13]
  have pointer : f2.locals[12]? = some (.i32 (Allocate.splitPointer p.memory (head p) p.words)) := by simp [f2,f1,Allocate.callbackFrame,Allocate.fitFrame,v12]
  have mask : f2.locals[6]? = some (.i32 4294967295) := by simp [f2,f1,Allocate.callbackFrame,Allocate.fitFrame,hr.alignmentMask]
  have finish : f2.locals[11]? = some (.i32 (Allocate.endWord p.memory (head p))) := by simp [f2,f1,Allocate.callbackFrame,Allocate.fitFrame,v11]
  have size : 14 ≤ f2.locals.size := by simpa [f2,f1,Allocate.callbackFrame,Allocate.fitFrame] using hr.localSize
  have csub : subtracted.host.gas.Credits (70*op+rest) := paid_credits s op 13 _ (hc.mono (by dsimp [op]; omega))
  have cback : callback.host.gas.Credits (35*op+rest) :=
    Allocate.callbackAfter_credits subtracted op (35*op+rest) (csub.mono (by omega))
  have arithmeticNext : WP cfg fuel (.next (atCode (paid callback op 35) limits stack
      (Allocate.arithmeticFrame f2 p.memory (head p) p.words) callers code)) rest post := by
    simpa only [callback,arithmeticDone,splitFrame,f2,f1,op] using hnext
  have arithmetic := Allocate.wp_split_arithmetic cfg fuel rest callback limits stack f2 callers code p.memory (head p) p.words post
    base quantum pointer mask finish size hn.split cback arithmeticNext
  have subCode := hcode.paid s op 13 p frame.inst
  have subMemory : subtracted.mems[p.memoryIndex]? = some p.memory := by simpa only [subtracted,endSubtracted,paid,chargedStore] using hmem
  have context : f1.locals[3]? = some (.i32 p.context) := by simp [f1,Allocate.fitFrame,hr.context]
  have words : f1.locals[0]? = some (.i32 p.words) := by simp [f1,Allocate.fitFrame,hr.words]
  have vtable : f1.locals[4]? = some (.i32 p.vtable) := by simp [f1,Allocate.fitFrame,hr.vtable]
  have callbackNext : WP cfg (fuel+35) (.next (atCode (Allocate.callbackAfter subtracted op) limits stack (Allocate.callbackFrame f1) callers
      (WNear.Binary.Allocate.splitArithmetic++code))) (35*op+rest) post := arithmetic
  have callbackProof := Allocate.wp_callback cfg (fuel+35) (35*op+rest) subtracted limits stack.toList f1 callers
    (WNear.Binary.Allocate.splitArithmetic++code) p.context p.words p.vtable p.mi p.memoryIndex p.memory
    p.tableAddress p.callbackAddress p.callbackInst p.unitsAddress p.table post context words vtable
    subCode.module subCode.memoryIndex subMemory hn.vtableBound subCode.tableIndex subCode.table subCode.callbackElement
    subCode.callbackType subCode.callbackFunction subCode.unitsIndex subCode.unitsFunction hd
    (csub.mono (by dsimp [op]; omega)) (by simpa only [Array.toArray_toList] using callbackNext)
  have fitNext : WP cfg (fuel+55) (.next (atCode subtracted limits stack f1 callers
      (WNear.Binary.Allocate.callbackCode++WNear.Binary.Allocate.splitArithmetic++code))) (70*op+rest) post := by
    have cost : 35*cfg.regularOpCost+(35*op+rest)=70*op+rest := by dsimp [op]; omega
    rw [cost] at callbackProof
    simpa only [Array.toArray_toList,Nat.add_assoc,Nat.reduceAdd,List.append_assoc] using callbackProof
  have bounds := intervals p hn
  have result := Allocate.wp_fit_header cfg (fuel+55) (70*op+rest) s limits stack frame callers
    (WNear.Binary.Allocate.callbackCode++WNear.Binary.Allocate.splitArithmetic++code) (head p) p.words p.mi p.memoryIndex p.memory post
    hr.headLocal hr.byteCount hr.alignmentFlag (by have := hr.localSize; omega) hcode.module hcode.memoryIndex hmem
    (by omega) hn.split (hc.mono (by dsimp [op]; omega)) fitNext
  have cost : 13*cfg.regularOpCost+(70*op+rest)=83*cfg.regularOpCost+rest := by dsimp [op]; omega
  rw [cost] at result
  simpa only [Nat.add_assoc,Nat.reduceAdd,List.append_assoc] using result
end WNear.Proofs.AllocateFlagged
