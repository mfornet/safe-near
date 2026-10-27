import Proofs.InterfaceSetPhases
import Proofs.ValueReturnOuterBody

/-! The real initialized-thread-local lookup, nonzero guard and borrow arguments. -/
namespace WNear.Proofs.InterfaceSetHead
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open WNear.Proofs.InterfaceSetState
set_option maxRecDepth 16384
set_option maxHeartbeats 300000

def looked (s : Store NearState) (op : Nat) := ValueReturnThreadLocal.indirectAfter (paid s op 2) op

def after (s : Store NearState) (op : Nat) := paid (paid (looked s op) op 3) op 5

def guarded (frame : CallFrame) := {frame with locals := frame.locals.set! 0 (.i32 1074904)}

/-- This prefix executes the actual indirect lookup and scalar instructions,
stopping immediately before the real441 call. -/
theorem wp_head (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (memory : Memory) (post : Post)
    (hcode : Code s p frame.inst) (hinterface : frame.locals[0]? = some (.i32 p.interface))
    (hscratch : frame.locals[3]? = some (.i32 (scratch p))) (hsize : 4 ≤ frame.locals.size)
    (hmem : s.mems[p.memoryIndex]? = some memory)
    (hbound : p.interface.toNat + 4 ≤ memory.byteSize)
    (hread : readI32 memory p.interface.toNat = p.lookupElement)
    (hthreadBound : 1074900 + 4 ≤ memory.byteSize) (hthreadStatus : readI32 memory 1074900 = 1)
    (hdepth : callers.length + 2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (39 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost) limits
      (base ++ [Value.i32 (scratch p + 8), .i32 1074904, .i32 1055120]).toArray (guarded frame) callers
      (.call 441 :: code))) rest post) :
    WP cfg (fuel + 25) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.InterfaceSet.lookup ++ WNear.Binary.InterfaceSet.acquire ++ code)))
      (39 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let l := paid s op 2
  let k := looked s op
  let g := paid k op 3
  let gf := guarded frame
  have cl : l.host.gas.Credits (37 * op + rest) := paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  have ck : k.host.gas.Credits (8 * op + rest) := ValueReturnThreadLocal.indirectAfter_credits l op _ (cl.mono (by omega))
  have cg : g.host.gas.Credits (5 * op + rest) := paid_credits k op 3 _ (ck.mono (by omega))
  have hs : gf.locals[3]? = some (.i32 (scratch p)) := by simpa [gf, guarded] using hscratch
  have hcell : gf.locals[0]? = some (.i32 1074904) := by simp [gf, guarded, show 0 < frame.locals.size by omega]
  have argsStack : (base ++ [Value.i32 (scratch p + 8), .i32 1074904, .i32 1055120]).toArray =
      (((base.toArray.push (.i32 (scratch p + 8))).push (.i32 1074904)).push (.i32 1055120)) := by
    apply Array.toList_inj.mp; simp
  have argsNext : WP cfg fuel (.next (atCode (paid g op 5) limits
      (((base.toArray.push (.i32 (scratch p + 8))).push (.i32 1074904)).push (.i32 1055120)) gf callers (.call 441 :: code))) rest post := by
    simpa only [after, g, k, gf, op, argsStack] using hnext
  have args := InterfaceSetBody.wp_acquire_arguments cfg fuel rest g limits base.toArray gf callers
    (.call 441 :: code) (scratch p) 1074904 post hs hcell cg argsNext
  let argsCode : List Instr := [.local_get 3, .i32_const 8, .i32_binop .add, .local_get 0, .i32_const 1055120, .call 441] ++ code
  have guardNext : WP cfg (fuel + 5) (.next (atCode (paid k op 3) limits base.toArray
      {frame with locals := frame.locals.set! 0 (.i32 1074904)} callers argsCode)) (5 * op + rest) post := by
    simpa only [argsCode, g, gf, guarded, List.cons_append, List.nil_append, op] using args
  have guard := ValueReturnOuter.wp_cell_guard cfg (fuel + 5) (5 * op + rest) k limits base.toArray frame callers
    argsCode 1074904 post (by decide) (ck.mono (by omega)) guardNext
  let lookupCode := WNear.Binary.InterfaceSet.acquire ++ code
  have guardStart : WP cfg ((fuel + 5) + 3) (.next (atCode k limits
      (base ++ [Value.i32 1074904]).toArray frame callers lookupCode)) (3 * op + (5 * op + rest)) post := by
    have stackEq : (base ++ [Value.i32 1074904]).toArray = base.toArray.push (.i32 1074904) := by
      apply Array.toList_inj.mp; simp
    simpa only [lookupCode, WNear.Binary.InterfaceSet.acquire, argsCode, List.cons_append, List.nil_append, stackEq, op] using guard
  have hm : l.modules[frame.inst]? = some p.mi := by simpa only [l, paid, chargedStore] using hcode.module
  have ht : l.tables[p.tableAddress]? = some p.table := by simpa only [l, paid, chargedStore] using hcode.table
  have hf : l.funcs[565]? = some (.wasm WNear.Binary.ValueReturnThreadLocal.lookupSignature frame.inst WNear.Binary.ValueReturnThreadLocal.lookupFunction) := by
    simpa only [l, paid, chargedStore] using hcode.lookupFunction
  have hh : l.funcs[468]? = some (.wasm WNear.Binary.ValueReturnThreadLocal.signature frame.inst WNear.Binary.ValueReturnThreadLocal.function) := by
    simpa only [l, paid, chargedStore] using hcode.helperFunction
  have hml : l.mems[p.memoryIndex]? = some memory := by simpa only [l, paid, chargedStore] using hmem
  have indirect := ValueReturnThreadLocal.wp_indirect_lookup cfg ((fuel + 5) + 3) (3 * op + (5 * op + rest)) l limits base frame callers
    lookupCode p.mi p.tableAddress 565 468 p.memoryIndex p.lookupElement p.table memory post hm hcode.tableIndex ht
    hcode.lookupElement hcode.lookupType hf hcode.helperIndex hh hcode.memoryIndex hml hthreadBound hthreadStatus hdepth
    (cl.mono (by omega)) guardStart
  have stackEq : (base ++ [Value.i32 p.lookupElement]).toArray = base.toArray.push (.i32 (readI32 memory p.interface.toNat)) := by
    rw [hread]; apply Array.toList_inj.mp; simp
  have lookupNext : WP cfg (((fuel + 5) + 3) + 15) (.next (atCode l limits
      (base.toArray.push (.i32 (readI32 memory p.interface.toNat))) frame callers (.call_indirect 1 0 :: lookupCode)))
      (29 * op + (3 * op + (5 * op + rest))) post := by simpa only [stackEq, hread, op] using indirect
  have result := ValueReturnOuter.wp_lookup_argument cfg (((fuel + 5) + 3) + 15) (29 * op + (3 * op + (5 * op + rest)))
    s limits base.toArray frame callers (.call_indirect 1 0 :: lookupCode) p.interface p.mi p.memoryIndex memory post
    hinterface hcode.module hcode.memoryIndex hmem hbound (hc.mono (by dsimp [op]; omega)) lookupNext
  have fe : fuel + 5 + 3 + 15 + 2 = fuel + 25 := by omega
  have ge : 2 * cfg.regularOpCost + (29 * op + (3 * op + (5 * op + rest))) = 39 * cfg.regularOpCost + rest := by dsimp [op]; omega
  have ce : [.local_get 0, .load .i32 none {align := 2, offset := 0}] ++ (.call_indirect 1 0 :: lookupCode) =
      WNear.Binary.InterfaceSet.lookup ++ WNear.Binary.InterfaceSet.acquire ++ code := by
    simp only [WNear.Binary.InterfaceSet.lookup, lookupCode, List.cons_append, List.nil_append]
  exact ValueReturnOuterBody.cast_phase cfg _ _ _ _ s limits base.toArray frame callers _ _ post fe ge ce result

end WNear.Proofs.InterfaceSetHead
