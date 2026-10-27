import Proofs.DeallocateAlignBody

/-! Actual typed local calls to deployed checked ceiling division helpers. -/
namespace WNear.Proofs.DeallocateAlign
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits paid_gas)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP

def entered568 (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (10 * op)
def after568 (s : Store NearState) (op : Nat) := paid (entered568 s op) op 18

theorem entered568_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (11 * op + rest)) : (entered568 s op).host.gas.Credits rest := by
  have c := StorePair.charged_credits s op (10 * op + rest) (hc.mono (by omega))
  exact StorePair.charged_credits (chargedStore s op) (10 * op) rest c

theorem after568_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (29 * op + rest)) : (after568 s op).host.gas.Credits rest := by
  exact paid_credits (entered568 s op) op 18 rest (entered568_credits s op (18 * op + rest) (hc.mono (by omega)))

/-- Actual f568 local call and its explicit one-result return. -/
theorem wp_call568 (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (a b : UInt32) (mi : ModuleInst) (address : Nat) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.funcAddrs[568]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.DeallocateAlign.signature568 frame.inst WNear.Binary.DeallocateAlign.function568))
    (hadd : Numeric.irelop32 .lt_u (a + b) a = false)
    (hsub : Numeric.irelop32 .gt_u (a + b + 4294967295) (a + b) = false)
    (hn : b ≠ 0) (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (29 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after568 s cfg.regularOpCost) limits
      (base ++ [Value.i32 (quotient a b)]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 21) (.next (atCode s limits (base ++ [Value.i32 a, .i32 b]).toArray frame callers (.call 568 :: code)))
      (29 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let leaf : CallFrame := {locals := #[Value.i32 a, .i32 b, .i32 0], inst := frame.inst, arity := 1, height := base.length, labels := [], code := []}
  let saved := {frame with code}
  have ca := entered568_credits s op (18 * op + rest) (hc.mono (by dsimp [op]; omega))
  have bodyNext : WP cfg fuel (.next (atCode (paid (entered568 s op) op 18) limits
      (base ++ [Value.i32 (quotient a b)]).toArray saved callers saved.code)) rest post := by
    simpa only [after568, saved, atCode, op] using hnext
  have body := wp_body568 cfg fuel rest (entered568 s op) limits base leaf saved callers [] a b post
    rfl rfl (by simp [leaf]) hadd hsub hn rfl rfl ca bodyNext
  have callRule := wp_call_wasm cfg (fuel + 20) (18 * op + rest) s limits base [.i32 a, .i32 b] frame callers code 568 address mi
    WNear.Binary.DeallocateAlign.signature568 frame.inst WNear.Binary.DeallocateAlign.function568 post hm hi hf rfl hd
  have ha : activationGas op (wasmLocals WNear.Binary.DeallocateAlign.function568 [.i32 a, .i32 b]) = 10 * op := by
    simp [activationGas, wasmLocals, WNear.Binary.DeallocateAlign.function568, ValType.default]
  rw [ha] at callRule
  have arrays : #[Value.i32 a, Value.i32 b] ++ #[Value.i32 0] = #[Value.i32 a, Value.i32 b, Value.i32 0] := by
    apply Array.toList_inj.mp
    simp
  have next : WP cfg (fuel + 20) (.next (wasmCallee (entered568 s op) limits base frame callers code
      WNear.Binary.DeallocateAlign.signature568 frame.inst WNear.Binary.DeallocateAlign.function568 [.i32 a, .i32 b])) (18 * op + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.DeallocateAlign.function568, WNear.Binary.DeallocateAlign.signature568,
      leaf, saved, atCode, List.map_cons, List.map_nil, ValType.default, List.append_nil, List.length_cons, List.length_nil, Nat.reduceAdd, arrays] using body
  have result := callRule (hc.mono (by dsimp [op]; omega)) next
  simpa only [Nat.add_assoc, Nat.reduceAdd,
    show cfg.regularOpCost + (10 * op + (18 * op + rest)) = 29 * cfg.regularOpCost + rest by dsimp [op]; omega] using result


def bodyAfter570 (s : Store NearState) (op : Nat) := after568 (paid s op 2) op

theorem bodyAfter570_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (31 * op + rest)) : (bodyAfter570 s op).host.gas.Credits rest := by
  exact after568_credits (paid s op 2) op rest (paid_credits s op 2 _ (hc.mono (by omega)))

/-- f570 actually passes the fixed alignment four to f568. -/
theorem wp_body570 (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (a : UInt32) (mi : ModuleInst) (address : Nat) (post : Post)
    (ha : frame.locals[0]? = some (.i32 a))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.funcAddrs[568]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.DeallocateAlign.signature568 frame.inst WNear.Binary.DeallocateAlign.function568))
    (hadd : Numeric.irelop32 .lt_u (a + 4) a = false)
    (hsub : Numeric.irelop32 .gt_u (a + 4 + 4294967295) (a + 4) = false)
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (31 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (bodyAfter570 s cfg.regularOpCost) limits
      (base ++ [Value.i32 (quotient a 4)]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 23) (.next (atCode s limits base.toArray frame callers (WNear.Binary.DeallocateAlign.body570 ++ code)))
      (31 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have hm2 : (paid s op 2).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hf2 : (paid s op 2).funcs[address]? = some (.wasm WNear.Binary.DeallocateAlign.signature568 frame.inst WNear.Binary.DeallocateAlign.function568) := by
    simpa only [paid, chargedStore] using hf
  have call := wp_call568 cfg fuel rest (paid s op 2) limits base frame callers code a 4 mi address post hm2 hi hf2 hadd hsub (by decide) hd
    (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) hnext
  have array : (base ++ [Value.i32 a, .i32 4]).toArray = (base.toArray.push (.i32 a)).push (.i32 4) := by
    apply Array.toList_inj.mp
    simp
  have callNext : WP cfg (fuel + 21) (.next (atCode (paid s op 2) limits ((base.toArray.push (.i32 a)).push (.i32 4)) frame callers (.call 568 :: code))) (29 * op + rest) post := by
    simpa only [array, op] using call
  have constant := wp_i32_const cfg (fuel + 21) (29 * op + rest) (paid s op 1) limits (base.toArray.push (.i32 a)) frame callers (.call 568 :: code) 4 post
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) callNext
  rw [show cfg.regularOpCost + (29 * op + rest) = 30 * op + rest by dsimp [op]; omega] at constant
  have get := wp_local_get cfg (fuel + 22) (30 * op + rest) s limits base.toArray frame callers (.i32_const 4 :: .call 568 :: code) 0 (.i32 a) post ha
    (hc.mono (by dsimp [op]; omega)) constant
  simpa only [WNear.Binary.DeallocateAlign.body570, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd,
    show cfg.regularOpCost + (30 * op + rest) = 31 * cfg.regularOpCost + rest by dsimp [op]; omega] using get

def entered570 (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (9 * op)
def after570 (s : Store NearState) (op : Nat) := bodyAfter570 (entered570 s op) op

theorem entered570_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (10 * op + rest)) : (entered570 s op).host.gas.Credits rest := by
  have c := StorePair.charged_credits s op (9 * op + rest) (hc.mono (by omega))
  exact StorePair.charged_credits (chargedStore s op) (9 * op) rest c

theorem after570_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (41 * op + rest)) : (after570 s op).host.gas.Credits rest := by
  exact bodyAfter570_credits (entered570 s op) op rest (entered570_credits s op (31 * op + rest) (hc.mono (by omega)))

/-- Full deployed f570 local call, with real f568 execution and a free normal
frame exit. Arbitrary caller operands, labels and callers are preserved. -/
theorem wp_call570 (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (a : UInt32) (mi : ModuleInst) (address568 address570 : Nat) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi568 : mi.funcAddrs[568]? = some address568)
    (hf568 : s.funcs[address568]? = some (.wasm WNear.Binary.DeallocateAlign.signature568 frame.inst WNear.Binary.DeallocateAlign.function568))
    (hi570 : mi.funcAddrs[570]? = some address570)
    (hf570 : s.funcs[address570]? = some (.wasm WNear.Binary.DeallocateAlign.signature570 frame.inst WNear.Binary.DeallocateAlign.function570))
    (hadd : Numeric.irelop32 .lt_u (a + 4) a = false)
    (hsub : Numeric.irelop32 .gt_u (a + 4 + 4294967295) (a + 4) = false)
    (hd : callers.length + 2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (41 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after570 s cfg.regularOpCost) limits
      (base ++ [Value.i32 (quotient a 4)]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 25) (.next (atCode s limits (base ++ [Value.i32 a]).toArray frame callers (.call 570 :: code)))
      (41 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := entered570 s op
  let leaf : CallFrame := {locals := #[Value.i32 a], inst := frame.inst, arity := 1, height := base.length, labels := [], code := []}
  let saved := {frame with code}
  have ca := entered570_credits s op (31 * op + rest) (hc.mono (by dsimp [op]; omega))
  have cf := after570_credits s op rest hc
  have leaving := wp_leave_wasm cfg fuel rest (after570 s op) limits base [.i32 (quotient a 4)] leaf saved callers post rfl rfl rfl cf
  have leaveNext : WP cfg fuel (.next (atCode (after570 s op) limits (base ++ [Value.i32 (quotient a 4)]).toArray saved callers saved.code)) rest post := by
    simpa only [saved, atCode, op] using hnext
  have left := leaving leaveNext
  have hm' : active.modules[leaf.inst]? = some mi := by simpa only [active, entered570, chargedStore, leaf] using hm
  have hf' : active.funcs[address568]? = some (.wasm WNear.Binary.DeallocateAlign.signature568 leaf.inst WNear.Binary.DeallocateAlign.function568) := by
    simpa only [active, entered570, chargedStore, leaf] using hf568
  have bodyNext : WP cfg (fuel + 1) (.next (atCode (bodyAfter570 active op) limits (base ++ [Value.i32 (quotient a 4)]).toArray leaf (saved :: callers) [])) rest post := by
    simpa only [after570, active] using left
  have body := wp_body570 cfg (fuel + 1) rest active limits base leaf (saved :: callers) [] a mi address568 post rfl hm' hi568 hf' hadd hsub
    (by simpa only [List.length_cons] using hd) ca bodyNext
  have callRule := wp_call_wasm cfg ((fuel + 1) + 23) (31 * op + rest) s limits base [.i32 a] frame callers code 570 address570 mi
    WNear.Binary.DeallocateAlign.signature570 frame.inst WNear.Binary.DeallocateAlign.function570 post hm hi570 hf570 rfl (by omega)
  have ha : activationGas op (wasmLocals WNear.Binary.DeallocateAlign.function570 [.i32 a]) = 9 * op := by
    simp [activationGas, wasmLocals, WNear.Binary.DeallocateAlign.function570]
  rw [ha] at callRule
  have next : WP cfg ((fuel + 1) + 23) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.DeallocateAlign.signature570 frame.inst WNear.Binary.DeallocateAlign.function570 [.i32 a])) (31 * op + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.DeallocateAlign.function570, WNear.Binary.DeallocateAlign.signature570,
      leaf, saved, atCode, List.map_nil, Array.append_empty, List.append_nil, List.length_cons, List.length_nil, Nat.reduceAdd] using body
  have result := callRule (hc.mono (by dsimp [op]; omega)) next
  simpa only [Nat.add_assoc, Nat.reduceAdd,
    show cfg.regularOpCost + (9 * op + (31 * op + rest)) = 41 * cfg.regularOpCost + rest by dsimp [op]; omega] using result
end WNear.Proofs.DeallocateAlign
