import Binary.AllocateGrowthHelpers
import Proofs.DeallocateAlignNative

/-! Complete actual checked page-ceiling helper f569. -/
namespace WNear.Proofs.AllocateGrowth
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
open DeallocateAlign (quotient wp_call568 after568 after568_credits)
attribute [local irreducible] WP atCode
set_option maxRecDepth 16384
theorem checks569 (a : UInt32) (h : a.toNat+65536<2^32) :
    Numeric.irelop32 .lt_u (a+65536) a=false ∧
    Numeric.irelop32 .gt_u (a+65536+4294967295) (a+65536)=false := by
  have checks := DeallocateAlign.checks a 65536 (by decide) (by simpa using h)
  exact ⟨checks.1,checks.2.1⟩

theorem quotient569_toNat (a : UInt32) (h : a.toNat+65536<2^32) :
    (quotient a 65536).toNat=(a.toNat+65535)/65536 := by
  have q := DeallocateAlign.quotient_toNat a 65536 (by decide) (by simpa using h)
  simpa using q

def bodyAfter569 (s : Store NearState) (op : Nat) := after568 (paid s op 2) op

theorem bodyAfter569_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (31 * op + rest)) : (bodyAfter569 s op).host.gas.Credits rest := by
  exact after568_credits (paid s op 2) op rest (paid_credits s op 2 _ (hc.mono (by omega)))

/-- f569 actually passes the fixed alignment four to f568. -/
theorem wp_body569 (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (a : UInt32) (mi : ModuleInst) (address : Nat) (post : Post)
    (ha : frame.locals[0]? = some (.i32 a))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.funcAddrs[568]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.DeallocateAlign.signature568 frame.inst WNear.Binary.DeallocateAlign.function568))
    (hadd : Numeric.irelop32 .lt_u (a + 65536) a = false)
    (hsub : Numeric.irelop32 .gt_u (a + 65536 + 4294967295) (a + 65536) = false)
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (31 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (bodyAfter569 s cfg.regularOpCost) limits
      (base ++ [Value.i32 (quotient a 65536)]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 23) (.next (atCode s limits base.toArray frame callers (WNear.Binary.AllocateGrowth.body569 ++ code)))
      (31 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have hm2 : (paid s op 2).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hm
  have hf2 : (paid s op 2).funcs[address]? = some (.wasm WNear.Binary.DeallocateAlign.signature568 frame.inst WNear.Binary.DeallocateAlign.function568) := by
    simpa only [paid, chargedStore] using hf
  have call := wp_call568 cfg fuel rest (paid s op 2) limits base frame callers code a 65536 mi address post hm2 hi hf2 hadd hsub (by decide) hd
    (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) hnext
  have array : (base ++ [Value.i32 a, .i32 65536]).toArray = (base.toArray.push (.i32 a)).push (.i32 65536) := by
    apply Array.toList_inj.mp
    simp
  have callNext : WP cfg (fuel + 21) (.next (atCode (paid s op 2) limits ((base.toArray.push (.i32 a)).push (.i32 65536)) frame callers (.call 568 :: code))) (29 * op + rest) post := by
    simpa only [array, op] using call
  have constant := wp_i32_const cfg (fuel + 21) (29 * op + rest) (paid s op 1) limits (base.toArray.push (.i32 a)) frame callers (.call 568 :: code) 65536 post
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) callNext
  rw [show cfg.regularOpCost + (29 * op + rest) = 30 * op + rest by dsimp [op]; omega] at constant
  have get := wp_local_get cfg (fuel + 22) (30 * op + rest) s limits base.toArray frame callers (.i32_const 65536 :: .call 568 :: code) 0 (.i32 a) post ha
    (hc.mono (by dsimp [op]; omega)) constant
  simpa only [WNear.Binary.AllocateGrowth.body569, List.cons_append, List.nil_append, Nat.add_assoc, Nat.reduceAdd,
    show cfg.regularOpCost + (30 * op + rest) = 31 * cfg.regularOpCost + rest by dsimp [op]; omega] using get

def entered569 (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (9 * op)
def after569 (s : Store NearState) (op : Nat) := bodyAfter569 (entered569 s op) op

theorem entered569_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (10 * op + rest)) : (entered569 s op).host.gas.Credits rest := by
  have c := StorePair.charged_credits s op (9 * op + rest) (hc.mono (by omega))
  exact StorePair.charged_credits (chargedStore s op) (9 * op) rest c

theorem after569_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (41 * op + rest)) : (after569 s op).host.gas.Credits rest := by
  exact bodyAfter569_credits (entered569 s op) op rest (entered569_credits s op (31 * op + rest) (hc.mono (by omega)))

/-- Full deployed f569 local call, with real f568 execution and a free normal
frame exit. Arbitrary caller operands, labels and callers are preserved. -/
theorem wp_call569 (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (a : UInt32) (mi : ModuleInst) (address568 address569 : Nat) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi568 : mi.funcAddrs[568]? = some address568)
    (hf568 : s.funcs[address568]? = some (.wasm WNear.Binary.DeallocateAlign.signature568 frame.inst WNear.Binary.DeallocateAlign.function568))
    (hi569 : mi.funcAddrs[569]? = some address569)
    (hf569 : s.funcs[address569]? = some (.wasm WNear.Binary.AllocateGrowth.signature569 frame.inst WNear.Binary.AllocateGrowth.function569))
    (hadd : Numeric.irelop32 .lt_u (a + 65536) a = false)
    (hsub : Numeric.irelop32 .gt_u (a + 65536 + 4294967295) (a + 65536) = false)
    (hd : callers.length + 2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (41 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after569 s cfg.regularOpCost) limits
      (base ++ [Value.i32 (quotient a 65536)]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 25) (.next (atCode s limits (base ++ [Value.i32 a]).toArray frame callers (.call 569 :: code)))
      (41 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := entered569 s op
  let leaf : CallFrame := {locals := #[Value.i32 a], inst := frame.inst, arity := 1, height := base.length, labels := [], code := []}
  let saved := {frame with code}
  have ca := entered569_credits s op (31 * op + rest) (hc.mono (by dsimp [op]; omega))
  have cf := after569_credits s op rest hc
  have leaving := wp_leave_wasm cfg fuel rest (after569 s op) limits base [.i32 (quotient a 65536)] leaf saved callers post rfl rfl rfl cf
  have leaveNext : WP cfg fuel (.next (atCode (after569 s op) limits (base ++ [Value.i32 (quotient a 65536)]).toArray saved callers saved.code)) rest post := by
    simpa only [saved, atCode, op] using hnext
  have left := leaving leaveNext
  have hm' : active.modules[leaf.inst]? = some mi := by simpa only [active, entered569, chargedStore, leaf] using hm
  have hf' : active.funcs[address568]? = some (.wasm WNear.Binary.DeallocateAlign.signature568 leaf.inst WNear.Binary.DeallocateAlign.function568) := by
    simpa only [active, entered569, chargedStore, leaf] using hf568
  have bodyNext : WP cfg (fuel + 1) (.next (atCode (bodyAfter569 active op) limits (base ++ [Value.i32 (quotient a 65536)]).toArray leaf (saved :: callers) [])) rest post := by
    simpa only [after569, active] using left
  have body := wp_body569 cfg (fuel + 1) rest active limits base leaf (saved :: callers) [] a mi address568 post rfl hm' hi568 hf' hadd hsub
    (by simpa only [List.length_cons] using hd) ca bodyNext
  have callRule := wp_call_wasm cfg ((fuel + 1) + 23) (31 * op + rest) s limits base [.i32 a] frame callers code 569 address569 mi
    WNear.Binary.AllocateGrowth.signature569 frame.inst WNear.Binary.AllocateGrowth.function569 post hm hi569 hf569 rfl (by omega)
  have ha : activationGas op (wasmLocals WNear.Binary.AllocateGrowth.function569 [.i32 a]) = 9 * op := by
    simp [activationGas, wasmLocals, WNear.Binary.AllocateGrowth.function569]
  rw [ha] at callRule
  have next : WP cfg ((fuel + 1) + 23) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.AllocateGrowth.signature569 frame.inst WNear.Binary.AllocateGrowth.function569 [.i32 a])) (31 * op + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.AllocateGrowth.function569, WNear.Binary.AllocateGrowth.signature569,
      leaf, saved, atCode, List.map_nil, Array.append_empty, List.append_nil, List.length_cons, List.length_nil, Nat.reduceAdd] using body
  have result := callRule (hc.mono (by dsimp [op]; omega)) next
  simpa only [Nat.add_assoc, Nat.reduceAdd,
    show cfg.regularOpCost + (9 * op + (31 * op + rest)) = 41 * cfg.regularOpCost + rest by dsimp [op]; omega] using result
end WNear.Proofs.AllocateGrowth
