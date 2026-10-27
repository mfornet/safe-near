import Proofs.AllocateUnitsCall
import Proofs.ValueReturnLazyLookup

/-! Actual accepted minimum-block-size guard574 and its explicit return. -/
namespace WNear.Proofs.AllocateUnits
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
open WNear.Binary.AllocateUnits
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode

theorem minimum_guard (value : UInt32) (h : 8 ≤ value.toNat) :
    Numeric.irelop32 .gt_u (value + 4294967288) value = false := by
  change decide (value < value + 4294967288) = false
  simp only [decide_eq_false_iff_not,UInt32.lt_iff_toNat_lt,UInt32.toNat_add,UInt32.toNat_ofNat]
  have hx := UInt32.toNat_lt value
  omega

def minimumAfter (s : Store NearState) (op : Nat) := paid (entered9 s op) op 7

theorem minimumAfter_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (17 * op + rest)) : (minimumAfter s op).host.gas.Credits rest :=
  paid_credits (entered9 s op) op 7 rest (entered9_credits s op _ (hc.mono (by omega)))

theorem wp_minimum_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame caller : CallFrame) (callers : List CallFrame)
    (value : UInt32) (post : Post)
    (hv : frame.locals[0]? = some (.i32 value)) (hb : 8 ≤ value.toNat)
    (ha : frame.arity = 0) (hh : frame.height = base.length)
    (hc : s.host.gas.Credits (7 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits base.toArray caller callers caller.code)) rest post) :
    WP cfg (fuel + 8) (.next (atCode s limits base.toArray frame (caller :: callers) minimumBody))
      (7 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let bf := emptyBlockFrame frame base.toArray.size minimumPanic
  have retNext : WP cfg fuel (.next (atCode (chargedStore (paid s op 6) cfg.regularOpCost) limits
      (base ++ []).toArray caller callers caller.code)) rest post := by
    simpa only [paid,op,List.append_nil] using hnext
  have hArity : ([] : List Value).length = bf.arity := ha.symm
  have hHeight : bf.height = base.length := hh
  have hRetCredits : (paid s op 6).host.gas.Credits (op + rest) :=
    paid_credits s op 6 (op + rest) (hc.mono (by dsimp [op]; omega))
  have ret := ValueReturnLazyLookup.wp_return_wasm cfg fuel rest (paid s op 6) limits base []
    bf caller callers [] post hArity hHeight hRetCredits retNext
  have retCast : WP cfg (fuel + 1) (.next (atCode (paid s op 6) limits base.toArray bf (caller :: callers) [.return]))
      (op + rest) post := by simpa only [List.append_nil,op] using ret
  have branch := wp_br_if_zero cfg (fuel + 1) (op + rest) (paid s op 5) limits base.toArray bf (caller :: callers) [.return] 0 post
    (paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))) retCast
  have branchCast : WP cfg (fuel + 2) (.next (atCode (paid s op 5) limits
      (base.toArray.push (.i32 (Numeric.bool (Numeric.irelop32 .gt_u (value + 4294967288) value)))) bf
      (caller :: callers) [.br_if 0,.return])) (op + (op + rest)) post := by
    simpa only [minimum_guard value hb,Numeric.bool,Bool.false_eq_true,ite_false,op,Nat.add_assoc,Nat.reduceAdd] using branch
  have rel := wp_i32_relop cfg (fuel + 2) (op + (op + rest)) (paid s op 4) limits base.toArray bf (caller :: callers)
    [.br_if 0,.return] .gt_u (value + 4294967288) value post
    (paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))) branchCast
  have get := wp_local_get cfg (fuel + 3) (op + (op + (op + rest))) (paid s op 3) limits
    (base.toArray.push (.i32 (value + 4294967288))) bf (caller :: callers) [.i32_relop .gt_u,.br_if 0,.return]
    0 (.i32 value) post hv (paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))) rel
  have add := wp_i32_add cfg (fuel + 4) (op + (op + (op + (op + rest)))) (paid s op 2) limits base.toArray bf (caller :: callers)
    [.local_get 0,.i32_relop .gt_u,.br_if 0,.return] value 4294967288 post
    (paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))) get
  have con := wp_i32_const cfg (fuel + 5) (op + (op + (op + (op + (op + rest))))) (paid s op 1) limits
    (base.toArray.push (.i32 value)) bf (caller :: callers) [.i32_binop .add,.local_get 0,.i32_relop .gt_u,.br_if 0,.return]
    4294967288 post (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) add
  have start := wp_local_get cfg (fuel + 6) (op + (op + (op + (op + (op + (op + rest)))))) s limits base.toArray bf (caller :: callers)
    [.i32_const 4294967288,.i32_binop .add,.local_get 0,.i32_relop .gt_u,.br_if 0,.return]
    0 (.i32 value) post hv (hc.mono (by dsimp [op]; omega)) con
  have inside : WP cfg (fuel + 7) (.next (atCode s limits base.toArray bf (caller :: callers) minimumGuard))
      (7 * cfg.regularOpCost + rest) post := by
    simpa only [minimumGuard,show cfg.regularOpCost + (op + (op + (op + (op + (op + (op + rest)))))) = 7 * cfg.regularOpCost + rest by dsimp [op]; omega] using start
  have block := wp_block_empty cfg (fuel + 7) (7 * cfg.regularOpCost + rest) s limits base.toArray frame (caller :: callers)
    minimumGuard minimumPanic post hc inside
  exact block

/-- The native bound8≤size selects the actual explicit return rather than853. -/
theorem wp_minimum_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (value : UInt32) (mi : ModuleInst) (address : Nat) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.funcAddrs[574]? = some address)
    (hf : s.funcs[address]? = some (.wasm minimumSignature frame.inst minimumFunction))
    (hb : 8 ≤ value.toNat) (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (17 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (minimumAfter s cfg.regularOpCost) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 9) (.next (atCode s limits (base ++ [Value.i32 value]).toArray frame callers (.call 574 :: code)))
      (17 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := entered9 s op
  let leaf : CallFrame := {locals := #[Value.i32 value],inst := frame.inst,arity := 0,height := base.length,labels := [],code := []}
  let saved := {frame with code}
  have ca := entered9_credits s op (7 * op + rest) (hc.mono (by dsimp [op]; omega))
  have hn : WP cfg fuel (.next (atCode (paid active op 7) limits base.toArray saved callers saved.code)) rest post := by
    simpa only [minimumAfter,active,saved,atCode,op] using hnext
  have body := wp_minimum_body cfg fuel rest active limits base leaf saved callers value post rfl hb rfl rfl ca hn
  have rule := wp_call_wasm cfg (fuel + 8) (7 * op + rest) s limits base [.i32 value]
    frame callers code 574 address mi minimumSignature frame.inst minimumFunction post hm hi hf rfl hd
  have ha : activationGas op (wasmLocals minimumFunction [.i32 value]) = 9 * op := by
    simp [activationGas,wasmLocals,minimumFunction]
  rw [ha] at rule
  have next : WP cfg (fuel + 8) (.next (wasmCallee active limits base frame callers code
      minimumSignature frame.inst minimumFunction [.i32 value])) (7 * op + rest) post := by
    simpa only [wasmCallee,wasmLocals,minimumFunction,minimumSignature,leaf,saved,atCode,
      List.map_nil,Array.append_empty,List.length_nil] using body
  have result := rule (hc.mono (by dsimp [op]; omega)) next
  simpa only [show fuel + 8 + 1 = fuel + 9 by omega,
    show cfg.regularOpCost + (9 * op + (7 * op + rest)) = 17 * cfg.regularOpCost + rest by dsimp [op]; omega] using result

end WNear.Proofs.AllocateUnits
