import Proofs.AllocateUnits
import NearVM.MeteredWasmCall
import NearVM.MeteredIndirectCall

/-! Actual typed size-scaling and constant allocation-quantum calls. -/
namespace WNear.Proofs.AllocateUnits
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
open WNear.Binary.AllocateUnits
set_option maxRecDepth 16384
attribute [local irreducible] WP

def entered9 (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (9 * op)
def unitsAfter (s : Store NearState) (op : Nat) := paid (entered9 s op) op 9
def quantumAfter (s : Store NearState) (op : Nat) := paid (entered9 s op) op 1

theorem entered9_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (10 * op + rest)) : (entered9 s op).host.gas.Credits rest := by
  have c := StorePair.charged_credits s op (9 * op + rest) (hc.mono (by omega))
  exact StorePair.charged_credits (chargedStore s op) (9 * op) rest c

theorem unitsAfter_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (19 * op + rest)) : (unitsAfter s op).host.gas.Credits rest :=
  paid_credits (entered9 s op) op 9 rest (entered9_credits s op _ (hc.mono (by omega)))

theorem quantumAfter_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (11 * op + rest)) : (quantumAfter s op).host.gas.Credits rest :=
  paid_credits (entered9 s op) op 1 rest (entered9_credits s op _ (hc.mono (by omega)))

/-- Full actual572 call, including activation and the normal one-value return. -/
theorem wp_units_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (value : UInt32) (mi : ModuleInst) (address : Nat) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.funcAddrs[572]? = some address)
    (hf : s.funcs[address]? = some (.wasm unitsSignature frame.inst unitsFunction))
    (hb : value.toNat < 2^30) (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (19 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (unitsAfter s cfg.regularOpCost) limits
      (base ++ [Value.i32 (value <<< (2 : UInt32))]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 12) (.next (atCode s limits (base ++ [Value.i32 value]).toArray frame callers (.call 572 :: code)))
      (19 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := entered9 s op
  let leaf : CallFrame := {locals := #[Value.i32 value],inst := frame.inst,arity := 1,height := base.length,labels := [],code := []}
  let saved := {frame with code}
  have ca := entered9_credits s op (9 * op + rest) (hc.mono (by dsimp [op]; omega))
  have cf := unitsAfter_credits s op rest hc
  have hn : WP cfg fuel (.next (atCode (unitsAfter s op) limits
      (base ++ [Value.i32 (value <<< (2 : UInt32))]).toArray saved callers saved.code)) rest post := by
    simpa only [saved,atCode,op] using hnext
  have leave := wp_leave_wasm cfg fuel rest (unitsAfter s op) limits base [.i32 (value <<< (2 : UInt32))]
    leaf saved callers post rfl rfl rfl cf hn
  have bn : WP cfg (fuel + 1) (.next (atCode (paid active op 9) limits
      (base.toArray.push (.i32 (value <<< (2 : UInt32)))) leaf (saved :: callers) [])) rest post := by
    have arr : (base ++ [Value.i32 (value <<< (2 : UInt32))]).toArray = base.toArray.push (.i32 (value <<< (2 : UInt32))) := by
      apply Array.toList_inj.mp; simp
    simpa only [unitsAfter,active,arr] using leave
  have body := wp_body cfg (fuel + 1) rest active limits base.toArray leaf (saved :: callers) [] value post rfl hb ca bn
  have rule := wp_call_wasm cfg ((fuel + 1) + 10) (9 * op + rest) s limits base [.i32 value]
    frame callers code 572 address mi unitsSignature frame.inst unitsFunction post hm hi hf rfl hd
  have ha : activationGas op (wasmLocals unitsFunction [.i32 value]) = 9 * op := by
    simp [activationGas,wasmLocals,unitsFunction]
  rw [ha] at rule
  have next : WP cfg ((fuel + 1) + 10) (.next (wasmCallee active limits base frame callers code
      unitsSignature frame.inst unitsFunction [.i32 value])) (9 * op + rest) post := by
    simpa only [wasmCallee,wasmLocals,unitsFunction,unitsSignature,leaf,saved,atCode,
      List.map_nil,Array.append_empty,List.append_nil,List.length_cons,List.length_nil] using body
  have result := rule (hc.mono (by dsimp [op]; omega)) next
  simpa only [show (fuel + 1 + 10) + 1 = fuel + 12 by omega,
    show cfg.regularOpCost + (9 * op + (9 * op + rest)) = 19 * cfg.regularOpCost + rest by dsimp [op]; omega] using result

/-- The actual constant-body578 resumes its caller with16, for arbitrary inputs. -/
theorem wp_quantum_callee (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (inst : Nat) (a b : UInt32) (post : Post)
    (hc : s.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 1) limits
      (base ++ [Value.i32 16]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 2) (.next (wasmCallee s limits base frame callers code
      quantumSignature inst quantumFunction [.i32 a,.i32 b])) (cfg.regularOpCost + rest) post := by
  let leaf : CallFrame := {locals := #[Value.i32 a,.i32 b],inst,arity := 1,height := base.length,labels := [],code := []}
  let saved := {frame with code}
  have cf := paid_credits s cfg.regularOpCost 1 rest (by simpa only [Nat.one_mul] using hc)
  have hn : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 1) limits
      (base ++ [Value.i32 16]).toArray saved callers saved.code)) rest post := by
    simpa only [saved,atCode] using hnext
  have leave := wp_leave_wasm cfg fuel rest (paid s cfg.regularOpCost 1) limits base [.i32 16] leaf saved callers post rfl rfl rfl cf hn
  have left : WP cfg (fuel + 1) (.next (atCode (paid s cfg.regularOpCost 1) limits
      (base.toArray.push (.i32 16)) leaf (saved :: callers) [])) rest post := by
    have arr : (base ++ [Value.i32 16]).toArray = base.toArray.push (.i32 16) := by
      apply Array.toList_inj.mp; simp
    simpa only [arr] using leave
  have result := wp_i32_const cfg (fuel + 1) rest s limits base.toArray leaf (saved :: callers) [] 16 post hc left
  simpa only [wasmCallee,wasmLocals,quantumFunction,quantumSignature,leaf,saved,atCode,
    List.map_nil,Array.append_empty,List.length_cons,List.length_nil] using result

/-- The actual indirect allocation callback578: table and type resolution are
original installed resources, and its returned16 follows from its real body. -/
theorem wp_quantum_indirect (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (a b element : UInt32) (mi : ModuleInst) (tableAddress address inst : Nat) (table : TableInst) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hti : mi.tableAddrs[0]? = some tableAddress)
    (ht : s.tables[tableAddress]? = some table) (he : table.elems[element.toNat]? = some (.func address))
    (hft : mi.types[13]? = some quantumSignature)
    (hf : s.funcs[address]? = some (.wasm quantumSignature inst quantumFunction))
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (11 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (quantumAfter s cfg.regularOpCost) limits
      (base ++ [Value.i32 16]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits ((base ++ [Value.i32 a,.i32 b]).toArray.push (.i32 element)) frame callers
      (.call_indirect 13 0 :: code))) (11 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have ca := entered9_credits s op (op + rest) (hc.mono (by dsimp [op]; omega))
  have body := wp_quantum_callee cfg fuel rest (entered9 s op) limits base frame callers code inst a b post ca hnext
  have rule := wp_call_indirect_wasm cfg (fuel + 2) (op + rest) s limits base [.i32 a,.i32 b]
    frame callers code 13 0 tableAddress address element table mi quantumSignature inst quantumFunction post
    hm hti ht he hft hf rfl hd
  have ha : activationGas op (wasmLocals quantumFunction [.i32 a,.i32 b]) = 9 * op := by
    simp [activationGas,wasmLocals,quantumFunction]
  rw [ha] at rule
  have result := rule (hc.mono (by dsimp [op]; omega)) body
  simpa only [show fuel + 2 + 1 = fuel + 3 by omega,
    show cfg.regularOpCost + (9 * op + (op + rest)) = 11 * cfg.regularOpCost + rest by dsimp [op]; omega] using result

end WNear.Proofs.AllocateUnits
