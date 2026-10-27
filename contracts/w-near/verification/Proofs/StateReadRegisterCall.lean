import Proofs.StateReadRegister
import NearVM.MeteredWasmCall

/-! Complete typed register-forwarder calls, with their actual activation charges. -/
namespace WNear.Proofs.StateReadRegister
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode
set_option maxRecDepth 16384

def enteredLength (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (10 * op)
def enteredRead (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (11 * op)
def lengthCallAfter (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) :=
  lengthAfter cfg (enteredLength s cfg.regularOpCost) mi
def readCallAfter (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) (ptr : UInt64) (bytes : List UInt8) :=
  readAfter cfg (enteredRead s cfg.regularOpCost) mi ptr bytes

theorem lengthAfter_credits (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) (rest : Nat)
    (hc : s.host.gas.Credits (2 * cfg.regularOpCost + s.host.extCosts.cost "base" + rest)) :
    (lengthAfter cfg s mi).host.gas.Credits rest := by
  have c : (paid s cfg.regularOpCost 1).host.gas.Credits (cfg.regularOpCost + ((paid s cfg.regularOpCost 1).host.extCosts.cost "base" + rest)) := by
    simpa only [paid,chargedStore,chargeHost] using (paid_credits s cfg.regularOpCost 1 (cfg.regularOpCost + (s.host.extCosts.cost "base" + rest)) (hc.mono (by omega)))
  exact (RegisterCalls.lengthStore_credits cfg (paid s cfg.regularOpCost 1) mi rest c).2.2

theorem readAfter_credits (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) (ptr : UInt64) (bytes : List UInt8) (rest : Nat)
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + RegisterRead.readCost s.host bytes.length + rest)) :
    (readAfter cfg s mi ptr bytes).host.gas.Credits rest := by
  have c : (paid s cfg.regularOpCost 2).host.gas.Credits (cfg.regularOpCost + (RegisterRead.readCost (paid s cfg.regularOpCost 2).host bytes.length + rest)) := by
    simpa only [RegisterRead.readCost,paid,chargedStore,chargeHost] using (paid_credits s cfg.regularOpCost 2 (cfg.regularOpCost + (RegisterRead.readCost s.host bytes.length + rest)) (hc.mono (by omega)))
  exact (RegisterCalls.readStore_credits cfg (paid s cfg.regularOpCost 2) mi ptr bytes rest c).2.2

/-- Actual f241 typed activation, two-instruction body, and normal return. -/
theorem wp_length_call (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (mi : ModuleInst) (hostAddress leafAddress index : Nat) (memory : Memory) (receiver : UInt32) (register : UInt64) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.funcAddrs[1]? = some hostAddress)
    (hf : s.funcs[hostAddress]? = some (.host (metered extra "register_len" registerLenFn).toHostFn))
    (hmi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hli : mi.funcAddrs[241]? = some leafAddress)
    (hlf : s.funcs[leafAddress]? = some (.wasm WNear.Binary.StateRead.lengthForwardSignature frame.inst WNear.Binary.StateRead.lengthForwardFunction))
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (13 * cfg.regularOpCost + s.host.extCosts.cost "base" + rest))
    (hnext : WP cfg fuel (.next (atCode (lengthCallAfter cfg s mi) limits
      (base ++ [Value.i64 (lengthValue s register)]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits (base ++ [Value.i32 receiver,.i64 register]).toArray frame callers (.call 241 :: code)))
      (13 * cfg.regularOpCost + s.host.extCosts.cost "base" + rest) post := by
  let op := cfg.regularOpCost
  let active := enteredLength s op
  let leaf : CallFrame := {
    locals := #[.i32 receiver,.i64 register],inst := frame.inst,arity := 1,height := base.length,labels := [],code := []}
  let saved := {frame with code}
  have c0 := (GasCounter.burn_credits s.host.gas op (10 * op + (2 * op + s.host.extCosts.cost "base" + rest)) (hc.mono (by dsimp [op]; omega))).2.2.2
  have c1 : active.host.gas.Credits (2 * op + s.host.extCosts.cost "base" + rest) :=
    (GasCounter.burn_credits (chargedStore s op).host.gas (10 * op) _ c0).2.2.2
  have cbody : active.host.gas.Credits (2 * cfg.regularOpCost + active.host.extCosts.cost "base" + rest) := by
    simpa only [active,enteredLength,chargedStore,chargeHost,op] using c1
  have cf := lengthAfter_credits cfg active mi rest cbody
  have ln : WP cfg fuel (.next (atCode (lengthCallAfter cfg s mi) limits
      (base ++ [Value.i64 (lengthValue s register)]).toArray saved callers saved.code)) rest post := by
    simpa only [saved,atCode] using hnext
  have left := wp_leave_wasm cfg fuel rest (lengthCallAfter cfg s mi) limits base [.i64 (lengthValue s register)] leaf saved callers post rfl rfl rfl cf ln
  have bn : WP cfg (fuel + 1) (.next (atCode (lengthAfter cfg active mi) limits
      (base ++ [Value.i64 (lengthValue active register)]).toArray leaf (saved :: callers) [])) rest post := by
    simpa only [lengthCallAfter,active,lengthValue,enteredLength,chargedStore,chargeHost] using left
  have body := wp_length_body cfg extra (fuel + 1) rest active limits base leaf (saved :: callers) [] mi hostAddress index memory register post
    rfl hm hi hf hmi hmem cbody bn
  have cr := wp_call_wasm cfg ((fuel + 1) + 2) (2 * op + s.host.extCosts.cost "base" + rest) s limits base [.i32 receiver,.i64 register]
    frame callers code 241 leafAddress mi WNear.Binary.StateRead.lengthForwardSignature frame.inst WNear.Binary.StateRead.lengthForwardFunction post hm hli hlf rfl hd
  have ac : activationGas op (wasmLocals WNear.Binary.StateRead.lengthForwardFunction [.i32 receiver,.i64 register]) = 10 * op := by
    simp [activationGas,wasmLocals,WNear.Binary.StateRead.lengthForwardFunction]
  rw [ac] at cr
  have next : WP cfg ((fuel + 1) + 2) (.next (wasmCallee active limits base frame callers code WNear.Binary.StateRead.lengthForwardSignature frame.inst
      WNear.Binary.StateRead.lengthForwardFunction [.i32 receiver,.i64 register])) (2 * op + s.host.extCosts.cost "base" + rest) post := by
    simpa only [op,active,enteredLength,chargedStore,chargeHost,wasmCallee,wasmLocals,WNear.Binary.StateRead.lengthForwardFunction,
      WNear.Binary.StateRead.lengthForwardSignature,leaf,saved,atCode,List.length_cons,List.length_nil,List.map_cons,List.map_nil,List.append_nil,Array.append_empty] using body
  have result := cr (hc.mono (by dsimp [op]; omega)) next
  simpa only [Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost + (10 * op + (2 * op + (s.host.extCosts.cost "base" + rest))) = 13 * cfg.regularOpCost + (s.host.extCosts.cost "base" + rest) by dsimp [op]; omega] using result

/-- Actual f240 typed activation, whole-register copy, and normal void return. -/
theorem wp_read_call (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (mi : ModuleInst) (hostAddress leafAddress index : Nat) (memory : Memory)
    (receiver : UInt32) (register ptr : UInt64) (bytes : List UInt8) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.funcAddrs[0]? = some hostAddress)
    (hf : s.funcs[hostAddress]? = some (.host (metered extra "read_register" readRegisterFn).toHostFn))
    (hmi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hli : mi.funcAddrs[240]? = some leafAddress)
    (hlf : s.funcs[leafAddress]? = some (.wasm WNear.Binary.StateRead.registerForwardSignature frame.inst WNear.Binary.StateRead.registerForwardFunction))
    (hr : s.host.registers register.toNat = some bytes) (hb : ptr.toNat + bytes.length ≤ memory.byteSize)
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (15 * cfg.regularOpCost + RegisterRead.readCost s.host bytes.length + rest))
    (hnext : WP cfg fuel (.next (atCode (readCallAfter cfg s mi ptr bytes) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits (base ++ [Value.i32 receiver,.i64 register,.i64 ptr]).toArray frame callers (.call 240 :: code)))
      (15 * cfg.regularOpCost + RegisterRead.readCost s.host bytes.length + rest) post := by
  let op := cfg.regularOpCost
  let active := enteredRead s op
  let leaf : CallFrame := {
    locals := #[.i32 receiver,.i64 register,.i64 ptr],inst := frame.inst,arity := 0,height := base.length,labels := [],code := []}
  let saved := {frame with code}
  have c0 := (GasCounter.burn_credits s.host.gas op (11 * op + (3 * op + RegisterRead.readCost s.host bytes.length + rest)) (hc.mono (by dsimp [op]; omega))).2.2.2
  have c1 : active.host.gas.Credits (3 * op + RegisterRead.readCost s.host bytes.length + rest) :=
    (GasCounter.burn_credits (chargedStore s op).host.gas (11 * op) _ c0).2.2.2
  have cbody : active.host.gas.Credits (3 * cfg.regularOpCost + RegisterRead.readCost active.host bytes.length + rest) := by
    simpa only [active,enteredRead,RegisterRead.readCost,chargedStore,chargeHost,op] using c1
  have cf := readAfter_credits cfg active mi ptr bytes rest cbody
  have ln : WP cfg fuel (.next (atCode (readCallAfter cfg s mi ptr bytes) limits (base ++ []).toArray saved callers saved.code)) rest post := by
    simpa only [saved,atCode,List.append_nil] using hnext
  have left := wp_leave_wasm cfg fuel rest (readCallAfter cfg s mi ptr bytes) limits base [] leaf saved callers post rfl rfl rfl cf ln
  have bn : WP cfg (fuel + 1) (.next (atCode (readAfter cfg active mi ptr bytes) limits base.toArray leaf (saved :: callers) [])) rest post := by
    simpa only [readCallAfter,active,List.append_nil] using left
  have body := wp_read_body cfg extra (fuel + 1) rest active limits base leaf (saved :: callers) [] mi hostAddress index memory register ptr bytes post
    rfl rfl hm hi hf hmi hmem hr hb cbody bn
  have cr := wp_call_wasm cfg ((fuel + 1) + 3) (3 * op + RegisterRead.readCost s.host bytes.length + rest) s limits base [.i32 receiver,.i64 register,.i64 ptr]
    frame callers code 240 leafAddress mi WNear.Binary.StateRead.registerForwardSignature frame.inst WNear.Binary.StateRead.registerForwardFunction post hm hli hlf rfl hd
  have ac : activationGas op (wasmLocals WNear.Binary.StateRead.registerForwardFunction [.i32 receiver,.i64 register,.i64 ptr]) = 11 * op := by
    simp [activationGas,wasmLocals,WNear.Binary.StateRead.registerForwardFunction]
  rw [ac] at cr
  have next : WP cfg ((fuel + 1) + 3) (.next (wasmCallee active limits base frame callers code WNear.Binary.StateRead.registerForwardSignature frame.inst
      WNear.Binary.StateRead.registerForwardFunction [.i32 receiver,.i64 register,.i64 ptr])) (3 * op + RegisterRead.readCost s.host bytes.length + rest) post := by
    simpa only [op,active,enteredRead,chargedStore,chargeHost,RegisterRead.readCost,wasmCallee,wasmLocals,WNear.Binary.StateRead.registerForwardFunction,
      WNear.Binary.StateRead.registerForwardSignature,leaf,saved,atCode,List.length_cons,List.length_nil,List.map_cons,List.map_nil,List.append_nil,Array.append_empty] using body
  have result := cr (hc.mono (by dsimp [op]; omega)) next
  simpa only [Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost + (11 * op + (3 * op + (RegisterRead.readCost s.host bytes.length + rest))) = 15 * cfg.regularOpCost + (RegisterRead.readCost s.host bytes.length + rest) by dsimp [op]; omega] using result

end WNear.Proofs.StateReadRegister
