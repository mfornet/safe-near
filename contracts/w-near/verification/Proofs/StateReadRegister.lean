import Binary.StateRead
import Proofs.StorePairCallerState
import NearVM.MeteredRegisterFrames

/-! Actual SDK vtable forwarders f241 and f240, through their real host calls. -/
namespace WNear.Proofs.StateReadRegister
open Wasm Wasm.Near MeteredLogic
open MeteredHosts
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode

def lengthAfter (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) :=
  RegisterCalls.lengthStore cfg (paid s cfg.regularOpCost 1) mi

def readAfter (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) (ptr : UInt64) (bytes : List UInt8) :=
  RegisterCalls.readStore cfg (paid s cfg.regularOpCost 2) mi ptr bytes

def lengthValue (s : Store NearState) (register : UInt64) :=
  ((s.host.registers register.toNat).map (fun xs => UInt64.ofNat xs.length)).getD u64Max

/-- Actual f241 ignores the receiver and forwards its register id to import1. -/
theorem wp_length_body (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (mi : ModuleInst) (address index : Nat) (memory : Memory) (register : UInt64) (post : Post)
    (hl : frame.locals[1]? = some (.i64 register))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.funcAddrs[1]? = some address)
    (hf : s.funcs[address]? = some (.host (metered extra "register_len" registerLenFn).toHostFn))
    (hmi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hc : s.host.gas.Credits (2 * cfg.regularOpCost + s.host.extCosts.cost "base" + rest))
    (hnext : WP cfg fuel (.next (atCode (lengthAfter cfg s mi) limits
      (base ++ [Value.i64 (lengthValue s register)]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 2) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateRead.lengthForwardBody ++ code)))
      (2 * cfg.regularOpCost + s.host.extCosts.cost "base" + rest) post := by
  let op := cfg.regularOpCost
  have hm1 : (paid s op 1).modules[frame.inst]? = some mi := hm
  have hf1 : (paid s op 1).funcs[address]? = some (.host (metered extra "register_len" registerLenFn).toHostFn) := hf
  have hmem1 : (paid s op 1).mems[index]? = some memory := hmem
  have hn : WP cfg fuel (.next (atCode (RegisterCalls.lengthStore cfg (paid s op 1) mi) limits
      (base ++ [Value.i64 (RegisterRead.lengthValue (RegisterCalls.beforeCall cfg (paid s op 1) mi) register)]).toArray frame callers code)) rest post := by
    simpa only [lengthAfter,lengthValue,RegisterRead.lengthValue,RegisterCalls.beforeCall,paid,chargedStore,chargeHost,op] using hnext
  have chost : (paid s op 1).host.gas.Credits (cfg.regularOpCost + ((paid s op 1).host.extCosts.cost "base" + rest)) := by
    simpa only [paid,chargedStore,chargeHost,op] using (paid_credits s op 1 (op + (s.host.extCosts.cost "base" + rest)) (hc.mono (by dsimp [op]; omega)))
  have tail := RegisterCalls.wp_length_call cfg extra fuel rest (paid s op 1) limits base frame callers code 1 address index mi memory register post
    hm1 hi hf1 hmi hmem1 chost hn
  have stackEq : (base ++ [Value.i64 register]).toArray = base.toArray.push (.i64 register) := by
    apply Array.toList_inj.mp; simp
  have tail' : WP cfg (fuel + 1) (.next (atCode (paid s op 1) limits (base.toArray.push (.i64 register)) frame callers (.call 1 :: code)))
      (op + (s.host.extCosts.cost "base" + rest)) post := by
    simpa only [stackEq,paid,chargedStore,chargeHost,op] using tail
  have result := wp_local_get cfg (fuel + 1) (op + (s.host.extCosts.cost "base" + rest)) s limits base.toArray frame callers (.call 1 :: code) 1 (.i64 register) post hl
    (hc.mono (by dsimp [op]; omega)) tail'
  simpa only [WNear.Binary.StateRead.lengthForwardBody,List.cons_append,List.nil_append,
    show cfg.regularOpCost + (op + (s.host.extCosts.cost "base" + rest)) = 2 * cfg.regularOpCost + s.host.extCosts.cost "base" + rest by dsimp [op]; omega] using result

/-- Actual f240 copies the whole register through import0. -/
theorem wp_read_body (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (mi : ModuleInst) (address index : Nat) (memory : Memory) (register ptr : UInt64) (bytes : List UInt8) (post : Post)
    (hl1 : frame.locals[1]? = some (.i64 register)) (hl2 : frame.locals[2]? = some (.i64 ptr))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.funcAddrs[0]? = some address)
    (hf : s.funcs[address]? = some (.host (metered extra "read_register" readRegisterFn).toHostFn))
    (hmi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hr : s.host.registers register.toNat = some bytes) (hb : ptr.toNat + bytes.length ≤ memory.byteSize)
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + RegisterRead.readCost s.host bytes.length + rest))
    (hnext : WP cfg fuel (.next (atCode (readAfter cfg s mi ptr bytes) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateRead.registerForwardBody ++ code)))
      (3 * cfg.regularOpCost + RegisterRead.readCost s.host bytes.length + rest) post := by
  let op := cfg.regularOpCost
  have hm2 : (paid s op 2).modules[frame.inst]? = some mi := hm
  have hf2 : (paid s op 2).funcs[address]? = some (.host (metered extra "read_register" readRegisterFn).toHostFn) := hf
  have hmem2 : (paid s op 2).mems[index]? = some memory := hmem
  have hr2 : (paid s op 2).host.registers register.toNat = some bytes := hr
  have hn : WP cfg fuel (.next (atCode (RegisterCalls.readStore cfg (paid s op 2) mi ptr bytes) limits (base ++ []).toArray frame callers code)) rest post := by
    simpa only [readAfter,op,List.append_nil] using hnext
  have chost : (paid s op 2).host.gas.Credits (cfg.regularOpCost + (RegisterRead.readCost (paid s op 2).host bytes.length + rest)) := by
    simpa only [RegisterRead.readCost,paid,chargedStore,chargeHost,op] using (paid_credits s op 2 (op + (RegisterRead.readCost s.host bytes.length + rest)) (hc.mono (by dsimp [op]; omega)))
  have tail := RegisterCalls.wp_read_call cfg extra fuel rest (paid s op 2) limits base frame callers code 0 address index mi memory register ptr bytes post
    hm2 hi hf2 hmi hmem2 hr2 hb chost hn
  have stackEq : (base ++ [Value.i64 register,.i64 ptr]).toArray = (base.toArray.push (.i64 register)).push (.i64 ptr) := by
    apply Array.toList_inj.mp; simp
  have tail' : WP cfg (fuel + 1) (.next (atCode (paid s op 2) limits ((base.toArray.push (.i64 register)).push (.i64 ptr)) frame callers (.call 0 :: code)))
      (op + (RegisterRead.readCost s.host bytes.length + rest)) post := by
    simpa only [stackEq,RegisterRead.readCost,paid,chargedStore,chargeHost,op] using tail
  have get2 := wp_local_get cfg (fuel + 1) (op + (RegisterRead.readCost s.host bytes.length + rest)) (paid s op 1) limits (base.toArray.push (.i64 register)) frame callers (.call 0 :: code) 2 (.i64 ptr) post hl2
    (paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))) tail'
  have result := wp_local_get cfg (fuel + 2) (op + (op + (RegisterRead.readCost s.host bytes.length + rest))) s limits base.toArray frame callers (.local_get 2 :: .call 0 :: code) 1 (.i64 register) post hl1
    (hc.mono (by dsimp [op]; omega)) get2
  simpa only [WNear.Binary.StateRead.registerForwardBody,List.cons_append,List.nil_append,
    show cfg.regularOpCost + (op + (op + (RegisterRead.readCost s.host bytes.length + rest))) = 3 * cfg.regularOpCost + RegisterRead.readCost s.host bytes.length + rest by dsimp [op]; omega] using result

end WNear.Proofs.StateReadRegister
