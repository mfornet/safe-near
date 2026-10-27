import Proofs.StateDispatchIndirect
import Proofs.StateReadRegisterCall
import Proofs.StateReadStorageCall

/-! Complete actual SDK host-forwarder calls through their deployed vtable types. -/
namespace WNear.Proofs.StateDispatchHosts
open Wasm Wasm.Near MeteredLogic MeteredHosts
attribute [local irreducible] WP atCode

/-- Real type7/table0 register_len dispatch executes f241 and the metered host. -/
theorem wp_length (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (mi : ModuleInst) (hostAddress leafAddress index tableAddress : Nat) (table : TableInst) (element : UInt32)
    (memory : Memory) (receiver : UInt32) (register : UInt64) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.funcAddrs[1]? = some hostAddress)
    (hf : s.funcs[hostAddress]? = some (.host (metered extra "register_len" registerLenFn).toHostFn))
    (hmi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hli : mi.funcAddrs[241]? = some leafAddress)
    (hlf : s.funcs[leafAddress]? = some (.wasm WNear.Binary.StateRead.lengthForwardSignature frame.inst WNear.Binary.StateRead.lengthForwardFunction))
    (hta : mi.tableAddrs[0]? = some tableAddress) (ht : s.tables[tableAddress]? = some table)
    (he : table.elems[element.toNat]? = some (.func leafAddress))
    (hty : mi.types[7]? = some WNear.Binary.StateRead.lengthForwardSignature)
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (13 * cfg.regularOpCost + s.host.extCosts.cost "base" + rest))
    (hnext : WP cfg fuel (.next (atCode (StateReadRegister.lengthCallAfter cfg s mi) limits
      (base ++ [Value.i64 (StateReadRegister.lengthValue s register)]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits ((base ++ [Value.i32 receiver,.i64 register]).toArray.push (.i32 element)) frame callers (.call_indirect 7 0 :: code)))
      (13 * cfg.regularOpCost + s.host.extCosts.cost "base" + rest) post := by
  have direct := StateReadRegister.wp_length_call cfg extra fuel rest s limits base frame callers code mi hostAddress leafAddress index memory receiver register post hm hi hf hmi hmem hli hlf hd hc hnext
  exact StateDispatchIndirect.wp_of_direct cfg (fuel + 3) _ s limits base [.i32 receiver,.i64 register] frame callers code
    241 7 tableAddress leafAddress element table mi WNear.Binary.StateRead.lengthForwardSignature frame.inst WNear.Binary.StateRead.lengthForwardFunction post
    hm hli hta ht he hty hlf rfl hd (by omega) direct

/-- Real type4/table0 read_register dispatch executes f240 and the exact copy. -/
theorem wp_read (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (mi : ModuleInst) (hostAddress leafAddress index tableAddress : Nat) (table : TableInst) (element : UInt32)
    (memory : Memory) (receiver : UInt32) (register ptr : UInt64) (bytes : List UInt8) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.funcAddrs[0]? = some hostAddress)
    (hf : s.funcs[hostAddress]? = some (.host (metered extra "read_register" readRegisterFn).toHostFn))
    (hmi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hli : mi.funcAddrs[240]? = some leafAddress)
    (hlf : s.funcs[leafAddress]? = some (.wasm WNear.Binary.StateRead.registerForwardSignature frame.inst WNear.Binary.StateRead.registerForwardFunction))
    (hta : mi.tableAddrs[0]? = some tableAddress) (ht : s.tables[tableAddress]? = some table)
    (he : table.elems[element.toNat]? = some (.func leafAddress))
    (hty : mi.types[4]? = some WNear.Binary.StateRead.registerForwardSignature)
    (hr : s.host.registers register.toNat = some bytes) (hb : ptr.toNat + bytes.length ≤ memory.byteSize)
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (15 * cfg.regularOpCost + RegisterRead.readCost s.host bytes.length + rest))
    (hnext : WP cfg fuel (.next (atCode (StateReadRegister.readCallAfter cfg s mi ptr bytes) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits ((base ++ [Value.i32 receiver,.i64 register,.i64 ptr]).toArray.push (.i32 element)) frame callers (.call_indirect 4 0 :: code)))
      (15 * cfg.regularOpCost + RegisterRead.readCost s.host bytes.length + rest) post := by
  have direct := StateReadRegister.wp_read_call cfg extra fuel rest s limits base frame callers code mi hostAddress leafAddress index memory receiver register ptr bytes post hm hi hf hmi hmem hli hlf hr hb hd hc hnext
  exact StateDispatchIndirect.wp_of_direct cfg (fuel + 4) _ s limits base [.i32 receiver,.i64 register,.i64 ptr] frame callers code
    240 4 tableAddress leafAddress element table mi WNear.Binary.StateRead.registerForwardSignature frame.inst WNear.Binary.StateRead.registerForwardFunction post
    hm hli hta ht he hty hlf rfl hd (by omega) direct

/-- Real type6/table0 canonical storage-read hit, through f284 and its host. -/
theorem wp_storage (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (mi : ModuleInst) (hostAddress leafAddress index tableAddress : Nat) (table : TableInst) (element : UInt32) (memory : Memory)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (storage : List (List UInt8 × List UInt8))
    (receiver : UInt32) (keyLen keyPtr register : UInt64) (key value : List UInt8) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.funcAddrs[43]? = some hostAddress)
    (hf : s.funcs[hostAddress]? = some (.host (metered extra "storage_read" storageReadFn).toHostFn))
    (hmi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hli : mi.funcAddrs[284]? = some leafAddress)
    (hlf : s.funcs[leafAddress]? = some (.wasm WNear.Binary.StateRead.storageForwardSignature frame.inst WNear.Binary.StateRead.storageForwardFunction))
    (hta : mi.tableAddrs[0]? = some tableAddress) (ht : s.tables[tableAddress]? = some table)
    (he : table.elems[element.toNat]? = some (.func leafAddress))
    (hty : mi.types[6]? = some WNear.Binary.StateRead.storageForwardSignature)
    (hr : StorageReadCalls.Ready ⟨memory,s.host⟩ ctx raw storage keyLen keyPtr register key value)
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (17 * cfg.regularOpCost + StorageReadCalls.cost ⟨memory,s.host⟩ ctx.trie keyLen keyPtr register key value + rest))
    (hnext : WP cfg fuel (.next (atCode (StateReadStorage.callAfter cfg s mi ctx.trie keyLen keyPtr register key value)
      limits (base ++ [Value.i64 1]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 6) (.next (atCode s limits ((base ++ [Value.i32 receiver,.i64 keyLen,.i64 keyPtr,.i64 register]).toArray.push (.i32 element)) frame callers (.call_indirect 6 0 :: code)))
      (17 * cfg.regularOpCost + StorageReadCalls.cost ⟨memory,s.host⟩ ctx.trie keyLen keyPtr register key value + rest) post := by
  have direct := StateReadStorage.wp_call cfg extra fuel rest s limits base frame callers code mi hostAddress leafAddress index memory ctx raw storage receiver keyLen keyPtr register key value post hm hi hf hmi hmem hli hlf hr hd hc hnext
  exact StateDispatchIndirect.wp_of_direct cfg (fuel + 5) _ s limits base [.i32 receiver,.i64 keyLen,.i64 keyPtr,.i64 register] frame callers code
    284 6 tableAddress leafAddress element table mi WNear.Binary.StateRead.storageForwardSignature frame.inst WNear.Binary.StateRead.storageForwardFunction post
    hm hli hta ht he hty hlf rfl hd (by omega) direct
end WNear.Proofs.StateDispatchHosts
