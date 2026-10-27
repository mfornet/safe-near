import Proofs.InterfaceInitialize
import Proofs.InterfaceStack
import Binary.InterfaceLazy

/-! Actual lazy f467 initializer invocation, after its shadow-stack reserve. -/
namespace WNear.Proofs.InterfaceLazyPrefix
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384

def after (s : Store NearState) (op index : Nat) (scratch : UInt32) (memory : Memory) :=
  InterfaceInitialize.after (paid s op 2) op index scratch.toNat memory

/-- Both actual local arguments and the real table call. No initializer
execution hypothesis is supplied. -/
theorem wp_initialize (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch location : UInt32) (mi : ModuleInst)
    (tableAddress address index : Nat) (table : TableInst) (memory : Memory) (post : Post)
    (hs : frame.locals[2]? = some (.i32 scratch)) (hl : frame.locals[1]? = some (.i32 location))
    (hm : s.modules[frame.inst]? = some mi) (hta : mi.tableAddrs[0]? = some tableAddress)
    (ht : s.tables[tableAddress]? = some table) (he : table.elems[location.toNat]? = some (.func address))
    (hty : mi.types[0]? = some WNear.Binary.InterfaceInitialize.signature)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.InterfaceInitialize.signature frame.inst WNear.Binary.InterfaceInitialize.function))
    (hi : mi.memAddrs[0]? = some index) (hmem : s.mems[index]? = some memory)
    (hb : scratch.toNat + 8 ≤ memory.byteSize) (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (15 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost index scratch memory)
      limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 7) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.InterfaceLazy.initCall ++ code))) (15 * cfg.regularOpCost + rest) post := by
  let prepared := paid s cfg.regularOpCost 2
  have hm' : prepared.modules[frame.inst]? = some mi := by simpa only [prepared, paid, chargedStore] using hm
  have ht' : prepared.tables[tableAddress]? = some table := by simpa only [prepared, paid, chargedStore] using ht
  have hf' : prepared.funcs[address]? = some (.wasm WNear.Binary.InterfaceInitialize.signature frame.inst WNear.Binary.InterfaceInitialize.function) := by
    simpa only [prepared, paid, chargedStore] using hf
  have hmemb : prepared.mems[index]? = some memory := by simpa only [prepared, paid, chargedStore] using hmem
  have cp : prepared.host.gas.Credits (13 * cfg.regularOpCost + rest) := paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  have indirectNext : WP cfg fuel (.next (atCode (InterfaceInitialize.after prepared cfg.regularOpCost index scratch.toNat memory)
      limits base.toArray frame callers code)) rest post := hnext
  have rule := InterfaceInitialize.wp_indirect cfg fuel rest prepared limits base frame callers code scratch mi
    tableAddress address index location table memory post hm' hta ht' he hty hf' hi hmemb hb hd cp indirectNext
  have arrayShape : ((base ++ [Value.i32 scratch]).toArray.push (.i32 location)) =
      (base.toArray.push (.i32 scratch)).push (.i32 location) := by
    apply Array.toList_inj.mp; simp
  rw [arrayShape] at rule
  rw [show 15 * cfg.regularOpCost + rest = cfg.regularOpCost + (14 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 6) _ s limits base.toArray frame callers _ 2 (.i32 scratch) post hs (hc.mono (by omega))
  rw [show 14 * cfg.regularOpCost + rest = cfg.regularOpCost + (13 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 5) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 1 (.i32 location) post hl
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  · exact rule

theorem after_credits (s : Store NearState) (op index rest : Nat) (scratch : UInt32) (memory : Memory)
    (hc : s.host.gas.Credits (15 * op + rest)) : (after s op index scratch memory).host.gas.Credits rest := by
  have hp : (paid s op 2).host.gas.Credits (13 * op + rest) := paid_credits s op 2 _ (hc.mono (by omega))
  exact InterfaceInitialize.after_credits (paid s op 2) op index scratch.toNat rest memory hp

theorem after_memory (s : Store NearState) (op index : Nat) (scratch : UInt32) (memory : Memory)
    (hm : s.mems[index]? = some memory) :
    (after s op index scratch memory).mems[index]? = some (writeI64 memory scratch.toNat 0) := by
  have hp : (paid s op 2).mems[index]? = some memory := by simpa only [paid, chargedStore] using hm
  exact InterfaceInitialize.after_memory (paid s op 2) op index scratch.toNat memory hp

theorem after_resources (s : Store NearState) (op index : Nat) (scratch : UInt32) (memory : Memory) :
    {after s op index scratch memory with mems := s.mems, host := s.host} = s := by
  simp only [after, InterfaceInitialize.after, InterfaceInitialize.bodyAfter, InterfaceInitialize.entry,
    paid, chargedStore, storeI64]

end WNear.Proofs.InterfaceLazyPrefix
