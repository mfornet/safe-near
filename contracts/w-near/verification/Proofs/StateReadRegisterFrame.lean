import Proofs.StateReadRegisterCall

/-! Actual register forwarder post-memory and installed-code frames. -/
namespace WNear.Proofs.StateReadRegister
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid paid_credits paid_gas)

private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems = s.mems := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

private theorem readStore_memory (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst)
    (index : Nat) (memory : Memory) (ptr : UInt64) (bytes : List UInt8)
    (hi : mi.memAddrs[0]? = some index) (hm : s.mems[index]? = some memory) :
    (RegisterCalls.readStore cfg s mi ptr bytes).mems[index]? = some (memory.writeList ptr.toNat bytes) := by
  have hb := (Array.getElem?_eq_some_iff.mp hm).1
  have hv := (Array.getElem?_eq_some_iff.mp hm).2
  simp only [RegisterCalls.readStore,RegisterCalls.readAfter,RegisterCalls.beforeCall,Exec.commitHost,Store.setMemOf,Store.memOf,hi]
  simp only [Option.bind_some,chargedStore]
  simp [hb,hv]

private theorem lengthStore_memory (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst)
    (index : Nat) (memory : Memory)
    (hi : mi.memAddrs[0]? = some index) (hm : s.mems[index]? = some memory) :
    (RegisterCalls.lengthStore cfg s mi).mems[index]? = some memory := by
  have hb := (Array.getElem?_eq_some_iff.mp hm).1
  have hv := (Array.getElem?_eq_some_iff.mp hm).2
  simp only [RegisterCalls.lengthStore,RegisterCalls.lengthAfter,RegisterRead.paid,Output.paidStore,
    RegisterCalls.beforeCall,Exec.commitHost,Store.setMemOf,Store.memOf,hi]
  simp only [Option.bind_some,chargedStore]
  simp [hb,hv]

 theorem readAfter_memory (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst)
    (index : Nat) (memory : Memory) (ptr : UInt64) (bytes : List UInt8)
    (hi : mi.memAddrs[0]? = some index) (hm : s.mems[index]? = some memory) :
    (readAfter cfg s mi ptr bytes).mems[index]? = some (memory.writeList ptr.toNat bytes) := by
  apply readStore_memory cfg (paid s cfg.regularOpCost 2) mi index memory ptr bytes hi
  rw [paid_mems]; exact hm

 theorem lengthAfter_memory (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst)
    (index : Nat) (memory : Memory)
    (hi : mi.memAddrs[0]? = some index) (hm : s.mems[index]? = some memory) :
    (lengthAfter cfg s mi).mems[index]? = some memory := by
  apply lengthStore_memory cfg (paid s cfg.regularOpCost 1) mi index memory hi
  rw [paid_mems]; exact hm

 theorem readCallAfter_memory (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst)
    (index : Nat) (memory : Memory) (ptr : UInt64) (bytes : List UInt8)
    (hi : mi.memAddrs[0]? = some index) (hm : s.mems[index]? = some memory) :
    (readCallAfter cfg s mi ptr bytes).mems[index]? = some (memory.writeList ptr.toNat bytes) :=
  readAfter_memory cfg (enteredRead s cfg.regularOpCost) mi index memory ptr bytes hi hm

 theorem lengthCallAfter_memory (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst)
    (index : Nat) (memory : Memory)
    (hi : mi.memAddrs[0]? = some index) (hm : s.mems[index]? = some memory) :
    (lengthCallAfter cfg s mi).mems[index]? = some memory :=
  lengthAfter_memory cfg (enteredLength s cfg.regularOpCost) mi index memory hi hm

 theorem readAfter_fields (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) (ptr : UInt64) (bytes : List UInt8) :
    (readAfter cfg s mi ptr bytes).funcs = s.funcs ∧ (readAfter cfg s mi ptr bytes).modules = s.modules ∧
    (readAfter cfg s mi ptr bytes).tables = s.tables ∧ (readAfter cfg s mi ptr bytes).globals = s.globals :=
  RegisterCalls.readStore_fields cfg (paid s cfg.regularOpCost 2) mi ptr bytes

 theorem lengthAfter_fields (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) :
    (lengthAfter cfg s mi).funcs = s.funcs ∧ (lengthAfter cfg s mi).modules = s.modules ∧
    (lengthAfter cfg s mi).tables = s.tables ∧ (lengthAfter cfg s mi).globals = s.globals :=
  RegisterCalls.lengthStore_fields cfg (paid s cfg.regularOpCost 1) mi

 theorem readCallAfter_fields (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) (ptr : UInt64) (bytes : List UInt8) :
    (readCallAfter cfg s mi ptr bytes).funcs = s.funcs ∧ (readCallAfter cfg s mi ptr bytes).modules = s.modules ∧
    (readCallAfter cfg s mi ptr bytes).tables = s.tables ∧ (readCallAfter cfg s mi ptr bytes).globals = s.globals :=
  readAfter_fields cfg (enteredRead s cfg.regularOpCost) mi ptr bytes

 theorem lengthCallAfter_fields (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst) :
    (lengthCallAfter cfg s mi).funcs = s.funcs ∧ (lengthCallAfter cfg s mi).modules = s.modules ∧
    (lengthCallAfter cfg s mi).tables = s.tables ∧ (lengthCallAfter cfg s mi).globals = s.globals :=
  lengthAfter_fields cfg (enteredLength s cfg.regularOpCost) mi

end WNear.Proofs.StateReadRegister
