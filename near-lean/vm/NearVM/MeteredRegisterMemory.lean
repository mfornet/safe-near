import NearVM.MeteredRegisterFrames

/-! Memory and register observations after committing the real register hosts. -/
namespace Wasm.Near.MeteredLogic.RegisterCalls
open MeteredHosts

theorem readStore_memory (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst)
    (index : Nat) (memory : Memory) (ptr : UInt64) (bytes : List UInt8)
    (hi : mi.memAddrs[0]? = some index) (hm : store.mems[index]? = some memory) :
    (readStore cfg store mi ptr bytes).mems[index]? = some (memory.writeList ptr.toNat bytes) := by
  have hb := (Array.getElem?_eq_some_iff.mp hm).1
  simp [readStore, Exec.commitHost, Store.setMemOf, beforeCall, readAfter,
    Store.memOf, hi, chargedStore, hb, (Array.getElem?_eq_some_iff.mp hm).2]

theorem readStore_other_memory (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst)
    (index other : Nat) (ptr : UInt64) (bytes : List UInt8)
    (hi : mi.memAddrs[0]? = some index) (hne : other ≠ index) :
    (readStore cfg store mi ptr bytes).mems[other]? = store.mems[other]? := by
  simp [readStore, Exec.commitHost, Store.setMemOf, hi, chargedStore, Ne.symm hne]

theorem readStore_registers (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst)
    (ptr : UInt64) (bytes : List UInt8) :
    (readStore cfg store mi ptr bytes).host.registers = store.host.registers := by
  simp only [readStore, commitHost_host, readAfter]
  exact RegisterRead.paid_registers (beforeCall cfg store mi) _ (RegisterRead.readCharges_burns _)

/-- Length queries commit the original memory unchanged at every index. -/
theorem lengthStore_mems (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst)
    (index : Nat) (memory : Memory)
    (hi : mi.memAddrs[0]? = some index) (hm : store.mems[index]? = some memory) :
    (lengthStore cfg store mi).mems = store.mems := by
  have hb := (Array.getElem?_eq_some_iff.mp hm).1
  simp only [lengthStore, Exec.commitHost, Store.setMemOf, hi, lengthAfter,
    RegisterRead.paid, Output.paidStore, beforeCall, chargedStore, Store.memOf, hm,
    Option.bind_some, Option.getD_some]
  apply Array.ext
  · simp
  · intro j h₁ h₂
    by_cases hj : j = index
    · subst j
      simp [(Array.getElem?_eq_some_iff.mp hm).2]
    · exact Array.getElem_setIfInBounds_ne h₂ (Ne.symm hj)

theorem lengthStore_registers (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst) :
    (lengthStore cfg store mi).host.registers = store.host.registers := by
  simp only [lengthStore, commitHost_host, lengthAfter]
  exact RegisterRead.paid_registers (beforeCall cfg store mi) _ (by simp [BurnsOnly])

end Wasm.Near.MeteredLogic.RegisterCalls
