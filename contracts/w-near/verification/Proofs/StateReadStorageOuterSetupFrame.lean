import Proofs.StateReadStorageOuterState

/-! Exact f548 setup effects before its real storage-read invocation. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] reserved highStore setupStore storageArguments highMemory setupMemory

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem funcs_paid (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem tables_paid (s : Store NearState) (op n : Nat) : (paid s op n).tables=s.tables := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with | zero=>rfl | succ n ih=>exact ih

theorem highStore_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (highStore s op p).mems[p.memoryIndex]?=some (highMemory p) := by
  have me : (paid (reserved s op p) op 3).mems[p.memoryIndex]?=some p.memory := by
    rw [mems_paid,reserved,setGlobal,mems_paid];exact hm
  simpa only [highStore,highMemory] using storeI32_memory (paid (reserved s op p) op 3) p.memoryIndex ((scratch p).toNat+12) p.memory p.keyLen me

theorem setupStore_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (setupStore s op p).mems[p.memoryIndex]?=some (setupMemory p) := by
  have me : (paid (highStore s op p) op 3).mems[p.memoryIndex]?=some (highMemory p) := by
    rw [mems_paid];exact highStore_memory s op p hm
  simpa only [setupStore,setupMemory] using storeI32_memory (paid (highStore s op p) op 3) p.memoryIndex ((scratch p).toNat+8) (highMemory p) p.keyPtr me

theorem storageArguments_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (storageArguments s op p).mems[p.memoryIndex]?=some (setupMemory p) := by
  rw [storageArguments,mems_paid];exact setupStore_memory s op p hm

theorem storageArguments_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (storageArguments s op p).funcs=s.funcs ∧ (storageArguments s op p).modules=s.modules ∧ (storageArguments s op p).tables=s.tables := by
  simp only [storageArguments,setupStore,highStore,storeI32_funcs,storeI32_modules,storeI32_tables,funcs_paid,modules_paid,tables_paid,reserved,setGlobal]
  simp only [and_self]

theorem storageArguments_global (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global548) :
    (storageArguments s op p).globals[p.globalIndex]?=some {p.global548 with value:=.i32 (scratch p)} := by
  rw [storageArguments,globals_paid,setupStore,storeI32_globals,globals_paid,highStore,storeI32_globals,globals_paid,reserved]
  simp only [setGlobal,globals_paid,Array.getElem?_modify,hg,Option.map_some]
  rfl

theorem storageArguments_registers (s : Store NearState) (op : Nat) (p : Layout) :
    (storageArguments s op p).host.registers=s.host.registers := by
  simp only [storageArguments,setupStore,highStore,storeI32_host,reserved,setGlobal,paid,chargedStore,chargeHost]

theorem storageArguments_costs (s : Store NearState) (op : Nat) (p : Layout) :
    (storageArguments s op p).host.extCosts=s.host.extCosts := by
  simp only [storageArguments,setupStore,highStore,storeI32_host,reserved,setGlobal,paid,chargedStore,chargeHost]

theorem storageArguments_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (15*op+rest)) : (storageArguments s op p).host.gas.Credits rest := by
  simpa only [storageArguments,setupStore,highStore,storeI32_host,reserved,setGlobal,paid,chargedStore] using paid_credits s op 15 rest hc
end WNear.Proofs.StateReadStorageOuter
