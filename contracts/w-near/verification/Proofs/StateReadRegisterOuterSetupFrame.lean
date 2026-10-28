import Proofs.StateReadRegisterOuterState

/-! Exact scalar523 setup effects before the real524 invocation. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] reserved registerStore lengthArguments registerMemory

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

theorem registerStore_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (registerStore s op p).mems[p.memoryIndex]?=some (registerMemory p) := by
  have me : (paid (reserved s op p) op 3).mems[p.memoryIndex]?=some p.memory := by
    rw [mems_paid,reserved,setGlobal,mems_paid];exact hm
  simpa only [registerStore,registerMemory] using storeI64_memory (paid (reserved s op p) op 3) p.memoryIndex ((scratch p).toNat+24) p.memory p.register me

theorem lengthArguments_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (lengthArguments s op p).mems[p.memoryIndex]?=some (registerMemory p) := by
  rw [lengthArguments,mems_paid];exact registerStore_memory s op p hm

theorem lengthArguments_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (lengthArguments s op p).funcs=s.funcs ∧ (lengthArguments s op p).modules=s.modules ∧ (lengthArguments s op p).tables=s.tables := by
  simp only [lengthArguments,registerStore,storeI64_funcs,storeI64_modules,storeI64_tables,funcs_paid,modules_paid,tables_paid,reserved,setGlobal]
  simp only [and_self]

theorem lengthArguments_global (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global523) :
    (lengthArguments s op p).globals[p.globalIndex]?=some {p.global523 with value:=.i32 (scratch p)} := by
  rw [lengthArguments,globals_paid,registerStore,storeI64_globals,globals_paid,reserved]
  simp only [setGlobal,globals_paid,Array.getElem?_modify,hg,Option.map_some]
  rfl

theorem lengthArguments_registers (s : Store NearState) (op : Nat) (p : Layout) :
    (lengthArguments s op p).host.registers=s.host.registers := by
  simp only [lengthArguments,registerStore,storeI64_host,reserved,setGlobal,paid,chargedStore,chargeHost]

theorem lengthArguments_costs (s : Store NearState) (op : Nat) (p : Layout) :
    (lengthArguments s op p).host.extCosts=s.host.extCosts := by
  simp only [lengthArguments,registerStore,storeI64_host,reserved,setGlobal,paid,chargedStore,chargeHost]

theorem lengthArguments_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (12*op+rest)) : (lengthArguments s op p).host.gas.Credits rest := by
  simpa only [lengthArguments,registerStore,storeI64_host,reserved,setGlobal,paid,chargedStore] using paid_credits s op 12 rest hc
end WNear.Proofs.StateReadRegisterOuter
