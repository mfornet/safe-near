import Proofs.StateReadStorageOuterRegisterCode
import Proofs.StateReadStorageOuterFrame
import Proofs.StateReadStorageOuterHost

/-! Actual523 callee resources follow from548's original resources and the real459
register write. No future store lookup or callee execution is an assumption. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] stored storageMemory
private theorem fields_paid (s : Store NearState) (op n : Nat) :
    (paid s op n).funcs=s.funcs ∧ (paid s op n).modules=s.modules ∧ (paid s op n).tables=s.tables := by
  induction n with |zero=>exact ⟨rfl,rfl,rfl⟩ |succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem regs_paid (s : Store NearState) (op n : Nat) : (paid s op n).host.registers=s.host.registers := by
  induction n with |zero=>rfl |succ n ih=>exact ih

theorem stored_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key : List UInt8)
    (hi : p.mi.memAddrs[0]?=some p.memoryIndex) (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (stored cfg s p ctx key).mems[p.memoryIndex]?=some (storageMemory p) := by
  have args := storageArguments_memory s cfg.regularOpCost p hm
  have memory := StateDispatchStorage.callAfter_memory cfg (storageArguments s cfg.regularOpCost p)
    (storageLayout p) ctx key p.bytes hi args
  have index : (storageLayout p).memoryIndex=p.memoryIndex := rfl
  rw [index] at memory
  simpa only [stored,StateDispatchStorage.finalMemory,storageMemory] using memory

theorem register_call_resources (cfg : WasmConfig) (extra : Nat) (s : Store NearState) (inst : Nat)
    (p : Layout) (ctx : NearInterface.Context) (key : List UInt8)
    (hn : Native p) (ha : p.allocator=1074896) (hcode : Code s inst p extra)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global548) :
    let q := actualRegister p
    StateReadRegisterOuter.Code (registerArguments cfg s p ctx key) inst q extra ∧
    (registerArguments cfg s p ctx key).mems[q.memoryIndex]?=some q.memory ∧
    (registerArguments cfg s p ctx key).globals[q.globalIndex]?=some q.global523 ∧
    q.global523.value=.i32 q.sp523 ∧
    (registerArguments cfg s p ctx key).host.registers q.register.toNat=some q.bytes ∧
    q.mi.funcAddrs[523]?=some p.address523 ∧
    (registerArguments cfg s p ctx key).funcs[p.address523]?=
      some (.wasm WNear.Binary.StateReadRegisterOuter.signature inst WNear.Binary.StateReadRegisterOuter.function) := by
  let t := registerArguments cfg s p ctx key
  have a := fields_paid (guarded cfg s p ctx key) cfg.regularOpCost 4
  have b := fields_paid (stored cfg s p ctx key) cfg.regularOpCost 7
  have c := stored_fields cfg s p ctx key
  have fields : t.funcs=s.funcs ∧ t.modules=s.modules ∧ t.tables=s.tables :=
    ⟨a.1.trans (b.1.trans c.1),a.2.1.trans (b.2.1.trans c.2.1),a.2.2.trans (b.2.2.trans c.2.2)⟩
  have code := (hcode.registerCode s inst p extra hn ha).transport s t inst (actualRegister p) extra fields.1 fields.2.1 fields.2.2
  have hi : p.mi.memAddrs[0]?=some p.memoryIndex := hcode.register.prefixCode.memoryIndex
  have memory : t.mems[(actualRegister p).memoryIndex]?=some (actualRegister p).memory := by
    change t.mems[p.memoryIndex]?=some (storageMemory p)
    dsimp only [t]
    rw [registerArguments,mems_paid,guarded,mems_paid]
    exact stored_memory cfg s p ctx key hi hm
  have global : t.globals[(actualRegister p).globalIndex]?=some (actualRegister p).global523 := by
    change t.globals[p.globalIndex]?=some p.global523
    dsimp only [t]
    rw [registerArguments,globals_paid,guarded,globals_paid]
    exact stored_global cfg s p ctx key hn hg
  have value : (actualRegister p).global523.value=.i32 (actualRegister p).sp523 := by
    change p.global523.value=.i32 p.sp523
    rw [hn.registerGlobal,hn.registerSP]
  have reg : t.host.registers (actualRegister p).register.toNat=some (actualRegister p).bytes := by
    change t.host.registers p.register.toNat=some p.bytes
    rw [hn.registerId]
    change t.host.registers 0=some p.bytes
    dsimp only [t]
    rw [registerArguments,regs_paid,guarded,regs_paid]
    exact stored_register_zero cfg s p ctx key
  have fn : t.funcs[p.address523]?=some (.wasm WNear.Binary.StateReadRegisterOuter.signature inst WNear.Binary.StateReadRegisterOuter.function) := by
    rw [fields.1];exact hcode.function523
  exact ⟨code,memory,global,value,reg,hcode.index523,fn⟩
end WNear.Proofs.StateReadStorageOuter
