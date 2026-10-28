import Proofs.StateReadRegisterOuterReadCode
import Proofs.StateReadRegisterOuterFrame
import Proofs.StateReadRegisterOuterHost

/-! The real435 leaf is ready from523's original native/installed-code/resources;
all post-allocation reads, code facts and register contents are derived. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readArguments allocated
private theorem mems_paid (s : Store NearState) (op n : Nat) : (StorePairCaller.paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih

theorem Code.read_ready (cfg : WasmConfig) (s : Store NearState) (limits : ExecLimits)
    (inst height : Nat) (callers : List CallFrame) (p : Layout) (extra : Nat)
    (hn : Native p) (ha : p.allocator=1074896) (hcode : Code s inst p extra)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global523)
    (hr : s.host.registers p.register.toNat=some p.bytes) (hd : callers.length+4<limits.maxCallDepth) :
    StateDispatchRead.Ready (readArguments cfg s p) limits
      (StateDispatchRead.leafFrame inst height (readLayout p)) callers (readLayout p) p.bytes extra := by
  have snapshot := read_snapshot p hn ha
  have fields := readArguments_fields cfg s p
  have code := (hcode.actualRead s inst p extra hn ha).transport s (readArguments cfg s p)
    (readLayout p) inst extra fields.1 fields.2.1 fields.2.2
  have memory : (readArguments cfg s p).mems[p.memoryIndex]?=some (readInputMemory p) := by
    rw [readArguments,mems_paid]
    exact allocated_memory cfg s limits inst height callers p extra hn ha hcode hm hg hr hd
  have global := readArguments_global cfg s p hn ha hg
  have regs : (readArguments cfg s p).host.registers p.register.toNat=some p.bytes := by
    rw [readArguments_registers cfg s p];exact hr
  apply snapshot.ready (readArguments cfg s p) limits
    (StateDispatchRead.leafFrame inst height (readLayout p)) callers extra code
    rfl rfl rfl (by change 5≤5; omega) memory global rfl regs
  omega
end WNear.Proofs.StateReadRegisterOuter
