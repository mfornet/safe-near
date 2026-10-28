import Proofs.StateReadStorageOuterFrame
import Proofs.StateReadStorageOuterRegisterNative

/-! Code arrays and globals through the actual548 register-reader call. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] guarded registerArguments registered actualRegister
private theorem funcs_paid (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem modules_paid (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem tables_paid (s : Store NearState) (op n : Nat) : (paid s op n).tables=s.tables := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with |zero=>rfl |succ n ih=>exact ih

theorem registerArguments_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key : List UInt8) :
    (registerArguments cfg s p ctx key).funcs=s.funcs ∧
    (registerArguments cfg s p ctx key).modules=s.modules ∧
    (registerArguments cfg s p ctx key).tables=s.tables := by
  simp only [registerArguments,guarded,funcs_paid,modules_paid,tables_paid]
  exact stored_fields cfg s p ctx key

theorem registerArguments_global (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key : List UInt8) (hn : Native p)
    (hg : s.globals[p.globalIndex]?=some p.global548) :
    (registerArguments cfg s p ctx key).globals[p.globalIndex]?=some p.global523 := by
  rw [registerArguments,globals_paid,guarded,globals_paid]
  exact stored_global cfg s p ctx key hn hg

theorem registered_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key : List UInt8) :
    (registered cfg s p ctx key).funcs=s.funcs ∧ (registered cfg s p ctx key).modules=s.modules ∧
    (registered cfg s p ctx key).tables=s.tables := by
  have call := StateReadRegisterOuter.callAfter_fields cfg (registerArguments cfg s p ctx key) (actualRegister p)
  have before := registerArguments_fields cfg s p ctx key
  unfold registered
  exact ⟨call.1.trans before.1,call.2.1.trans before.2.1,call.2.2.trans before.2.2⟩

theorem registered_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key : List UInt8) (hn : Native p) (ha : p.allocator=1074896)
    (hg : s.globals[p.globalIndex]?=some p.global548) :
    (registered cfg s p ctx key).globals=(registerArguments cfg s p ctx key).globals := by
  have sg : (registerArguments cfg s p ctx key).globals[(actualRegister p).globalIndex]?=some (actualRegister p).global523 :=
    by simpa only [actualRegister,registerTemplate] using registerArguments_global cfg s p ctx key hn hg
  have sp : (actualRegister p).global523.value=.i32 (actualRegister p).sp523 := by
    simp only [actualRegister,registerTemplate,hn.registerGlobal,hn.registerSP]
  unfold registered
  exact StateReadRegisterOuter.callAfter_globals cfg (registerArguments cfg s p ctx key) (actualRegister p) (register_native p hn ha) (by simpa only [actualRegister,registerTemplate] using ha) sg sp

theorem registered_global (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key : List UInt8) (hn : Native p) (ha : p.allocator=1074896)
    (hg : s.globals[p.globalIndex]?=some p.global548) :
    (registered cfg s p ctx key).globals[p.globalIndex]?=some p.global523 := by
  rw [registered_globals cfg s p ctx key hn ha hg]
  exact registerArguments_global cfg s p ctx key hn hg
end WNear.Proofs.StateReadStorageOuter
