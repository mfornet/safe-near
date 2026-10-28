import Proofs.StateReadStorageOuterCallFrame
import Proofs.StateReadStorageOuterSetupFrame
import Proofs.StateReadStorageOuterNative
import Proofs.StateReadStorageOuterPhases

/-! Code arrays and the reserved stack pointer survive the actual storage call. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] stored storageArguments

theorem stored_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key : List UInt8) :
    (stored cfg s p ctx key).funcs=s.funcs ∧ (stored cfg s p ctx key).modules=s.modules ∧
    (stored cfg s p ctx key).tables=s.tables := by
  have call := StateDispatchStorage.callAfter_fields cfg (storageArguments s cfg.regularOpCost p)
    (storageLayout p) ctx key p.bytes
  have setup := storageArguments_fields s cfg.regularOpCost p
  unfold stored
  exact ⟨call.1.trans setup.1,call.2.1.trans setup.2.1,call.2.2.trans setup.2.2⟩

theorem stored_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key : List UInt8) (_hn : Native p)
    (hg : s.globals[p.globalIndex]?=some p.global548) :
    (stored cfg s p ctx key).globals=(storageArguments s cfg.regularOpCost p).globals := by
  have sg := storageArguments_global s cfg.regularOpCost p hg
  unfold stored
  exact StateDispatchStorage.callAfter_globals cfg (storageArguments s cfg.regularOpCost p)
    (storageLayout p) ctx key p.bytes sg rfl

theorem stored_global (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key : List UInt8) (hn : Native p)
    (hg : s.globals[p.globalIndex]?=some p.global548) :
    (stored cfg s p ctx key).globals[p.globalIndex]?=some p.global523 := by
  rw [stored_globals cfg s p ctx key hn hg,hn.registerGlobal]
  exact storageArguments_global s cfg.regularOpCost p hg
end WNear.Proofs.StateReadStorageOuter
