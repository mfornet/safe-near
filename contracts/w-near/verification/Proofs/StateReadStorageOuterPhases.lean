import Proofs.StateReadStorageOuterState
import Proofs.StateReadResultCall
import Proofs.StateReadStorageOuterGuard

/-! Exact computed selected548 phases and one complete call-cost ledger. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

def guarded (cfg : WasmConfig) (s : Store NearState) (p : Layout) (ctx : NearInterface.Context) (key : List UInt8) :=
  paid (stored cfg s p ctx key) cfg.regularOpCost 7
def registerArguments (cfg : WasmConfig) (s : Store NearState) (p : Layout) (ctx : NearInterface.Context) (key : List UInt8) :=
  paid (guarded cfg s p ctx key) cfg.regularOpCost 4
def registered (cfg : WasmConfig) (s : Store NearState) (p : Layout) (ctx : NearInterface.Context) (key : List UInt8) :=
  StateReadRegisterOuter.callAfter cfg (registerArguments cfg s p ctx key) (actualRegister p)
def optionArguments (cfg : WasmConfig) (s : Store NearState) (p : Layout) (ctx : NearInterface.Context) (key : List UInt8) :=
  paid (registered cfg s p ctx key) cfg.regularOpCost 7
def registeredMemory (p : Layout) := StateReadRegisterOuter.copiedMemory (actualRegister p)
def converted (cfg : WasmConfig) (s : Store NearState) (p : Layout) (ctx : NearInterface.Context) (key : List UInt8) :=
  StateReadResult.callAfter (optionArguments cfg s p ctx key) cfg.regularOpCost p.memoryIndex
    (registeredMemory p) p.out548 (scratch p+16)
def after (cfg : WasmConfig) (s : Store NearState) (p : Layout) (ctx : NearInterface.Context) (key : List UInt8) :=
  setGlobal (paid (converted cfg s p ctx key) cfg.regularOpCost 4) p.globalIndex (.i32 p.sp548)
def finalMemory (p : Layout) := StateReadResult.finalMemory (registeredMemory p) p.out548 (scratch p+16)
def bodyCost (p : Layout) := StateReadRegisterOuter.bodyCost (actualRegister p)+336
def bodySteps (p : Layout) := StateReadRegisterOuter.bodySteps (actualRegister p)+231
def fee (cfg : WasmConfig) (s : Store NearState) (p : Layout) (ctx : NearInterface.Context) (key : List UInt8) :=
  StateDispatchStorage.fee s (storageLayout p) ctx key p.bytes+StateReadRegisterOuter.fee cfg s (actualRegister p)
def guardedFrame (frame : CallFrame) (p : Layout) := statusFrame (reservedFrame frame p)
end WNear.Proofs.StateReadStorageOuter
