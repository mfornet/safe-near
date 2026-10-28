import Proofs.StateReadRegisterOuterReadFinal
import Proofs.StateReadRegisterOuterCopyBody
import Proofs.AllocateVectorOuterCall

/-! Actual523 accepted-path states, with each realcallee and sequential finalcopy. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

def guarded (cfg : WasmConfig) (s : Store NearState) (p : Layout) := paid (looked cfg s p) cfg.regularOpCost 5
def vectorArguments (cfg : WasmConfig) (s : Store NearState) (p : Layout) := paid (guarded cfg s p) cfg.regularOpCost 7
def allocated (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  AllocateVectorOuter.callAfter cfg (vectorArguments cfg s p) (actualVector p)
def readArguments (cfg : WasmConfig) (s : Store NearState) (p : Layout) := paid (allocated cfg s p) cfg.regularOpCost 7
def readDone (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  StateDispatchRead.callAfter cfg (readArguments cfg s p) (readLayout p) p.bytes
def copyDone (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  copied (readDone cfg s p) cfg.regularOpCost p.memoryIndex (readFinalMemory p) p.out523 (scratch p)
def branched (cfg : WasmConfig) (s : Store NearState) (p : Layout) := chargedStore (copyDone cfg s p) cfg.regularOpCost
def after (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  setGlobal (paid (branched cfg s p) cfg.regularOpCost 4) p.globalIndex (.i32 p.sp523)
def copiedMemory (p : Layout) := finalMemory (readFinalMemory p) p.out523 (scratch p)
def bodyCost (p : Layout) := AllocateVectorOuter.bodyCost (actualVector p)+601
def bodySteps (p : Layout) := AllocateVectorOuter.bodySteps (actualVector p)+406
def fee (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  AllocateVectorOuter.fee cfg (actualVector p)+s.host.extCosts.cost "base"+
    MeteredHosts.RegisterRead.readCost s.host p.bytes.length
end WNear.Proofs.StateReadRegisterOuter
