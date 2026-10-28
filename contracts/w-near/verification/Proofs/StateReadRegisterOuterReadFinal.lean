import Proofs.StateReadRegisterOuterReadState

/-! The real435 post-memory first contains the register payload, then the release
writes the decremented counter. Neither phase is discarded from523's copy input. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic

def readCounter (p : Layout) := StateDispatchRead.counter (readLayout p) p.bytes
def readFinalMemory (p : Layout) := writeI32 (readOutputMemory p) (readCounter p).toNat
  (readI32 (readOutputMemory p) (readCounter p).toNat+4294967295)
end WNear.Proofs.StateReadRegisterOuter
