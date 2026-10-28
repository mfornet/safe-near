import Proofs.StateDecodeScalarState
import Proofs.StateDecodeScalarValues
import Proofs.StateDecodeScalarFinish

/-! Complete accepted scalar-reader computed endpoint and exact selected-path ledger. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic

def values (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  valuesStore wide (dropCached wide cfg s p) cfg.regularOpCost p.memoryIndex (droppedMemory wide p) p.out
    (if wide then highValue p else lowValue wide p) (lowValue wide p)
def updated (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  updateStore (values wide cfg s p) cfg.regularOpCost p.memoryIndex (valuesMemory wide p) p.slice (dropValue wide p)
def restored (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  finishStore (updated wide cfg s p) cfg.regularOpCost p.memoryIndex p.globalIndex (updatedMemory wide p) p.out (scratch p)
def after (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  chargedStore (restored wide cfg s p) cfg.regularOpCost
def bodyCost (wide : Bool) : Nat := if wide then 154 else 138
def bodySteps (wide : Bool) : Nat := if wide then 133 else 117
def activationUnits (wide : Bool) : Nat := if wide then 13 else 12
end WNear.Proofs.StateDecodeScalar
