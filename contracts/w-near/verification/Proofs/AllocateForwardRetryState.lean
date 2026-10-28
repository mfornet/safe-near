import Binary.AllocateForward
import Proofs.AllocateZeroedRetryGas

/-! Exact239/313 forwarding states for the original empty/growth/retry153 path. -/
namespace WNear.Proofs.AllocateForwardRetry
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

abbrev Layout := AllocateZeroedRetry.Layout
abbrev Native := AllocateZeroedRetry.Native
abbrev Code := AllocateZeroedRetry.Code
abbrev fee (cfg : WasmConfig) (p : Layout) := AllocateZeroedRetry.fee cfg p

def entered153 (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (10*op)
def zeroedAfter (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  AllocateZeroedRetry.after cfg (entered153 s cfg.regularOpCost) p

def after239 (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  zeroedAfter cfg (paid s cfg.regularOpCost 3) p
def cost239 (p : Layout) := AllocateZeroedRetry.bodyCost p+14
def steps239 (p : Layout) := AllocateZeroedRetry.bodySteps p+5
def entered239 (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (9*op)
def callAfter239 (cfg : WasmConfig) (s : Store NearState) (p : Layout) := after239 cfg (entered239 s cfg.regularOpCost) p

def called239 (cfg : WasmConfig) (s : Store NearState) (p : Layout) := callAfter239 cfg (paid s cfg.regularOpCost 2) p
def after313 (cfg : WasmConfig) (s : Store NearState) (p : Layout) := paid (called239 cfg s p) cfg.regularOpCost 3
def cost313 (p : Layout) := cost239 p+15
def steps313 (p : Layout) := steps239 p+7
def entered313 (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (10*op)
def callAfter313 (cfg : WasmConfig) (s : Store NearState) (p : Layout) := after313 cfg (entered313 s cfg.regularOpCost) p
end WNear.Proofs.AllocateForwardRetry
