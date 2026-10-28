import Binary.AllocateRawForward
import Proofs.AllocatePositiveSkipGas

/-! Exact236/310 nonzeroing forwarding states for the original one-short-candidate then fitting581 path. -/
namespace WNear.Proofs.AllocateRawForwardSkip
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

abbrev Layout := AllocatePositiveSkip.Layout
abbrev Native := AllocatePositiveSkip.Native
abbrev Code := AllocatePositiveSkip.Code

def entered581 (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (11*op)
def allocatedAfter (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  AllocatePositiveSkip.after (entered581 s cfg.regularOpCost) cfg.regularOpCost p

def after236 (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  allocatedAfter cfg (paid s cfg.regularOpCost 3) p
def cost236 (_p : Layout) := 432
def steps236 (_p : Layout) := 361
def entered236 (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (9*op)
def callAfter236 (cfg : WasmConfig) (s : Store NearState) (p : Layout) := after236 cfg (entered236 s cfg.regularOpCost) p

def called236 (cfg : WasmConfig) (s : Store NearState) (p : Layout) := callAfter236 cfg (paid s cfg.regularOpCost 2) p
def after310 (cfg : WasmConfig) (s : Store NearState) (p : Layout) := paid (called236 cfg s p) cfg.regularOpCost 3
def cost310 (p : Layout) := cost236 p+15
def steps310 (p : Layout) := steps236 p+7
def entered310 (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (10*op)
def callAfter310 (cfg : WasmConfig) (s : Store NearState) (p : Layout) := after310 cfg (entered310 s cfg.regularOpCost) p
end WNear.Proofs.AllocateRawForwardSkip
