import Proofs.AllocateRetryCall
import Proofs.AllocateRetryHost
import Proofs.AllocateRetryPayload

/-! Exact observable resources of the actual complete typed581 growth/retry call. -/
namespace WNear.Proofs.AllocateRetry
open Wasm Wasm.Near MeteredLogic
open AllocateSearch (gasUnits_charge)
open AllocateGrowth (GasCost)
set_option maxRecDepth 16384
attribute [local irreducible] after callAfter

theorem callAfter_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (callAfter cfg s p).mems[p.memoryIndex]?=some (finalMemory p) := by
  unfold callAfter
  exact after_memory cfg (entered s cfg.regularOpCost) p hm

theorem callAfter_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (callAfter cfg s p).globals=s.globals := by
  unfold callAfter
  exact after_globals cfg (entered s cfg.regularOpCost) p hg hv

theorem callAfter_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (callAfter cfg s p).funcs=s.funcs ∧ (callAfter cfg s p).modules=s.modules ∧ (callAfter cfg s p).tables=s.tables := by
  unfold callAfter
  exact after_fields cfg (entered s cfg.regularOpCost) p

theorem callAfter_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (603*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (growthLayout p))+rest)) :
    (callAfter cfg s p).host.gas.burnt=s.host.gas.burnt+603*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (growthLayout p)) ∧
    (callAfter cfg s p).host.gas.promises=s.host.gas.promises ∧
    (callAfter cfg s p).host.gas.Credits rest := by
  let op := cfg.regularOpCost
  have first := gasUnits_charge s op 1
  simp only [Nat.one_mul] at first
  have en := first.trans (gasUnits_charge (chargedStore s op) op 11)
  have all := (GasCost.of_units en).trans (after_gas cfg (entered s op) p)
  have cost : (1+11)*op+(591*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (growthLayout p)))=
      603*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (growthLayout p)) := by dsimp [op];omega
  rw [cost] at all
  simpa only [callAfter,entered,op,Nat.add_assoc] using all rest (hc.mono (by omega))

private def view (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_reset (seed old host : NearState) :
    view seed {host with gas:=old.gas,gasProfile:=old.gasProfile}=view seed host := rfl
private theorem view_entered (seed : NearState) (s : Store NearState) (op : Nat) :
    view seed (entered s op).host=view seed s.host := rfl

theorem callAfter_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(callAfter cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  have body := after_functional_host cfg (entered s cfg.regularOpCost) p
  have h := congrArg (view s.host) body
  rw [view_reset,view_entered] at h
  simpa only [view,callAfter] using h
end WNear.Proofs.AllocateRetry
