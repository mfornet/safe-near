import Skeleton.StorageResources

/-!
# Original credits pay the storage-call prefix

Loading, activation, constants, the input call, and storage's call opcode are
paid in their actual order. This is arithmetic on computed intermediate stores;
no host-invocation or whole-method execution equation is assumed. Input limits
are separate semantic obligations for reaching those stores in an execution.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near Wasm.Near.MeteredLogic

namespace StorageCredits

theorem charged (store : Store NearState) (cost rest : Nat)
    (h : store.host.gas.Credits (cost + rest)) :
    (chargedStore store cost).host.gas.Credits rest :=
  (Pays.chargeWasm (.done [] store) cost rest h).2.2.2.2

theorem chargedMany (store : Store NearState) (cost rest count : Nat)
    (h : store.host.gas.Credits (count * cost + rest)) :
    (WNear.Skeleton.chargedMany store cost count).host.gas.Credits rest := by
  induction count generalizing store with
  | zero => simpa only [WNear.Skeleton.chargedMany, Nat.zero_mul, Nat.zero_add] using h
  | succ count ih =>
    apply ih
    apply charged
    simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Actual loading and the eight activation opcodes consume their own budget. -/
theorem active (cfg : RuntimeConfig) (ctx : VMContext) (raw : Storage) (rest : Nat)
    (h : (ctx.toNearState cfg raw).gas.Credits
      (MeteredHosts.burnSum (ctx.toNearState cfg raw).extCosts (loadingCharges 0) +
        (8 * cfg.wasm.regularOpCost + rest))) :
    (executionActive cfg ctx raw).gas.Credits rest := by
  have hl := MeteredHosts.applyCharges_credits (ctx.toNearState cfg raw) (loadingCharges 0)
    (8 * cfg.wasm.regularOpCost + rest) (by simp [loadingCharges, MeteredHosts.BurnsOnly]) h
  have ha := GasCounter.burn_credits (executionLoaded cfg ctx raw).gas
    (8 * cfg.wasm.regularOpCost) rest (by simpa only [executionLoaded] using hl.2.2.2.2)
  simpa only [executionActive, chargeHost] using ha.2.2.2

/-- The input host cost is invariant under the call opcode's gas charge. -/
theorem inputBefore_cost (cfg : WasmConfig) (store : Store NearState) :
    MeteredHosts.Input.cost (inputBefore cfg store moduleInstance).host =
      MeteredHosts.Input.cost store.host := rfl

/-- Body-entry credits pay the prefix to the actual storage host view. -/
theorem body_storage (cfg : RuntimeConfig) (store : Store NearState)
    (post : HostStore NearState) (storageCost rest : Nat)
    (h : store.host.gas.Credits (successBudget cfg store post storageCost rest)) :
    (inputBefore cfg.wasm (successStorageBefore cfg store) moduleInstance).host.gas.Credits
      (storageCost + (successCosts cfg store post storageCost).storageSuffix cfg.wasm.regularOpCost rest) := by
  let cost := successCosts cfg store post storageCost
  have hb : store.host.gas.Credits (cost.bodyBudget cfg.wasm.regularOpCost rest) := by
    rw [successBudget_eq]
    exact h
  have hconst : (successInputBefore cfg store).host.gas.Credits
      (cost.inputBudget cfg.wasm.regularOpCost rest) := by
    apply chargedMany
    simpa only [HostCosts.bodyBudget, Nat.one_mul] using hb
  have hcall : (inputBefore cfg.wasm (successInputBefore cfg store) moduleInstance).host.gas.Credits
      (MeteredHosts.Input.cost (inputBefore cfg.wasm (successInputBefore cfg store) moduleInstance).host +
        cost.inputSuffix cfg.wasm.regularOpCost rest) := by
    rw [inputBefore_cost]
    apply charged
    simpa only [HostCosts.inputBudget, cost, successCosts_input] using hconst
  have hi := MeteredHosts.Input.paid_credits
    (inputBefore cfg.wasm (successInputBefore cfg store) moduleInstance)
    (cost.inputSuffix cfg.wasm.regularOpCost rest) hcall
  have hinput : (successInputAfter cfg store).host.gas.Credits
      (cost.inputSuffix cfg.wasm.regularOpCost rest) := hi.2.2.2
  have hfive : (successStorageBefore cfg store).host.gas.Credits
      (cost.storageBudget cfg.wasm.regularOpCost rest) := by
    apply chargedMany
    simpa only [commitCall_host, HostCosts.inputSuffix] using hinput
  have hc : (inputBefore cfg.wasm (successStorageBefore cfg store) moduleInstance).host.gas.Credits
      (cost.storage + cost.storageSuffix cfg.wasm.regularOpCost rest) := by
    apply charged
    simpa only [HostCosts.storageBudget] using hfive
  simpa only [cost, successCosts_storage] using hc

end StorageCredits

/-- One original budget hypothesis supplies the local credits required by
`empty_storageFrontier`, without an additional storage-entry gas assumption. -/
theorem storageInput_credits (cfg : RuntimeConfig) (ctx : VMContext) (raw : Storage)
    (post : HostStore NearState) (storageCost rest : Nat)
    (h : (ctx.toNearState cfg raw).gas.Credits
      (executionBudget cfg ctx raw post storageCost rest)) :
    (storageInput cfg ctx raw).host.gas.Credits
      (storageCost + (successCosts cfg (executionStore cfg ctx raw) post storageCost).storageSuffix
        cfg.wasm.regularOpCost rest) := by
  have ha := StorageCredits.active cfg ctx raw
    (successBudget cfg (executionStore cfg ctx raw) post storageCost rest) h
  apply StorageCredits.body_storage
  simpa only [executionStore, initialized_host] using ha

end WNear.Skeleton
