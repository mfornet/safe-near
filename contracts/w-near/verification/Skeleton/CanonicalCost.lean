import Skeleton.CanonicalBody
import NearVM.MeteredHosts.StorageCanonicalCost

/-! Original-context budgets for the complete canonical walking body.
The cost reads no execution, lookup result, cache state or old-value bytes. -/
namespace WNear.Skeleton.CanonicalCost
open Wasm Wasm.Near MeteredLogic NearInterface
open MeteredHosts StorageMetered FunctionalInvariant BudgetSimulation CanonicalBody

/-- The empty-write cost plus conservative canonical node, evicted-byte and
replacement-register bills, all from original context data. -/
def saveCost (ctx : Context) : Nat :=
  saveEmptyCost ctx + StorageCanonicalCost.phaseBound ctx.protocol.wasm.extCosts ctx "k".toUTF8.toList +
    StorageCanonicalCost.postBound ctx.protocol.wasm.extCosts ctx

/-- The computed general storage reservation is bounded before the run. -/
theorem storage_cost_le (ctx : Context) (raw : Storage) (host : NearState)
    (hh : PreEq (origin ctx raw) host) (hwf : ctx.WF raw.toFinset)
    (hnodes : ctx.trie.NonzeroNodes)
    (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hk : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hv : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue) :
    cost ctx host ≤ emptyStorageCost ctx.protocol ctx.args.length +
      StorageCanonicalCost.phaseBound ctx.protocol.wasm.extCosts ctx "k".toUTF8.toList +
      StorageCanonicalCost.postBound ctx.protocol.wasm.extCosts ctx := by
  have hb := FundedEmpty.before_resources ctx raw host hh
  have hp := (paid_resources ctx raw host hh).1
  have hr : StorageOverlay.Represents (paid ctx host) ctx raw := by
    refine ⟨hp.current, ?_⟩
    intro key
    rw [hp.storage]
    rfl
  have hre : StorageOverlay.Represents (Output.paidStore (before ctx host) (paid ctx host)).host ctx raw := hr
  have hext : (before ctx host).host.extCosts = ctx.protocol.wasm.extCosts :=
    congrArg NearState.extCosts hb.1.fields
  have hc := StorageCanonicalCost.plan_cost_le ctx.protocol.wasm.extCosts
    (Output.paidStore (before ctx host) (paid ctx host)) ctx raw.toFinset hwf raw rfl hre hnodes "k".toUTF8.toList
  have hpost := StorageCanonicalCost.postCharges_cost_le ctx.protocol.wasm.extCosts
    (Output.paidStore (before ctx host) (paid ctx host)) ctx raw.toFinset hwf raw rfl hre "k".toUTF8.toList
  have hpre := FundedEmpty.cost_eq ctx raw host hh hpages hk hv
  change burnSum (before ctx host).host.extCosts (preCharges ctx host) = _ at hpre
  unfold cost
  rw [hpre, hext]
  simpa only [lookup, Output.paidStore] using Nat.add_le_add (Nat.add_le_add_left hc (emptyStorageCost ctx.protocol ctx.args.length)) hpost

/-- A single original-data reservation funds the complete accepted body for
any framed host, including arbitrary internal gas counters. -/
theorem budget_le (ctx : Context) (raw : Storage) (host : NearState) (rest : Nat)
    (hh : PreEq (origin ctx raw) host) (hwf : ctx.WF raw.toFinset)
    (hnodes : ctx.trie.NonzeroNodes)
    (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hk : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hv : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue) :
    successBudget ctx.protocol (bodyStore ctx host) (after ctx host) (cost ctx host) rest ≤ saveCost ctx + rest := by
  have hb := FundedEmpty.before_resources ctx raw host hh
  have hf := after_frame ctx host
  have hext : (after ctx host).host.extCosts = ctx.protocol.wasm.extCosts :=
    hf.extCosts.trans (congrArg NearState.extCosts hb.1.fields)
  have hfees : (after ctx host).host.fees = ctx.protocol.fees.actionFees :=
    hf.fees.trans (congrArg NearState.fees hb.1.fields)
  have ho := congrArg NearState.outputDataReceivers hf.2
  have hreceivers : (after ctx host).host.outputDataReceivers = (Near.Boundary.toVMContext ctx).outputDataReceivers :=
    ho.trans (congrArg NearState.outputDataReceivers hb.1.fields)
  have hcurrent : (after ctx host).host.context.currentAccountId = ctx.current.bytes :=
    hf.currentAccountId.trans hb.1.fields.current
  have hregister := (congrFun hf.registers 0).trans hb.2
  have hr := successReturn_cost_le ctx.protocol (bodyStore ctx host) (after ctx host) ctx.args hregister
  rw [hext, hfees, hreceivers, hcurrent] at hr
  have hhostExt : host.extCosts = ctx.protocol.wasm.extCosts := congrArg NearState.extCosts hh
  have hi : Input.cost (successInputBefore ctx.protocol (bodyStore ctx host)).host =
      ctx.protocol.wasm.extCosts.cost "base" + ctx.protocol.wasm.extCosts.cost "write_register_base" := by
    simp only [Input.cost, successInputBefore, chargedMany, chargedStore, chargeHost, bodyStore,
      FundedEmpty.bodyStore, initialized_host, hhostExt]
  have hl : (successLogBefore ctx.protocol (bodyStore ctx host) (after ctx host)).host.extCosts = ctx.protocol.wasm.extCosts := hext
  have hc := storage_cost_le ctx raw host hh hwf hnodes hpages hk hv
  unfold successBudget
  rw [hi, hl]
  unfold saveCost saveEmptyCost
  dsimp only
  omega

end WNear.Skeleton.CanonicalCost
