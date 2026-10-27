import Skeleton.EmptyCost
import Skeleton.EmptySuccess
import Skeleton.SuccessGas

/-!
# Original-data cost of the successful empty-base method

Output-data receipts are included by receiver, with the actual same-account
send fee. The formula depends on original context data, never an execution.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near Wasm.Near.MeteredLogic
open MeteredHosts

/-- The actual byte-receipt charge for returning the input. -/
def returnDataCost (fees : ActionFees) (receivers : List Near.Bytes)
    (current : Near.Bytes) (length : Nat) : Nat :=
  (receivers.map fun receiver =>
    fees.newDataReceiptByte.send (receiver == current) * length +
      fees.newDataReceiptByte.execution * length).sum

def valueReturnCost (costs : ExtCosts) (fees : ActionFees)
    (receivers : List Near.Bytes) (current : Near.Bytes) (length : Nat) : Nat :=
  costs.cost "base" + costs.cost "read_register_base" +
    costs.cost "read_register_byte" * length + returnDataCost fees receivers current length

/-- The actual sentinel return reads register zero and then pays data bytes. -/
theorem returnPlan_of_register (st : HostStore NearState) (bytes : Near.Bytes)
    (hregister : st.host.registers 0 = some bytes)
    (hlimit : withinLimit st.host.config.maxReturnLen bytes.length = true) :
    chargesBefore "value_return" st [.i64 u64Max, .i64 0] =
      [.ext "base", .ext "read_register_base", .ext "read_register_byte" bytes.length,
        .burn (returnDataCost st.host.fees st.host.outputDataReceivers
          st.host.context.currentAccountId bytes.length)] := by
  simp [chargesBefore, storageMutationPlan?, chargesBeforeUnvalidated, creationAccountArgs,
    argU64, spanLen, getMemOrReg, readSpan, hregister, hlimit, returnDataCost]

theorem returnCost_of_register (cfg : WasmConfig) (store : Store NearState) (bytes : Near.Bytes)
    (hregister : store.host.registers 0 = some bytes)
    (hlimit : withinLimit store.host.config.maxReturnLen bytes.length = true) :
    returnCost cfg store = valueReturnCost store.host.extCosts store.host.fees
      store.host.outputDataReceivers store.host.context.currentAccountId bytes.length := by
  rw [returnCost, returnCharges, returnPlan_of_register _ bytes hregister hlimit]
  simp [burnSum, burnCost, valueReturnCost, inputBefore, chargedStore, chargeHost, Nat.add_assoc]

private def costView (host : NearState) :=
  (host.extCosts, host.fees, host.outputDataReceivers, host.context.currentAccountId,
    host.registers 0, host.config.maxReturnLen)

private theorem charged_costView (store : Store NearState) (cost : Nat) :
    costView (chargedStore store cost).host = costView store.host := rfl

private theorem chargedMany_costView (store : Store NearState) (cost n : Nat) :
    costView (chargedMany store cost n).host = costView store.host := by
  induction n generalizing store with
  | zero => rfl
  | succ n ih => simpa only [chargedMany, charged_costView] using ih (chargedStore store cost)

private theorem inputBefore_costView (cfg : WasmConfig) (store : Store NearState) :
    costView (inputBefore cfg store moduleInstance).host = costView store.host := rfl

private theorem saved_costView (before : HostStore NearState) :
    costView (savedAfter before).host = costView before.host := by
  have h := congrArg costView (applyCharges_frame before.host savedCharges (by
    simp only [savedCharges, extCharges, List.mem_map]
    rintro _ ⟨_, _, rfl⟩
    trivial))
  exact h

private theorem successReturn_costView (cfg : RuntimeConfig) (store : Store NearState)
    (storage : HostStore NearState) :
    costView (successReturnBefore cfg store storage).host = costView storage.host := by
  simp only [successReturnBefore, chargedMany_costView, commitCall_host,
    successLogAfter, saved_costView, inputBefore_costView, successLogBefore, charged_costView]

/-- Logging and regular opcodes preserve every input to the return cost. -/
theorem successReturn_cost (cfg : RuntimeConfig) (store : Store NearState)
    (storage : HostStore NearState) (bytes : Near.Bytes)
    (hregister : storage.host.registers 0 = some bytes)
    (hlimit : withinLimit storage.host.config.maxReturnLen bytes.length = true) :
    returnCost cfg.wasm (successReturnBefore cfg store storage) =
      valueReturnCost storage.host.extCosts storage.host.fees storage.host.outputDataReceivers
        storage.host.context.currentAccountId bytes.length := by
  have hf := successReturn_costView cfg store storage
  have hext := congrArg (fun fields => fields.1) hf
  have hfees := congrArg (fun fields => fields.2.1) hf
  have hreceivers := congrArg (fun fields => fields.2.2.1) hf
  have hcurrent := congrArg (fun fields => fields.2.2.2.1) hf
  have hreg := congrArg (fun fields => fields.2.2.2.2.1) hf
  have hlen := congrArg (fun fields => fields.2.2.2.2.2) hf
  dsimp only [costView] at hext hfees hreceivers hcurrent hreg hlen
  rw [returnCost_of_register cfg.wasm (successReturnBefore cfg store storage) bytes (hreg.trans hregister)]
  · rw [hext, hfees, hreceivers, hcurrent]
  · simpa only [hlen] using hlimit

/-- A context-only sufficient-success cost for the empty-base specialization.
The receipt receivers and same-account fee tests are original inputs. -/
def saveEmptyCost (ctx : NearInterface.Context) : Nat :=
  let cfg := ctx.protocol
  let cost := cfg.wasm.extCosts.cost
  burnSum cfg.wasm.extCosts (loadingCharges 0) + 23 * cfg.wasm.regularOpCost +
    (cost "base" + cost "write_register_base") + emptyStorageCost cfg ctx.args.length +
    burnSum cfg.wasm.extCosts savedCharges +
    valueReturnCost cfg.wasm.extCosts cfg.fees.actionFees
      (Near.Boundary.toVMContext ctx).outputDataReceivers ctx.current.bytes ctx.args.length

private theorem active_extCosts (cfg : RuntimeConfig) (ctx : VMContext) (raw : Storage) :
    (executionActive cfg ctx raw).extCosts = cfg.wasm.extCosts := by
  have h := congrArg NearState.extCosts (applyCharges_frame (ctx.toNearState cfg raw)
    (loadingCharges 0) (by simp [loadingCharges, BurnsOnly]))
  simpa only [executionActive, executionLoaded, chargeHost, VMContext.toNearState] using h

/-- The computed empty-success budget equals a formula in original context
fields plus the unused frame, for every raw listing. -/
theorem executionBudget_empty_eq (ctx : NearInterface.Context) (raw : Storage) (rest : Nat)
    (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hreturn : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthReturnedData) :
    executionBudget ctx.protocol (Near.Boundary.toVMContext ctx) raw
      (emptyAfter ctx raw) (emptyCost ctx raw) rest = saveEmptyCost ctx + rest := by
  have hf := emptyAfter_frame ctx raw
  have hext := emptyAfter_extCosts ctx raw
  have hfees := (StorageFrame.Frame.fees hf).trans
    (storageInput_fees ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have ho := congrArg NearState.outputDataReceivers hf.2
  have hreceivers : (emptyAfter ctx raw).host.outputDataReceivers =
      (Near.Boundary.toVMContext ctx).outputDataReceivers :=
    ho.trans (storageInput_outputDataReceivers ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have hcurrent := (StorageFrame.Frame.currentAccountId hf).trans (storageInput_represents ctx raw).1
  have hregister := (congrFun (StorageFrame.Frame.registers hf) 0).trans
    (storageInput_register ctx.protocol (Near.Boundary.toVMContext ctx) raw)
  have hlimit : withinLimit (emptyAfter ctx raw).host.config.maxReturnLen ctx.args.length = true := by
    rw [emptyAfter_config]
    change withinLimit (some ctx.protocol.wasm.limits.maxLengthReturnedData) ctx.args.length = true
    simpa [withinLimit] using hreturn
  have hr := successReturn_cost ctx.protocol
    (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) (emptyAfter ctx raw)
    ctx.args hregister hlimit
  rw [hext, hfees, hreceivers, hcurrent] at hr
  have hi : Input.cost (successInputBefore ctx.protocol
      (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw)).host =
      ctx.protocol.wasm.extCosts.cost "base" + ctx.protocol.wasm.extCosts.cost "write_register_base" := by
    change Input.cost (executionActive ctx.protocol (Near.Boundary.toVMContext ctx) raw) = _
    simp only [Input.cost, active_extCosts]
  have hl : (successLogBefore ctx.protocol
      (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) raw) (emptyAfter ctx raw)).host.extCosts =
      ctx.protocol.wasm.extCosts := by
    exact hext
  rw [executionBudget_eq, hi, hl, hr, emptyCost_eq ctx raw hpages hkey hvalue]
  rfl

/-- A bound on the original gas limit supplies all initial credits for the
computed empty-success budget, without an intermediate-state assumption. -/
theorem emptyCredits_of_gasLimit (ctx : NearInterface.Context) (raw : Storage) (rest : Nat)
    (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalue : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hreturn : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthReturnedData)
    (hgas : saveEmptyCost ctx + rest ≤ ctx.gasLimit) :
    ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol raw).gas.Credits
      (executionBudget ctx.protocol (Near.Boundary.toVMContext ctx) raw
        (emptyAfter ctx raw) (emptyCost ctx raw) rest) := by
  apply (Near.Boundary.initial_credits_iff ctx raw _).mpr
  rw [executionBudget_empty_eq ctx raw rest hpages hkey hvalue hreturn]
  exact hgas

/-- The sufficient-gas clause for the original-data empty-base success slice:
actual receipt/model matching and a context-only used-gas bound. This leaves
all nonempty-base, deterministic-failure and low-gas clauses separate. -/
theorem execOn_empty_matches_and_gas
    (gasBound : NearInterface.Context → Option Storage → Unit → Nat)
    (ctx : NearInterface.Context) (storage : Storage) (st : Option Storage)
    (hwf : ctx.WF storage.toFinset)
    (hrepresented : (model gasBound).Represents storage.toFinset st)
    (hmethod : ctx.method = "save") (hp : PreparationLimits ctx.protocol) (hm : ModelSaveLimits ctx)
    (hread : ctx.protocol.wasm.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hroom : ctx.storageUsage + 1 + ctx.args.length + ctx.protocol.fees.numExtraBytesRecord < 2 ^ 64)
    (hstake : NearInterface.stakeDeficit ctx.protocol
      (ctx.storageUsage - NearInterface.storageUsageOf ctx.protocol storage.toFinset +
        NearInterface.storageUsageOf ctx.protocol (savedStorage storage ctx.args).toFinset)
      (ctx.balance + ctx.attached) ctx.locked = 0)
    (hgas : saveEmptyCost ctx ≤ ctx.gasLimit)
    (hproof : recordedStorageError (emptyPaid ctx storage)
      (ctx.trie.set (Near.TrieOverlay.contractKey (emptyPaid ctx storage).context.currentAccountId
        "k".toUTF8.toList) ctx.args) = none) :
    NearInterface.Matches (model gasBound) ctx storage.toFinset (Near.Boundary.execOn code storage ctx)
      ((model gasBound).step ctx st ()) ∧
    (Near.Boundary.execOn code storage ctx).usedGas ≤ saveEmptyCost ctx := by
  have hc := emptyCredits_of_gasLimit ctx storage 0 hp.positive hm.key hm.value hm.returned
    (by simpa only [Nat.add_zero] using hgas)
  have hr := emptyAfter_resources ctx storage 0 hwf hp hm hread hentries hselected hc hproof
  have hg := execOn_save_success_used_add_rest_le ctx storage (emptyAfter ctx storage)
    (emptyCost ctx storage) 0 0 hmethod hp hr (emptyAfter_promises ctx storage)
  rw [executionBudget_empty_eq ctx storage 0 hp.positive hm.key hm.value hm.returned] at hg
  simp only [Nat.add_zero] at hg
  exact ⟨execOn_empty_matches_modelStep gasBound ctx storage st 0 hwf hrepresented hmethod hp hm
    hread hentries hselected hroom hstake hc hproof, hg⟩

end WNear.Skeleton
