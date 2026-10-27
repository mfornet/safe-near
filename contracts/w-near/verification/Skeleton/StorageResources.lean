import Skeleton.Execution
import Skeleton.Model
import NearVM.MeteredHosts.StorageOverlay

/-!
# Resources at the actual storage call

Startup, the input call and intervening constants preserve the original storage,
configuration and trie. Register zero holds the original input. These facts
instantiate the storage contracts from the original boundary data.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near Wasm.Near.MeteredLogic

set_option maxHeartbeats 600000

/-- The store observed by storage_write after its actual call-opcode charge. -/
def storageInput (cfg : RuntimeConfig) (ctx : VMContext) (raw : Storage) : HostStore NearState :=
  inputBefore cfg.wasm (successStorageBefore cfg (executionStore cfg ctx raw)) moduleInstance

/-- Forget only startup's billing diagnostics and the synchronized gas field. -/
private def startupView (host : NearState) : NearState :=
  { host with
    gas := {}
    gasProfile := {}
    actionProfile := []
    context := { host.context with usedGas := 0 } }

private theorem chargedMany_view (store : Store NearState) (cost count : Nat) :
    startupView (chargedMany store cost count).host = startupView store.host := by
  induction count generalizing store with
  | zero => rfl
  | succ count ih => simpa only [chargedMany, chargedStore, chargeHost, startupView] using
      (ih (chargedStore store cost))

private theorem inputAfter_view (cfg : WasmConfig) (store : Store NearState) :
    startupView (inputAfter cfg store moduleInstance 0).host =
      startupView (store.host.setRegister 0 store.host.context.input) := by
  let before := inputBefore cfg store moduleInstance
  have hp : startupView (MeteredHosts.Input.paid before).host = startupView before.host := by
    have hf := congrArg (fun st : HostStore NearState => startupView st.host) (MeteredHosts.Input.paid_frame before)
    exact hf
  exact congrArg (fun host : NearState => host.setRegister 0 store.host.context.input) hp

private theorem executionActive_view (cfg : RuntimeConfig) (ctx : VMContext) (raw : Storage) :
    startupView (executionActive cfg ctx raw) = startupView (ctx.toNearState cfg raw) := by
  have hf := congrArg startupView
    (MeteredHosts.applyCharges_frame (ctx.toNearState cfg raw) (loadingCharges 0) (by
      simp [loadingCharges, MeteredHosts.BurnsOnly]))
  simpa only [executionActive, executionLoaded, chargeHost, startupView] using hf

private theorem storageInput_view (cfg : RuntimeConfig) (ctx : VMContext) (raw : Storage) :
    startupView (storageInput cfg ctx raw).host =
      startupView ((ctx.toNearState cfg raw).setRegister 0 ctx.input) := by
  simp only [storageInput, inputBefore, chargedStore, chargeHost]
  change startupView (successStorageBefore cfg (executionStore cfg ctx raw)).host = _
  rw [successStorageBefore, chargedMany_view, commitCall_host, successInputAfter, inputAfter_view]
  simp only [successInputBefore, chargedMany, chargedStore, chargeHost, executionStore, initialized_host]
  have hf := congrArg (fun host : NearState => host.setRegister 0 ctx.input)
    (executionActive_view cfg ctx raw)
  simpa only [startupView, NearState.setRegister, executionActive_input] using hf

/-- Register zero is available to the real register-sentinel storage ABI. -/
theorem storageInput_register (cfg : RuntimeConfig) (ctx : VMContext) (raw : Storage) :
    (storageInput cfg ctx raw).host.registers 0 = some ctx.input := by
  have hf := congrArg (fun host : NearState => host.registers 0) (storageInput_view cfg ctx raw)
  simpa only [startupView, NearState.setRegister, ↓reduceIte] using hf

/-- No preceding host has changed the initialized data memory. -/
theorem storageInput_memory (cfg : RuntimeConfig) (ctx : VMContext) (raw : Storage) :
    (storageInput cfg ctx raw).mem = preparedData cfg := by rfl

/-- Raw storage and the account prefix agree with the original action context. -/
theorem storageInput_represents (ctx : NearInterface.Context) (raw : Storage) :
    MeteredHosts.StorageOverlay.Represents
      (storageInput ctx.protocol (Near.Boundary.toVMContext ctx) raw).host ctx raw := by
  have hf := storageInput_view ctx.protocol (Near.Boundary.toVMContext ctx) raw
  constructor
  · exact congrArg (fun host : NearState => host.context.currentAccountId) hf
  · intro key
    exact congrArg (fun host : NearState => host.storage key) hf

/-- Billing and input-register initialization retain the actual chunk trie. -/
theorem storageInput_accounting (cfg : RuntimeConfig) (ctx : VMContext) (raw : Storage) :
    (storageInput cfg ctx raw).host.storageAccounting = ctx.storageAccounting := by
  exact congrArg NearState.storageAccounting (storageInput_view cfg ctx raw)

/-- The original protocol's host limits remain installed at storage entry. -/
theorem storageInput_config (cfg : RuntimeConfig) (ctx : VMContext) (raw : Storage) :
    (storageInput cfg ctx raw).host.config = (ctx.toNearState cfg raw).config := by
  have hf := congrArg NearState.config (storageInput_view cfg ctx raw)
  exact hf

end WNear.Skeleton
