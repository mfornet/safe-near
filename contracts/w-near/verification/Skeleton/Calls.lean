import Skeleton.Body
import Skeleton.Output

/-!
# Discharging the walking body's output calls

These adapters turn semantic host contracts into the single-call evidence
consumed by `wp_save_body`. No Wasm call or method execution is a premise.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near Wasm.Near.MeteredLogic

/-- Functional host view before paying the call opcode. -/
def hostView (store : Store NearState) : HostStore NearState :=
  ⟨(store.memOf moduleInstance).getD (Memory.new 0 none), store.host⟩

/-- Concrete log-call evidence, including the call opcode, exact log billing
and residual credits. The memory and resource premises concern the source store. -/
theorem log_evidence (cfg : RuntimeConfig) (store : Store NearState)
    (pages : Nat) (max : Option Nat) (rest : Nat)
    (hmodule : store.modules[0]? = some moduleInstance)
    (hfn : store.funcs[2]? = some
      (.host (metered cfg.fees.numExtraBytesRecord "log_utf8" logUtf8Fn).toHostFn))
    (hpages : 0 < pages) (hmemory : store.memOf moduleInstance = some (dataMemory pages max))
    (hcount : logCountError (hostView store) = none)
    (hspace : 5 ≤ logSpace (hostView store))
    (hcost : store.host.extCosts.cost "read_memory_byte" * 5 < 2 ^ 64)
    (hpush : ∀ limit, store.host.config.maxLogLen = some limit →
      totalLogLength (hostView store) + 5 ≤ limit)
    (hcredits : store.host.gas.Credits (cfg.wasm.regularOpCost +
      (MeteredHosts.burnSum store.host.extCosts savedCharges + rest))) :
    CallEvidence cfg.wasm store 2 [.i64 5, .i64 1] []
      (metered cfg.fees.numExtraBytesRecord "log_utf8" logUtf8Fn)
      (savedAfter (inputBefore cfg.wasm store moduleInstance))
      (MeteredHosts.burnSum store.host.extCosts savedCharges) rest := by
  let before := inputBefore cfg.wasm store moduleInstance
  have hc := Pays.chargeConfig (atCode store {} #[] saveFrame [] []) cfg.wasm.regularOpCost
    (MeteredHosts.burnSum store.host.extCosts savedCharges + rest) hcredits
  have hi : before.host.gas.Credits
      (MeteredHosts.burnSum before.host.extCosts savedCharges + rest) := hc.2.2.2.2
  obtain ⟨hinvoke, hburn, hpromises, hrest⟩ := metered_saved cfg.fees.numExtraBytesRecord
    before pages max rest hpages
    (by simp only [before, inputBefore, hmemory, Option.getD_some])
    hcount hspace hcost hpush hi
  refine ⟨hmodule, rfl, hfn, rfl, hinvoke, Nat.le_of_eq hburn, ?_, hrest⟩
  change (savedAfter before).host.gas.burnt + (savedAfter before).host.gas.promises ≤
    before.host.gas.burnt + before.host.gas.promises +
      MeteredHosts.burnSum before.host.extCosts savedCharges
  omega

/-- Return-value cost is derived from the host's actual argument-reading and
output-data-receipt plan; it does not inspect an execution result. -/
def returnCharges (cfg : WasmConfig) (store : Store NearState) : List Charge :=
  chargesBefore "value_return" (inputBefore cfg store moduleInstance) [.i64 u64Max, .i64 0]

def returnCost (cfg : WasmConfig) (store : Store NearState) : Nat :=
  MeteredHosts.burnSum store.host.extCosts (returnCharges cfg store)

/-- The explicit paid return store, with a value replacing any promise return. -/
def returnedAfter (cfg : WasmConfig) (store : Store NearState) (bytes : List UInt8) :
    HostStore NearState :=
  let before := inputBefore cfg store moduleInstance
  let paid := MeteredHosts.Output.paidStore before (applyCharges before.host (returnCharges cfg store)).1
  { paid with host := { paid.host with returnData := some bytes, returnedPromise := none } }

/-- Return-call evidence follows from the original register and return limit,
with both opcode and host gas paid and the caller's remaining credits intact. -/
theorem return_evidence (cfg : RuntimeConfig) (store : Store NearState)
    (bytes : List UInt8) (rest : Nat)
    (hmodule : store.modules[0]? = some moduleInstance)
    (hfn : store.funcs[3]? = some
      (.host (metered cfg.fees.numExtraBytesRecord "value_return" valueReturnFn).toHostFn))
    (hregister : store.host.registers 0 = some bytes)
    (hlimit : withinLimit store.host.config.maxReturnLen bytes.length = true)
    (hcredits : store.host.gas.Credits
      (cfg.wasm.regularOpCost + (returnCost cfg.wasm store + rest))) :
    CallEvidence cfg.wasm store 3 [.i64 u64Max, .i64 0] []
      (metered cfg.fees.numExtraBytesRecord "value_return" valueReturnFn)
      (returnedAfter cfg.wasm store bytes) (returnCost cfg.wasm store) rest := by
  let before := inputBefore cfg.wasm store moduleInstance
  have hc := Pays.chargeConfig (atCode store {} #[] saveFrame [] []) cfg.wasm.regularOpCost
    (returnCost cfg.wasm store + rest) hcredits
  have hi : before.host.gas.Credits
      (MeteredHosts.burnSum before.host.extCosts
        (chargesBefore "value_return" before [.i64 u64Max, .i64 0]) + rest) := hc.2.2.2.2
  have hread : getMemOrReg before 0 u64Max = some bytes := by
    simp only [getMemOrReg, ↓reduceIte]
    exact hregister
  obtain ⟨hinvoke, hburn, hpromises, hrest⟩ := MeteredHosts.Output.metered_valueReturn_credits
    cfg.fees.numExtraBytesRecord before u64Max 0 rest bytes hi hread hlimit
  refine ⟨hmodule, rfl, hfn, rfl, hinvoke, Nat.le_of_eq hburn, ?_, hrest⟩
  change (returnedAfter cfg.wasm store bytes).host.gas.burnt +
      (returnedAfter cfg.wasm store bytes).host.gas.promises ≤
    before.host.gas.burnt + before.host.gas.promises + returnCost cfg.wasm store
  change (returnedAfter cfg.wasm store bytes).host.gas.burnt =
    before.host.gas.burnt + returnCost cfg.wasm store at hburn
  change (returnedAfter cfg.wasm store bytes).host.gas.promises = before.host.gas.promises at hpromises
  omega

end WNear.Skeleton
