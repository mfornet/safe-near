import Skeleton.FunctionalInvariant
import NearVM.MeteredHosts.StorageCanonical

/-! Canonical primitive readiness for arbitrary paid gas budgets. -/
namespace WNear.Skeleton.CanonicalReady
open Wasm Wasm.Near MeteredLogic NearInterface MeteredHosts
open BudgetSimulation FunctionalInvariant
open StorageMetered StorageCanonical

/-- The original prepared memory supplies the method's concrete one-byte key,
independently of billing and register limits. -/
theorem prepared_key (ctx : Context) (raw : Storage) (before : HostStore NearState)
    (h : BeforeWrite ctx raw before) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages) :
    getMemOrReg before 0 1 = some "k".toUTF8.toList := by
  let reference := Output.paidStore (emptyBefore ctx raw) (emptyPaid ctx raw)
  have hmem : before.mem = reference.mem :=
    h.memory.trans (storageInput_memory ctx.protocol (Near.Boundary.toVMContext ctx) raw).symm
  calc
    getMemOrReg before 0 1 = getMemOrReg reference 0 1 := by
      simp only [getMemOrReg, show (1 : UInt64) ≠ u64Max by decide +kernel, ↓reduceIte, hmem]
    _ = some "k".toUTF8.toList := emptyPaid_key ctx raw hpages

/-- The recorded proof obligation follows the actual fetched canonical plan,
which includes its warmed cache and accounting state before the staged write. -/
def ProofAccepted (ctx : Context) (raw : Storage) : Prop :=
  recordedStorageError (origin ctx raw)
    ((plan ctx.trie (_root_.Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList)).fetched.set
      (_root_.Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) ctx.args) = none

/-- Canonical construction supplies fresh or replacement primitive readiness
at any actual paid functional state. No gas-credit hypothesis occurs here. -/
theorem canonical_ready (ctx : Context) (raw : Storage) (before : HostStore NearState)
    (h : BeforeWrite ctx raw before) (hregister : before.host.registers 0 = some ctx.args)
    (hwf : ctx.WF raw.toFinset) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hkey : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hnodes : ctx.trie.NonzeroNodes) (hproof : ProofAccepted ctx raw) :
    StorageMeteredBudget.Ready before 1 0 u64Max 0 := by
  let key := "k".toUTF8.toList
  let fullKey := _root_.Near.TrieOverlay.contractKey ctx.current.bytes key
  have hcurrent : before.host.context.currentAccountId = ctx.current.bytes := h.fields.current
  have hk := prepared_key ctx raw before h hpages
  have hv := plan_valid before ctx raw.toFinset hwf raw rfl h.represents hnodes key
  dsimp only at hv
  rw [hcurrent] at hv
  change (plan ctx.trie fullKey).Valid ctx.trie fullKey (before.host.storage key) at hv
  have hlimit : ∀ limit, before.host.config.maxStorageKeyLen = some limit → key.length ≤ limit := by
    intro limit hl
    rw [h.fields.config] at hl
    change some ctx.protocol.wasm.limits.maxLengthStorageKey = some limit at hl
    cases Option.some.inj hl
    simpa only [key, show "k".toUTF8.toList.length = 1 by decide +kernel] using hkey
  have hvalue : getMemOrReg before 0 u64Max = some ctx.args := by
    simp only [getMemOrReg, ↓reduceIte, UInt64.toNat_zero, hregister]
  change recordedStorageError (origin ctx raw) ((plan ctx.trie fullKey).fetched.set fullKey ctx.args) = none at hproof
  generalize hp : plan ctx.trie fullKey = p at hv hproof
  cases p with
  | fresh looked =>
    refine Or.inl ⟨key, ctx.args, ctx.trie, looked, h.fields.accounting, hk, hlimit, ?_, hv.2, hvalue, ?_⟩
    · rw [hcurrent]
      exact hv.1
    · rw [hcurrent]
      unfold recordedStorageError at hproof ⊢
      rw [h.fields.proof, h.fields.config]
      exact hproof
  | replace looked pointer fetched old =>
    refine Or.inr ⟨key, ctx.args, old, ctx.trie, looked, fetched, pointer, h.fields.accounting,
      hk, hlimit, ?_, hv.2.2, hv.2.1, hvalue, ?_⟩
    · rw [hcurrent]
      exact hv.1
    · rw [hcurrent]
      unfold recordedStorageError at hproof ⊢
      rw [h.fields.proof, h.fields.config]
      exact hproof

/-- The low paid state remains canonically ready even if the attempted bill
exhausted its gas. Readiness is needed only after actual key validation accepts,
so no original key-limit acceptance condition is imposed. -/
theorem storageReady_allKeyLimits (ctx : Context) (raw : Storage) (store : Store NearState)
    (h : StoreBeforeWrite ctx raw store) (hregister : store.host.registers 0 = some ctx.args)
    (hwf : ctx.WF raw.toFinset) (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hnodes : ctx.trie.NonzeroNodes) (hproof : ProofAccepted ctx raw) :
    StorageReady ctx.protocol store := by
  let before := MeteredHostBudget.hostView (chargedStore store ctx.protocol.wasm.regularOpCost) moduleInstance
  have hb : BeforeWrite ctx raw before := (h.charged ctx.protocol.wasm.regularOpCost).hostView
  have hp := hb.paid _ (StorageBudget.plan_burnsOnly before 1 0 u64Max 0)
  have hr : (StorageMeteredBudget.paid before 1 0 u64Max 0).host.registers 0 = some ctx.args := by
    have hf := congrArg (fun host : NearState => host.registers 0)
      (applyCharges_frame before.host _ (StorageBudget.plan_burnsOnly before 1 0 u64Max 0))
    exact hf.trans hregister
  intro hpre
  have hcfg : (StorageMeteredBudget.paid before 1 0 u64Max 0).host.config.maxStorageKeyLen =
      some ctx.protocol.wasm.limits.maxLengthStorageKey := congrArg NearConfig.maxStorageKeyLen hp.fields.config
  have hkey := preInvoke_key_bound _ (prepared_key ctx raw _ hp hpages) hpre _ hcfg
  exact canonical_ready ctx raw _ hp hr hwf hpages hkey hnodes hproof

end WNear.Skeleton.CanonicalReady
