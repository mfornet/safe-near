import NearVM.MeteredHosts.StorageOverlay
import NearInterface.TrieEmpty

/-!
# Metered writes into a genuine empty trie base

The base entries are empty and neither overlay selects the written key.
Canonical construction fixes the empty base; the actual disk primitive then
returns absence without reading a witness or changing accounting. Overlays
may still contain unrelated entries.
-/
namespace Wasm.Near.MeteredHosts.StorageEmpty
open StorageMetered StorageOverlay
open _root_.Near.TrieOverlay

/-- Empty-base lookup incurs no node-accounting gas even if the accounting
snapshot already contains earlier work. -/
theorem trieCharges_self_cost (costs : ExtCosts) (trie : _root_.Near.TrieOverlay.State) :
    burnSum costs (trieCharges trie trie) = 0 := by
  simp [burnSum, burnCost, trieCharges]

/-- Empty base entries and no selected overlay cell imply raw absence. -/
theorem storage_none (before : HostStore NearState) (ctx : NearInterface.Context)
    (raw : NearInterface.RawStorage) (hwf : ctx.WF raw)
    (storage : List (List UInt8 × List UInt8)) (hs : storage.toFinset = raw)
    (hr : Represents before.host ctx storage) (key : List UInt8)
    (hentries : ctx.trie.entries = [])
    (hselected : selected ctx.trie (contractKey ctx.current.bytes key) = none) :
    before.host.storage key = none := by
  rw [hr.2, NearInterface.wf_storage_lookup ctx raw hwf storage hs key]
  rw [view_unselected ctx.trie _ hwf.trie_changes_unique hselected, hentries]
  rfl

/-- Actual empty-base write with sufficient credits and exact gas and usage. -/
theorem prepare_empty_credits (before : HostStore NearState)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (hwf : ctx.WF raw)
    (storage : List (List UInt8 × List UInt8)) (hs : storage.toFinset = raw)
    (hr : Represents before.host ctx storage)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : List UInt8) (rest : Nat)
    (haccounting : before.host.storageAccounting = some ctx.trie)
    (hkey : getMemOrReg before keyPtr keyLen = some key)
    (hkeyLimit : ∀ limit, before.host.config.maxStorageKeyLen = some limit → key.length ≤ limit)
    (hentries : ctx.trie.entries = [])
    (hselected : selected ctx.trie (contractKey ctx.current.bytes key) = none)
    (hcredits : before.host.gas.Credits
      (burnSum before.host.extCosts (trieCharges ctx.trie ctx.trie) + rest))
    (hvalue : getMemOrReg before valuePtr valueLen = some value)
    (hproof : recordedStorageError before.host
      (ctx.trie.set (contractKey before.host.context.currentAccountId key) value) = none) :
    let paid := (applyCharges (accounted before ctx.trie).host (trieCharges ctx.trie ctx.trie)).1
    let result := prepared before paid
      (ctx.trie.set (contractKey before.host.context.currentAccountId key) value)
    prepareStorageCall "storage_write" before (args keyLen keyPtr valueLen valuePtr) = (result, none) ∧
      result.host.gas.burnt = before.host.gas.burnt +
        burnSum before.host.extCosts (trieCharges ctx.trie ctx.trie) ∧
      result.host.gas.Credits rest := by
  apply prepare_fresh_credits before keyLen keyPtr valueLen valuePtr key value ctx.trie ctx.trie rest
    haccounting hkey hkeyLimit _ (storage_none before ctx raw hwf storage hs hr key hentries hselected)
    hcredits hvalue hproof
  rw [hr.1]
  exact getReference_empty_unselected ctx.trie (contractKey ctx.current.bytes key) true
    (base_empty_of_canonical ctx.trie hentries hwf.trie_canonical) hselected

/-- Actual empty-base write with sufficient credits and exact gas and usage. -/
theorem metered_empty_credits (extra : Nat) (before : HostStore NearState)
    (prePaid : NearState) (ctx : NearInterface.Context) (raw : NearInterface.RawStorage)
    (hwf : ctx.WF raw) (storage : List (List UInt8 × List UInt8))
    (hs : storage.toFinset = raw) (hr : Represents prePaid ctx storage)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : List UInt8) (rest : Nat)
    (hview : before.host.context.isView = false)
    (hpre : applyCharges before.host (chargesBefore "storage_write" before
      (args keyLen keyPtr valueLen valuePtr)) = (prePaid, none))
    (hpaidView : prePaid.context.isView = false)
    (haccounting : prePaid.storageAccounting = some ctx.trie)
    (hkey : getMemOrReg (Output.paidStore before prePaid) keyPtr keyLen = some key)
    (hvalue : getMemOrReg (Output.paidStore before prePaid) valuePtr valueLen = some value)
    (hkeyLimit : withinLimit prePaid.config.maxStorageKeyLen key.length = true)
    (hvalueLimit : withinLimit prePaid.config.maxStorageValueLen value.length = true)
    (hentries : ctx.trie.entries = [])
    (hselected : selected ctx.trie (contractKey ctx.current.bytes key) = none)
    (hcredits : prePaid.gas.Credits (burnSum prePaid.extCosts (trieCharges ctx.trie ctx.trie) +
        (burnSum prePaid.extCosts (postCharges (Output.paidStore before prePaid) key) + rest)))
    (hproof : recordedStorageError prePaid
      (ctx.trie.set (contractKey prePaid.context.currentAccountId key) value) = none) :
    let phasePaid := (applyCharges (accounted (Output.paidStore before prePaid) ctx.trie).host
      (trieCharges ctx.trie ctx.trie)).1
    let trie := ctx.trie.set (contractKey prePaid.context.currentAccountId key) value
    let phase := prepared (Output.paidStore before prePaid) phasePaid trie
    let paid := (applyCharges (written phase key value).host (postCharges phase key)).1
    let result := finished extra phase keyLen keyPtr valueLen valuePtr key value paid
    (metered extra "storage_write" storageWriteFn).invoke before (args keyLen keyPtr valueLen valuePtr) =
      .Return [.i64 (if (prePaid.storage key).isSome then 1 else 0)] result ∧
      result.host.gas.burnt = prePaid.gas.burnt + burnSum prePaid.extCosts (trieCharges ctx.trie ctx.trie) +
        burnSum prePaid.extCosts (postCharges (Output.paidStore before prePaid) key) ∧
      result.host.gas.Credits rest ∧
      result.host.context.storageUsage = UInt64.ofNat (writeUsage extra phase key value) ∧
      result.host.gas.promises = prePaid.gas.promises := by
  let phasePaid := (applyCharges (accounted (Output.paidStore before prePaid) ctx.trie).host
    (trieCharges ctx.trie ctx.trie)).1
  let trie := ctx.trie.set (contractKey prePaid.context.currentAccountId key) value
  let phase := prepared (Output.paidStore before prePaid) phasePaid trie
  have hlim : ∀ limit, prePaid.config.maxStorageKeyLen = some limit → key.length ≤ limit := by
    intro limit hl
    simpa [withinLimit, hl] using hkeyLimit
  have hp := prepare_empty_credits (Output.paidStore before prePaid) ctx raw hwf storage hs hr
    keyLen keyPtr valueLen valuePtr key value
    (burnSum prePaid.extCosts (postCharges (Output.paidStore before prePaid) key) + rest)
    haccounting hkey hlim hentries hselected hcredits hvalue hproof
  have hm := metered_discard_credits extra before keyLen keyPtr valueLen valuePtr key value
    prePaid _ _ rest hview hpre hpaidView hkey hvalue hkeyLimit hvalueLimit hp.1 hp.2.2
  refine ⟨hm.1, ?_, hm.2.2.1, hm.2.2.2, ?_⟩
  · exact hm.2.1.trans (congrArg (fun n => n +
    burnSum prePaid.extCosts (postCharges (Output.paidStore before prePaid) key)) hp.2.1)
  · rw [finished_gas]
    exact (applyCharges_credits (written phase key value).host (postCharges phase key) rest (postCharges_burnsOnly phase key) hp.2.2).2.2.1

/-- Actual empty-base write with sufficient credits and exact gas and usage. -/
theorem metered_empty_sufficient (extra : Nat) (before : HostStore NearState)
    (prePaid : NearState) (ctx : NearInterface.Context) (raw : NearInterface.RawStorage)
    (hwf : ctx.WF raw) (storage : List (List UInt8 × List UInt8))
    (hs : storage.toFinset = raw) (hr : Represents prePaid ctx storage)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : List UInt8) (rest : Nat)
    (hview : before.host.context.isView = false)
    (hcomputed : prePaid = (applyCharges before.host (chargesBefore "storage_write" before
      (args keyLen keyPtr valueLen valuePtr))).1)
    (hpaidView : prePaid.context.isView = false)
    (haccounting : prePaid.storageAccounting = some ctx.trie)
    (hkey : getMemOrReg (Output.paidStore before prePaid) keyPtr keyLen = some key)
    (hvalue : getMemOrReg (Output.paidStore before prePaid) valuePtr valueLen = some value)
    (hkeyLimit : withinLimit prePaid.config.maxStorageKeyLen key.length = true)
    (hvalueLimit : withinLimit prePaid.config.maxStorageValueLen value.length = true)
    (hentries : ctx.trie.entries = [])
    (hselected : selected ctx.trie (contractKey ctx.current.bytes key) = none)
    (hcredits : before.host.gas.Credits
      (burnSum before.host.extCosts (chargesBefore "storage_write" before
        (args keyLen keyPtr valueLen valuePtr)) + (burnSum before.host.extCosts (trieCharges ctx.trie ctx.trie) +
        (burnSum before.host.extCosts (postCharges (Output.paidStore before prePaid) key) + rest))))
    (hproof : recordedStorageError prePaid
      (ctx.trie.set (contractKey prePaid.context.currentAccountId key) value) = none) :
    let phasePaid := (applyCharges (accounted (Output.paidStore before prePaid) ctx.trie).host
      (trieCharges ctx.trie ctx.trie)).1
    let trie := ctx.trie.set (contractKey prePaid.context.currentAccountId key) value
    let phase := prepared (Output.paidStore before prePaid) phasePaid trie
    let paid := (applyCharges (written phase key value).host (postCharges phase key)).1
    let result := finished extra phase keyLen keyPtr valueLen valuePtr key value paid
    (metered extra "storage_write" storageWriteFn).invoke before (args keyLen keyPtr valueLen valuePtr) =
      .Return [.i64 (if (prePaid.storage key).isSome then 1 else 0)] result ∧
      result.host.gas.burnt = before.host.gas.burnt +
        burnSum before.host.extCosts (chargesBefore "storage_write" before
          (args keyLen keyPtr valueLen valuePtr)) + burnSum prePaid.extCosts (trieCharges ctx.trie ctx.trie) +
        burnSum prePaid.extCosts (postCharges (Output.paidStore before prePaid) key) ∧
      result.host.gas.Credits rest ∧
      result.host.context.storageUsage = UInt64.ofNat (writeUsage extra phase key value) ∧
      result.host.gas.promises = before.host.gas.promises := by
  have hc := applyCharges_credits before.host
    (chargesBefore "storage_write" before (args keyLen keyPtr valueLen valuePtr))
    (burnSum before.host.extCosts (trieCharges ctx.trie ctx.trie) +
        (burnSum before.host.extCosts (postCharges (Output.paidStore before prePaid) key) + rest)) (preCharges_burnsOnly before keyLen keyPtr valueLen valuePtr) hcredits
  have hpre : applyCharges before.host (chargesBefore "storage_write" before
      (args keyLen keyPtr valueLen valuePtr)) = (prePaid, none) := by
    rw [hcomputed]
    exact Prod.ext rfl hc.1
  have hext : prePaid.extCosts = before.host.extCosts := by
    rw [hcomputed]
    exact hc.2.2.2.1
  have hrest : prePaid.gas.Credits (burnSum prePaid.extCosts (trieCharges ctx.trie ctx.trie) +
        (burnSum prePaid.extCosts (postCharges (Output.paidStore before prePaid) key) + rest)) := by
    rw [hext]
    simpa only [← hcomputed] using hc.2.2.2.2
  have hm := metered_empty_credits extra before prePaid ctx raw hwf storage hs hr
    keyLen keyPtr valueLen valuePtr key value rest hview hpre hpaidView haccounting
    hkey hvalue hkeyLimit hvalueLimit hentries hselected hrest hproof
  refine ⟨hm.1, ?_, hm.2.2.1, hm.2.2.2.1, ?_⟩
  · have hburn : prePaid.gas.burnt = before.host.gas.burnt +
        burnSum before.host.extCosts (chargesBefore "storage_write" before
          (args keyLen keyPtr valueLen valuePtr)) := by
      rw [hcomputed]
      exact hc.2.1
    exact hm.2.1.trans (by rw [hburn])
  · exact hm.2.2.2.2.trans (by simpa only [← hcomputed] using hc.2.2.1)

end Wasm.Near.MeteredHosts.StorageEmpty
