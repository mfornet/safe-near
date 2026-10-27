import NearVM.MeteredHosts.StorageRead

/-! Actual storage-read preparation under sufficient ordered burn credits. -/
namespace Wasm.Near.MeteredHosts.StorageRead
open StorageMetered
open _root_.Near.TrieOverlay
set_option maxRecDepth 16384

theorem valueCharges_burnsOnly (length : Nat) : ∀ c ∈ storageReadValueCharges length, BurnsOnly c := by
  by_cases h : length > 4000 <;> simp [storageReadValueCharges, h, BurnsOnly]

def nodePaid (before : HostStore NearState) (initial looked : State) :=
  (applyCharges (accounted before looked).host (trieCharges initial looked)).1
def hitPaid (before : HostStore NearState) (initial looked : State) (pointer : ValuePointer) :=
  (applyCharges (nodePaid before initial looked) (storageReadValueCharges pointer.reference.2.length)).1

theorem prepare_miss_credits (before : HostStore NearState) (keyLen keyPtr register : UInt64) (key : List UInt8)
    (initial looked : State) (rest : Nat)
    (ha : before.host.storageAccounting = some initial)
    (hk : getMemOrReg before keyPtr keyLen = some key)
    (hl : ∀ limit, before.host.config.maxStorageKeyLen = some limit → key.length ≤ limit)
    (hg : getReference initial (contractKey before.host.context.currentAccountId key)
      before.host.storageReadsFromTrie = .ok (looked, none))
    (hs : before.host.storage key = none)
    (hc : before.host.gas.Credits (burnSum before.host.extCosts (trieCharges initial looked) + rest))
    (hp : recordedStorageError before.host looked = none) :
    let result := prepared before (nodePaid before initial looked) looked
    prepareStorageCall "storage_read" before (args keyLen keyPtr register) = (result, none) ∧
    result.host.gas.burnt = before.host.gas.burnt + burnSum before.host.extCosts (trieCharges initial looked) ∧
    result.host.gas.Credits rest := by
  let paid := nodePaid before initial looked
  have c := applyCharges_credits (accounted before looked).host (trieCharges initial looked) rest (trieCharges_burnsOnly initial looked) hc
  have lim := applyCharges_gas_limits (accounted before looked).host (trieCharges initial looked)
  have ge := prepared_gas_eq before paid looked c.2.2.1 lim.1 lim.2
  refine ⟨prepare_miss before keyLen keyPtr register key initial looked paid ha hk hl hg hs (Prod.ext rfl c.1) ?_, c.2.1, ?_⟩
  · simpa only [paid, nodePaid] using (recordedStorageError_charges (accounted before looked) (trieCharges initial looked) looked (trieCharges_burnsOnly initial looked)).trans hp
  · rw [ge]; exact c.2.2.2.2

theorem prepare_hit_credits (before : HostStore NearState) (keyLen keyPtr register : UInt64) (key value : List UInt8)
    (initial looked fetched : State) (pointer : ValuePointer) (rest : Nat)
    (ha : before.host.storageAccounting = some initial)
    (hk : getMemOrReg before keyPtr keyLen = some key)
    (hl : ∀ limit, before.host.config.maxStorageKeyLen = some limit → key.length ≤ limit)
    (hg : getReference initial (contractKey before.host.context.currentAccountId key)
      before.host.storageReadsFromTrie = .ok (looked, some pointer))
    (hs : before.host.storage key = some value)
    (hd : dereference looked pointer = .ok (fetched, value))
    (hc : before.host.gas.Credits (burnSum before.host.extCosts (trieCharges initial looked) +
      (burnSum before.host.extCosts (storageReadValueCharges pointer.reference.2.length) + rest)))
    (hp : recordedStorageError before.host looked = none) :
    let result := prepared before (hitPaid before initial looked pointer) fetched
    prepareStorageCall "storage_read" before (args keyLen keyPtr register) = (result, none) ∧
    result.host.gas.burnt = before.host.gas.burnt + burnSum before.host.extCosts (trieCharges initial looked) +
      burnSum before.host.extCosts (storageReadValueCharges pointer.reference.2.length) ∧
    result.host.gas.Credits rest := by
  let npaid := nodePaid before initial looked
  let vpaid := hitPaid before initial looked pointer
  let values := storageReadValueCharges pointer.reference.2.length
  have nc := applyCharges_credits (accounted before looked).host (trieCharges initial looked)
    (burnSum before.host.extCosts values + rest) (trieCharges_burnsOnly initial looked) hc
  have ne : npaid.extCosts = before.host.extCosts := nc.2.2.2.1
  have vc := applyCharges_credits npaid values rest (valueCharges_burnsOnly pointer.reference.2.length)
    (by rw [ne]; exact nc.2.2.2.2)
  have nl := applyCharges_gas_limits (accounted before looked).host (trieCharges initial looked)
  have vl := applyCharges_gas_limits npaid values
  have ge := prepared_gas_eq before vpaid fetched (vc.2.2.1.trans nc.2.2.1) (vl.1.trans nl.1) (vl.2.trans nl.2)
  refine ⟨prepare_hit before keyLen keyPtr register key value initial looked fetched pointer npaid vpaid ha hk hl hg hs
    (Prod.ext rfl nc.1) ?_ (Prod.ext rfl vc.1) hd, ?_, ?_⟩
  · simpa only [npaid, nodePaid] using (recordedStorageError_charges (accounted before looked) (trieCharges initial looked) looked (trieCharges_burnsOnly initial looked)).trans hp
  · have vb : vpaid.gas.burnt = npaid.gas.burnt + burnSum npaid.extCosts values := vc.2.1
    have nb : npaid.gas.burnt = before.host.gas.burnt + burnSum before.host.extCosts (trieCharges initial looked) := nc.2.1
    change vpaid.gas.burnt = _
    rw [vb, nb, ne]
  · rw [ge]; exact vc.2.2.2.2

end Wasm.Near.MeteredHosts.StorageRead
