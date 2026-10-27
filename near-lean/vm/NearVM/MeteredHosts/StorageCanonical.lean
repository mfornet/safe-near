import NearVM.MeteredHosts.StorageOverlay
import NearInterface.TrieCanonicalLookup

/-! Actual canonical storage-write preparation for arbitrary overlay/base
selections. Ordered charges are computed from real reference operations;
canonical construction discharges their success, without lookup callbacks. -/
namespace Wasm.Near.MeteredHosts.StorageCanonical
open StorageMetered StorageOverlay
open _root_.Near.TrieOverlay
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384

/-- A successful actual lookup and optional old-value dereference. -/
inductive LookupPlan where
  | fresh (looked : State)
  | replace (looked : State) (pointer : ValuePointer) (fetched : State) (old : List UInt8)

namespace LookupPlan

def fetched : LookupPlan → State
  | .fresh looked => looked
  | .replace _ _ fetched _ => fetched

def old : LookupPlan → Option (List UInt8)
  | .fresh _ => none
  | .replace _ _ _ old => some old

/-- Actual charge order: evicted-reference bytes precede total node deltas. -/
def charges (initial : State) : LookupPlan → List Charge
  | .fresh looked => trieCharges initial looked
  | .replace _ pointer fetched _ => evictedCharges pointer ++ trieCharges initial fetched

def paid (before : HostStore NearState) (initial : State) : LookupPlan → NearState
  | .fresh looked => (applyCharges (accounted before looked).host (trieCharges initial looked)).1
  | .replace looked pointer fetched _ =>
    let valuePaid := (applyCharges (accounted before looked).host (evictedCharges pointer)).1
    let mid := accounted {before with host := valuePaid} fetched
    (applyCharges mid.host (trieCharges initial fetched)).1

def result (before : HostStore NearState) (initial : State) (key value : List UInt8) (p : LookupPlan) : HostStore NearState :=
  prepared before (p.paid before initial)
    (p.fetched.set (contractKey before.host.context.currentAccountId key) value)

def Valid (initial : State) (key : List UInt8) (original : Option (List UInt8)) : LookupPlan → Prop
  | .fresh looked => getReference initial key true = .ok (looked, none) ∧ original = none
  | .replace looked pointer fetched old =>
    getReference initial key true = .ok (looked, some pointer) ∧
      dereference looked pointer = .ok (fetched, old) ∧ original = some old

end LookupPlan

/-- Run only actual primitive reference operations, retaining their error. -/
def lookupPlan (initial : State) (key : List UInt8) : Except String LookupPlan := do
  let (looked, pointer) ← getReference initial key true
  match pointer with
  | none => return .fresh looked
  | some pointer =>
    let (fetched, old) ← dereference looked pointer
    return .replace looked pointer fetched old

/-- Total symbolic plan. The fallback is ruled out by `plan_valid` on a
canonical state; callers need not assume a successful primitive outcome. -/
def plan (initial : State) (key : List UInt8) : LookupPlan :=
  match lookupPlan initial key with
  | .ok p => p
  | .error _ => .fresh initial

/-- Host/raw agreement and WF identify the bytes observed by canonical lookup. -/
theorem storage_view (before : HostStore NearState) (ctx : NearInterface.Context)
    (raw : NearInterface.RawStorage) (hwf : ctx.WF raw)
    (storage : List (List UInt8 × List UInt8)) (hs : storage.toFinset = raw)
    (hr : Represents before.host ctx storage) (key : List UInt8) :
    before.host.storage key = Lookup.first ctx.trie.view (contractKey before.host.context.currentAccountId key) := by
  rw [hr.1, hr.2]
  exact NearInterface.wf_storage_lookup ctx raw hwf storage hs key

/-- Canonical construction, overlay uniqueness and nonzero real nodes derive
success of the complete actual lookup/dereference plan and raw-byte agreement. -/
theorem plan_valid (before : HostStore NearState) (ctx : NearInterface.Context)
    (raw : NearInterface.RawStorage) (hwf : ctx.WF raw)
    (storage : List (List UInt8 × List UInt8)) (hs : storage.toFinset = raw)
    (hr : Represents before.host ctx storage) (hnodes : ctx.trie.NonzeroNodes) (key : List UInt8) :
    let fullKey := contractKey before.host.context.currentAccountId key
    (plan ctx.trie fullKey).Valid ctx.trie fullKey (before.host.storage key) := by
  let fullKey := contractKey before.host.context.currentAccountId key
  have hread := canonical_read ctx.trie fullKey true hwf.trie_canonical hwf.trie_changes_unique hnodes
  have hstorage := storage_view before ctx raw hwf storage hs hr key
  change (plan ctx.trie fullKey).Valid ctx.trie fullKey (before.host.storage key)
  cases hv : Lookup.first ctx.trie.view fullKey with
  | none =>
    rw [hv] at hread
    obtain ⟨looked, hget, _⟩ := hread
    simp only [plan, lookupPlan, hget, bind, Except.bind, pure, Except.pure, LookupPlan.Valid]
    exact ⟨True.intro, hstorage.trans hv⟩
  | some old =>
    rw [hv] at hread
    obtain ⟨looked, pointer, fetched, hget, hfetch, _⟩ := hread
    simp only [plan, lookupPlan, hget, hfetch, bind, Except.bind, pure, Except.pure, LookupPlan.Valid]
    exact ⟨True.intro, True.intro, hstorage.trans hv⟩

/-- Every symbolic canonical write charge is an actual burn. -/
theorem charges_burnsOnly (initial : State) (p : LookupPlan) :
    ∀ c ∈ p.charges initial, BurnsOnly c := by
  cases p with
  | fresh looked => exact trieCharges_burnsOnly initial looked
  | replace looked pointer fetched old =>
    exact List.forall_mem_append.mpr ⟨evictedCharges_burnsOnly pointer, trieCharges_burnsOnly initial fetched⟩

/-- Full actual preparation on any canonical trie, with old-value bytes and
trie charges in their actual order. No getReference/dereference success
premise, selected-key restriction or complete host outcome is assumed. -/
theorem prepare_canonical_credits (before : HostStore NearState)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (hwf : ctx.WF raw)
    (storage : List (List UInt8 × List UInt8)) (hs : storage.toFinset = raw)
    (hr : Represents before.host ctx storage) (hnodes : ctx.trie.NonzeroNodes)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : List UInt8) (rest : Nat)
    (haccounting : before.host.storageAccounting = some ctx.trie)
    (hkey : getMemOrReg before keyPtr keyLen = some key)
    (hkeyLimit : ∀ limit, before.host.config.maxStorageKeyLen = some limit → key.length ≤ limit)
    (hcredits : before.host.gas.Credits
      (burnSum before.host.extCosts ((plan ctx.trie (contractKey before.host.context.currentAccountId key)).charges ctx.trie) + rest))
    (hvalue : getMemOrReg before valuePtr valueLen = some value)
    (hproof : recordedStorageError before.host
      ((plan ctx.trie (contractKey before.host.context.currentAccountId key)).fetched.set
        (contractKey before.host.context.currentAccountId key) value) = none) :
    let p := plan ctx.trie (contractKey before.host.context.currentAccountId key)
    let result := p.result before ctx.trie key value
    prepareStorageCall "storage_write" before (args keyLen keyPtr valueLen valuePtr) = (result, none) ∧
      result.host.gas.burnt = before.host.gas.burnt + burnSum before.host.extCosts (p.charges ctx.trie) ∧
      result.host.gas.Credits rest := by
  have hp := plan_valid before ctx raw hwf storage hs hr hnodes key
  dsimp only at hp ⊢
  generalize he : plan ctx.trie (contractKey before.host.context.currentAccountId key) = p at hp hcredits hproof ⊢
  cases p with
  | fresh looked =>
    exact prepare_fresh_credits before keyLen keyPtr valueLen valuePtr key value ctx.trie looked rest
      haccounting hkey hkeyLimit hp.1 hp.2 hcredits hvalue hproof
  | replace looked pointer fetched old =>
    have hc : before.host.gas.Credits (burnSum before.host.extCosts (evictedCharges pointer) +
        (burnSum before.host.extCosts (trieCharges ctx.trie fetched) + rest)) := by
      simpa only [LookupPlan.charges, burnSum, List.map_append, List.sum_append, Nat.add_assoc] using hcredits
    have h := prepare_replace_credits before keyLen keyPtr valueLen valuePtr key value old ctx.trie looked fetched pointer rest
      haccounting hkey hkeyLimit hp.1 hp.2.2 hp.2.1 hc hvalue hproof
    simpa only [LookupPlan.result, LookupPlan.paid, LookupPlan.fetched, LookupPlan.charges,
      burnSum, List.map_append, List.sum_append] using h


/-- Canonical assumptions rule out the total-plan fallback: the actual
reference operation sequence succeeds with precisely the symbolic plan. -/
theorem lookupPlan_ok (before : HostStore NearState) (ctx : NearInterface.Context)
    (raw : NearInterface.RawStorage) (hwf : ctx.WF raw)
    (storage : List (List UInt8 × List UInt8)) (hs : storage.toFinset = raw)
    (hr : Represents before.host ctx storage) (hnodes : ctx.trie.NonzeroNodes) (key : List UInt8) :
    lookupPlan ctx.trie (contractKey before.host.context.currentAccountId key) =
      .ok (plan ctx.trie (contractKey before.host.context.currentAccountId key)) := by
  have hp := plan_valid before ctx raw hwf storage hs hr hnodes key
  dsimp only at hp
  generalize he : plan ctx.trie (contractKey before.host.context.currentAccountId key) = p at hp ⊢
  cases p with
  | fresh looked => simp only [lookupPlan, hp.1, bind, Except.bind, pure, Except.pure]
  | replace looked pointer fetched old => simp only [lookupPlan, hp.1, hp.2.1, bind, Except.bind, pure, Except.pure]

/-- The complete metered discard-register write over arbitrary canonical
storage. The credits cover actual argument reads, canonical lookup/dereference
billing and evicted-register billing. All primitive successes are derived. -/
theorem metered_canonical_credits (extra : Nat) (before : HostStore NearState) (prePaid : NearState)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (hwf : ctx.WF raw)
    (storage : List (List UInt8 × List UInt8)) (hs : storage.toFinset = raw)
    (hr : Represents prePaid ctx storage) (hnodes : ctx.trie.NonzeroNodes)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : List UInt8) (rest : Nat)
    (hview : before.host.context.isView = false)
    (hcomputed : prePaid = (applyCharges before.host
      (chargesBefore "storage_write" before (args keyLen keyPtr valueLen valuePtr))).1)
    (haccounting : prePaid.storageAccounting = some ctx.trie)
    (hkey : getMemOrReg (Output.paidStore before prePaid) keyPtr keyLen = some key)
    (hvalue : getMemOrReg (Output.paidStore before prePaid) valuePtr valueLen = some value)
    (hkeyLimit : withinLimit prePaid.config.maxStorageKeyLen key.length = true)
    (hvalueLimit : withinLimit prePaid.config.maxStorageValueLen value.length = true)
    (hcredits : before.host.gas.Credits
      (burnSum before.host.extCosts (chargesBefore "storage_write" before (args keyLen keyPtr valueLen valuePtr)) +
        (burnSum before.host.extCosts ((plan ctx.trie (contractKey prePaid.context.currentAccountId key)).charges ctx.trie) +
          (burnSum before.host.extCosts (postCharges (Output.paidStore before prePaid) key) + rest))))
    (hproof : recordedStorageError prePaid
      ((plan ctx.trie (contractKey prePaid.context.currentAccountId key)).fetched.set
        (contractKey prePaid.context.currentAccountId key) value) = none) :
    let b := Output.paidStore before prePaid
    let p := plan ctx.trie (contractKey prePaid.context.currentAccountId key)
    let phase := p.result b ctx.trie key value
    let paid := (applyCharges (written phase key value).host (postCharges phase key)).1
    let result := finished extra phase keyLen keyPtr valueLen valuePtr key value paid
    (metered extra "storage_write" storageWriteFn).invoke before (args keyLen keyPtr valueLen valuePtr) =
      .Return [.i64 (if (prePaid.storage key).isSome then 1 else 0)] result ∧
      result.host.gas.burnt = before.host.gas.burnt +
        burnSum before.host.extCosts (chargesBefore "storage_write" before (args keyLen keyPtr valueLen valuePtr)) +
        burnSum prePaid.extCosts (p.charges ctx.trie) + burnSum prePaid.extCosts (postCharges b key) ∧
      result.host.gas.Credits rest ∧
      result.host.context.storageUsage = UInt64.ofNat (writeUsage extra phase key value) ∧
      result.host.gas.promises = before.host.gas.promises := by
  let b := Output.paidStore before prePaid
  let p := plan ctx.trie (contractKey prePaid.context.currentAccountId key)
  let phase := p.result b ctx.trie key value
  have hc := applyCharges_credits before.host
    (chargesBefore "storage_write" before (args keyLen keyPtr valueLen valuePtr))
    (burnSum before.host.extCosts (p.charges ctx.trie) +
      (burnSum before.host.extCosts (postCharges b key) + rest))
    (preCharges_burnsOnly before keyLen keyPtr valueLen valuePtr) hcredits
  have hpre : applyCharges before.host (chargesBefore "storage_write" before (args keyLen keyPtr valueLen valuePtr)) =
      (prePaid, none) := by
    rw [hcomputed]
    exact Prod.ext rfl hc.1
  have hext : prePaid.extCosts = before.host.extCosts := by
    rw [hcomputed]
    exact hc.2.2.2.1
  have hpcredit : prePaid.gas.Credits
      (burnSum prePaid.extCosts (p.charges ctx.trie) +
        (burnSum prePaid.extCosts (postCharges b key) + rest)) := by
    rw [hext, hcomputed]
    exact hc.2.2.2.2
  have hpaidView : prePaid.context.isView = false := by
    have hf := congrArg (fun ns : NearState => ns.context.isView)
      (applyCharges_frame before.host (chargesBefore "storage_write" before (args keyLen keyPtr valueLen valuePtr))
        (preCharges_burnsOnly before keyLen keyPtr valueLen valuePtr))
    rw [← hcomputed] at hf
    exact hf.trans hview
  have hrep : Represents b.host ctx storage := ⟨hr.1, hr.2⟩
  have hlim : ∀ limit, b.host.config.maxStorageKeyLen = some limit → key.length ≤ limit := by
    intro limit hl
    simpa [withinLimit, show prePaid.config.maxStorageKeyLen = some limit from hl] using hkeyLimit
  have hp := prepare_canonical_credits b ctx raw hwf storage hs hrep hnodes
    keyLen keyPtr valueLen valuePtr key value
    (burnSum prePaid.extCosts (postCharges b key) + rest) haccounting hkey hlim hpcredit hvalue hproof
  have hm := metered_discard_credits extra before keyLen keyPtr valueLen valuePtr key value prePaid
    (p.paid b ctx.trie) (p.fetched.set (contractKey prePaid.context.currentAccountId key) value) rest
    hview hpre hpaidView hkey hvalue hkeyLimit hvalueLimit hp.1 hp.2.2
  have hpost := applyCharges_credits (written phase key value).host (postCharges phase key) rest
    (postCharges_burnsOnly phase key) hp.2.2
  have hpromises : prePaid.gas.promises = before.host.gas.promises := by
    rw [hcomputed]
    exact hc.2.2.1
  refine ⟨hm.1, ?_, hm.2.2.1, hm.2.2.2, ?_⟩
  · have hphase : (p.paid b ctx.trie).gas.burnt = prePaid.gas.burnt + burnSum prePaid.extCosts (p.charges ctx.trie) := hp.2.1
    have hpaid : prePaid.gas.burnt = before.host.gas.burnt +
        burnSum before.host.extCosts (chargesBefore "storage_write" before (args keyLen keyPtr valueLen valuePtr)) := by
      rw [hcomputed]
      exact hc.2.1
    refine hm.2.1.trans ?_
    rw [hphase, hpaid]
    rfl
  · rw [finished_gas]
    exact hpost.2.2.1.trans hpromises

end Wasm.Near.MeteredHosts.StorageCanonical
