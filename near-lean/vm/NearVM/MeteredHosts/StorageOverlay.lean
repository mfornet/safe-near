import NearVM.MeteredHosts.StorageMetered
import NearInterface.TrieOverlayStorage

/-!
# Storage writes through overlay references

These contracts discharge the trie-reference and dereference obligations of
`StorageMetered` for selected memory values and tombstones. Raw storage agrees
through `Context.WF`, rather than an assumed result of a complete host call.
Canonical disk references remain outside this layer.
-/
namespace Wasm.Near.MeteredHosts.StorageOverlay
open StorageMetered
open _root_.Near.TrieOverlay

/-- A host's storage function represents the same finite records as the action
boundary. This representation premise permits repeated identical list cells. -/
def Represents (host : NearState) (ctx : NearInterface.Context)
    (storage : List (List UInt8 × List UInt8)) : Prop :=
  host.context.currentAccountId = ctx.current.bytes ∧
  ∀ key, host.storage key = Lookup.first storage key

theorem storage_none (before : HostStore NearState) (ctx : NearInterface.Context)
    (raw : NearInterface.RawStorage) (hwf : ctx.WF raw)
    (storage : List (List UInt8 × List UInt8)) (hs : storage.toFinset = raw)
    (hr : Represents before.host ctx storage) (key : List UInt8)
    (hselected : selected ctx.trie (contractKey ctx.current.bytes key) = some none) :
    before.host.storage key = none := by
  rw [hr.2]
  exact (NearInterface.wf_selected_tombstone ctx raw hwf storage hs key true hselected).2.1

theorem storage_some (before : HostStore NearState) (ctx : NearInterface.Context)
    (raw : NearInterface.RawStorage) (hwf : ctx.WF raw)
    (storage : List (List UInt8 × List UInt8)) (hs : storage.toFinset = raw)
    (hr : Represents before.host ctx storage) (key old : List UInt8)
    (hselected : selected ctx.trie (contractKey ctx.current.bytes key) = some (some old)) :
    before.host.storage key = some old := by
  rw [hr.2]
  exact (NearInterface.wf_selected_value ctx raw hwf storage hs key old true hselected).2.1

/-- Tombstones bypass disk lookup. The two zero-node charge operations are
still the actual runtime phase, and its exact cost remains explicit. -/
theorem prepare_tombstone_credits (before : HostStore NearState)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (hwf : ctx.WF raw)
    (storage : List (List UInt8 × List UInt8)) (hs : storage.toFinset = raw)
    (hr : Represents before.host ctx storage)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value : List UInt8) (rest : Nat)
    (haccounting : before.host.storageAccounting = some ctx.trie)
    (hkey : getMemOrReg before keyPtr keyLen = some key)
    (hkeyLimit : ∀ limit, before.host.config.maxStorageKeyLen = some limit → key.length ≤ limit)
    (hselected : selected ctx.trie (contractKey ctx.current.bytes key) = some none)
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
    haccounting hkey hkeyLimit _ (storage_none before ctx raw hwf storage hs hr key hselected)
    hcredits hvalue hproof
  rw [hr.1]
  exact (getReference_selected_tombstone ctx.trie (contractKey ctx.current.bytes key) true
    hwf.trie_changes_unique hselected).1

/-- Memory references dereference to their exact raw bytes with no disk-node
accounting change. The old-value byte charge is retained even for discard. -/
theorem prepare_memory_credits (before : HostStore NearState)
    (ctx : NearInterface.Context) (raw : NearInterface.RawStorage) (hwf : ctx.WF raw)
    (storage : List (List UInt8 × List UInt8)) (hs : storage.toFinset = raw)
    (hr : Represents before.host ctx storage)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value old : List UInt8) (rest : Nat)
    (haccounting : before.host.storageAccounting = some ctx.trie)
    (hkey : getMemOrReg before keyPtr keyLen = some key)
    (hkeyLimit : ∀ limit, before.host.config.maxStorageKeyLen = some limit → key.length ≤ limit)
    (hselected : selected ctx.trie (contractKey ctx.current.bytes key) = some (some old))
    (hcredits : before.host.gas.Credits
      (burnSum before.host.extCosts (evictedCharges (.memory old)) +
        (burnSum before.host.extCosts (trieCharges ctx.trie ctx.trie) + rest)))
    (hvalue : getMemOrReg before valuePtr valueLen = some value)
    (hproof : recordedStorageError before.host
      (ctx.trie.set (contractKey before.host.context.currentAccountId key) value) = none) :
    let valuePaid := (applyCharges (accounted before ctx.trie).host (evictedCharges (.memory old))).1
    let mid := accounted { before with host := valuePaid } ctx.trie
    let paid := (applyCharges mid.host (trieCharges ctx.trie ctx.trie)).1
    let result := prepared before paid
      (ctx.trie.set (contractKey before.host.context.currentAccountId key) value)
    prepareStorageCall "storage_write" before (args keyLen keyPtr valueLen valuePtr) = (result, none) ∧
      result.host.gas.burnt = before.host.gas.burnt +
        (burnSum before.host.extCosts (evictedCharges (.memory old)) +
          burnSum before.host.extCosts (trieCharges ctx.trie ctx.trie)) ∧
      result.host.gas.Credits rest := by
  apply prepare_replace_credits before keyLen keyPtr valueLen valuePtr key value old
    ctx.trie ctx.trie ctx.trie (.memory old) rest haccounting hkey hkeyLimit _
    (storage_some before ctx raw hwf storage hs hr key old hselected)
    (dereference_memory ctx.trie old) hcredits hvalue hproof
  rw [hr.1]
  exact (getReference_selected_value ctx.trie (contractKey ctx.current.bytes key) true
    hwf.trie_changes_unique old hselected).1


/-- Every storage-write pre-call plan consists entirely of burn charges,
including the validation-failure prefixes. -/
theorem preCharges_burnsOnly (before : HostStore NearState)
    (keyLen keyPtr valueLen valuePtr : UInt64) :
    ∀ charge ∈ chargesBefore "storage_write" before (args keyLen keyPtr valueLen valuePtr),
      BurnsOnly charge := by
  have hread (len ptr : UInt64) : ∀ charge ∈ readSpan before len ptr, BurnsOnly charge := by
    unfold readSpan
    split
    · cases before.host.registers ptr.toNat <;> simp [BurnsOnly]
    · simp [BurnsOnly]
  have hvalue (key : List UInt8) :
      ∀ charge ∈ storageValueCharges before "storage_write_evicted_byte" key, BurnsOnly charge := by
    unfold storageValueCharges
    split
    · cases before.host.storage key <;> simp [BurnsOnly]
    · simp
  have hplan : ∃ plan, storageMutationPlan? "storage_write" before
      (args keyLen keyPtr valueLen valuePtr) = some plan ∧
      ∀ charge ∈ plan.charges, BurnsOnly charge := by
    unfold storageMutationPlan?
    simp only [show ("storage_write" != "storage_write" && "storage_write" != "storage_remove") = false by decide,
      Bool.false_eq_true, ↓reduceIte]
    simp only [show ("storage_write" == "storage_write") = true by decide, ↓reduceIte]
    repeat' split
    all_goals refine ⟨_, rfl, ?_⟩
    all_goals
      simp only [List.forall_mem_append, List.forall_mem_cons]
      repeat' apply And.intro
      all_goals first | exact List.forall_mem_nil _ | trivial | apply hread | apply hvalue
  obtain ⟨plan, hp, hb⟩ := hplan
  simpa only [chargesBefore, hp] using hb

/-- Complete metered discard write for an overlay tombstone. The credit
reservation pays the trie phase and actual post-call register bill. -/
theorem metered_tombstone_credits (extra : Nat) (before : HostStore NearState)
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
    (hselected : selected ctx.trie (contractKey ctx.current.bytes key) = some none)
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
  have hp := prepare_tombstone_credits (Output.paidStore before prePaid) ctx raw hwf storage hs hr
    keyLen keyPtr valueLen valuePtr key value
    (burnSum prePaid.extCosts (postCharges (Output.paidStore before prePaid) key) + rest)
    haccounting hkey hlim hselected hcredits hvalue hproof
  have hm := metered_discard_credits extra before keyLen keyPtr valueLen valuePtr key value
    prePaid _ _ rest hview hpre hpaidView hkey hvalue hkeyLimit hvalueLimit hp.1 hp.2.2
  refine ⟨hm.1, ?_, hm.2.2.1, hm.2.2.2, ?_⟩
  · exact hm.2.1.trans (congrArg (fun n => n +
    burnSum prePaid.extCosts (postCharges (Output.paidStore before prePaid) key)) hp.2.1)
  · rw [finished_gas]
    exact (applyCharges_credits (written phase key value).host (postCharges phase key) rest (postCharges_burnsOnly phase key) hp.2.2).2.2.1

/-- Complete metered discard write for an overlay memory. The credit
reservation pays the trie phase and actual post-call register bill. -/
theorem metered_memory_credits (extra : Nat) (before : HostStore NearState)
    (prePaid : NearState) (ctx : NearInterface.Context) (raw : NearInterface.RawStorage)
    (hwf : ctx.WF raw) (storage : List (List UInt8 × List UInt8))
    (hs : storage.toFinset = raw) (hr : Represents prePaid ctx storage)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value old : List UInt8) (rest : Nat)
    (hview : before.host.context.isView = false)
    (hpre : applyCharges before.host (chargesBefore "storage_write" before
      (args keyLen keyPtr valueLen valuePtr)) = (prePaid, none))
    (hpaidView : prePaid.context.isView = false)
    (haccounting : prePaid.storageAccounting = some ctx.trie)
    (hkey : getMemOrReg (Output.paidStore before prePaid) keyPtr keyLen = some key)
    (hvalue : getMemOrReg (Output.paidStore before prePaid) valuePtr valueLen = some value)
    (hkeyLimit : withinLimit prePaid.config.maxStorageKeyLen key.length = true)
    (hvalueLimit : withinLimit prePaid.config.maxStorageValueLen value.length = true)
    (hselected : selected ctx.trie (contractKey ctx.current.bytes key) = some (some old))
    (hcredits : prePaid.gas.Credits (burnSum prePaid.extCosts (evictedCharges (.memory old)) +
        (burnSum prePaid.extCosts (trieCharges ctx.trie ctx.trie) +
          (burnSum prePaid.extCosts (postCharges (Output.paidStore before prePaid) key) + rest))))
    (hproof : recordedStorageError prePaid
      (ctx.trie.set (contractKey prePaid.context.currentAccountId key) value) = none) :
    let valuePaid := (applyCharges (accounted (Output.paidStore before prePaid) ctx.trie).host
      (evictedCharges (.memory old))).1
    let mid := accounted { Output.paidStore before prePaid with host := valuePaid } ctx.trie
    let phasePaid := (applyCharges mid.host (trieCharges ctx.trie ctx.trie)).1
    let trie := ctx.trie.set (contractKey prePaid.context.currentAccountId key) value
    let phase := prepared (Output.paidStore before prePaid) phasePaid trie
    let paid := (applyCharges (written phase key value).host (postCharges phase key)).1
    let result := finished extra phase keyLen keyPtr valueLen valuePtr key value paid
    (metered extra "storage_write" storageWriteFn).invoke before (args keyLen keyPtr valueLen valuePtr) =
      .Return [.i64 (if (prePaid.storage key).isSome then 1 else 0)] result ∧
      result.host.gas.burnt = prePaid.gas.burnt + (burnSum prePaid.extCosts (evictedCharges (.memory old)) +
        burnSum prePaid.extCosts (trieCharges ctx.trie ctx.trie)) +
        burnSum prePaid.extCosts (postCharges (Output.paidStore before prePaid) key) ∧
      result.host.gas.Credits rest ∧
      result.host.context.storageUsage = UInt64.ofNat (writeUsage extra phase key value) ∧
      result.host.gas.promises = prePaid.gas.promises := by
  let valuePaid := (applyCharges (accounted (Output.paidStore before prePaid) ctx.trie).host
    (evictedCharges (.memory old))).1
  let mid := accounted { Output.paidStore before prePaid with host := valuePaid } ctx.trie
  let phasePaid := (applyCharges mid.host (trieCharges ctx.trie ctx.trie)).1
  let trie := ctx.trie.set (contractKey prePaid.context.currentAccountId key) value
  let phase := prepared (Output.paidStore before prePaid) phasePaid trie
  have hlim : ∀ limit, prePaid.config.maxStorageKeyLen = some limit → key.length ≤ limit := by
    intro limit hl
    simpa [withinLimit, hl] using hkeyLimit
  have hp := prepare_memory_credits (Output.paidStore before prePaid) ctx raw hwf storage hs hr
    keyLen keyPtr valueLen valuePtr key value old
    (burnSum prePaid.extCosts (postCharges (Output.paidStore before prePaid) key) + rest)
    haccounting hkey hlim hselected hcredits hvalue hproof
  have hm := metered_discard_credits extra before keyLen keyPtr valueLen valuePtr key value
    prePaid _ _ rest hview hpre hpaidView hkey hvalue hkeyLimit hvalueLimit hp.1 hp.2.2
  refine ⟨hm.1, ?_, hm.2.2.1, hm.2.2.2, ?_⟩
  · exact hm.2.1.trans (congrArg (fun n => n +
    burnSum prePaid.extCosts (postCharges (Output.paidStore before prePaid) key)) hp.2.1)

  · rw [finished_gas]
    exact (applyCharges_credits (written phase key value).host (postCharges phase key) rest (postCharges_burnsOnly phase key) hp.2.2).2.2.1

/-- Sufficient initial credits discharge the real pre-call bill as well as
the overlay phase and post-call bill; the prepayment is a computed state. -/
theorem metered_tombstone_sufficient (extra : Nat) (before : HostStore NearState)
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
    (hselected : selected ctx.trie (contractKey ctx.current.bytes key) = some none)
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
  have hm := metered_tombstone_credits extra before prePaid ctx raw hwf storage hs hr
    keyLen keyPtr valueLen valuePtr key value rest hview hpre hpaidView haccounting
    hkey hvalue hkeyLimit hvalueLimit hselected hrest hproof
  refine ⟨hm.1, ?_, hm.2.2.1, hm.2.2.2.1, ?_⟩
  · have hburn : prePaid.gas.burnt = before.host.gas.burnt +
        burnSum before.host.extCosts (chargesBefore "storage_write" before
          (args keyLen keyPtr valueLen valuePtr)) := by
      rw [hcomputed]
      exact hc.2.1
    exact hm.2.1.trans (by rw [hburn])
  · exact hm.2.2.2.2.trans (by simpa only [← hcomputed] using hc.2.2.1)

/-- Sufficient initial credits discharge the real pre-call bill as well as
the overlay phase and post-call bill; the prepayment is a computed state. -/
theorem metered_memory_sufficient (extra : Nat) (before : HostStore NearState)
    (prePaid : NearState) (ctx : NearInterface.Context) (raw : NearInterface.RawStorage)
    (hwf : ctx.WF raw) (storage : List (List UInt8 × List UInt8))
    (hs : storage.toFinset = raw) (hr : Represents prePaid ctx storage)
    (keyLen keyPtr valueLen valuePtr : UInt64) (key value old : List UInt8) (rest : Nat)
    (hview : before.host.context.isView = false)
    (hcomputed : prePaid = (applyCharges before.host (chargesBefore "storage_write" before
      (args keyLen keyPtr valueLen valuePtr))).1)
    (hpaidView : prePaid.context.isView = false)
    (haccounting : prePaid.storageAccounting = some ctx.trie)
    (hkey : getMemOrReg (Output.paidStore before prePaid) keyPtr keyLen = some key)
    (hvalue : getMemOrReg (Output.paidStore before prePaid) valuePtr valueLen = some value)
    (hkeyLimit : withinLimit prePaid.config.maxStorageKeyLen key.length = true)
    (hvalueLimit : withinLimit prePaid.config.maxStorageValueLen value.length = true)
    (hselected : selected ctx.trie (contractKey ctx.current.bytes key) = some (some old))
    (hcredits : before.host.gas.Credits
      (burnSum before.host.extCosts (chargesBefore "storage_write" before
        (args keyLen keyPtr valueLen valuePtr)) + (burnSum before.host.extCosts (evictedCharges (.memory old)) +
        (burnSum before.host.extCosts (trieCharges ctx.trie ctx.trie) +
          (burnSum before.host.extCosts (postCharges (Output.paidStore before prePaid) key) + rest)))))
    (hproof : recordedStorageError prePaid
      (ctx.trie.set (contractKey prePaid.context.currentAccountId key) value) = none) :
    let valuePaid := (applyCharges (accounted (Output.paidStore before prePaid) ctx.trie).host
      (evictedCharges (.memory old))).1
    let mid := accounted { Output.paidStore before prePaid with host := valuePaid } ctx.trie
    let phasePaid := (applyCharges mid.host (trieCharges ctx.trie ctx.trie)).1
    let trie := ctx.trie.set (contractKey prePaid.context.currentAccountId key) value
    let phase := prepared (Output.paidStore before prePaid) phasePaid trie
    let paid := (applyCharges (written phase key value).host (postCharges phase key)).1
    let result := finished extra phase keyLen keyPtr valueLen valuePtr key value paid
    (metered extra "storage_write" storageWriteFn).invoke before (args keyLen keyPtr valueLen valuePtr) =
      .Return [.i64 (if (prePaid.storage key).isSome then 1 else 0)] result ∧
      result.host.gas.burnt = before.host.gas.burnt +
        burnSum before.host.extCosts (chargesBefore "storage_write" before
          (args keyLen keyPtr valueLen valuePtr)) + (burnSum prePaid.extCosts (evictedCharges (.memory old)) +
        burnSum prePaid.extCosts (trieCharges ctx.trie ctx.trie)) +
        burnSum prePaid.extCosts (postCharges (Output.paidStore before prePaid) key) ∧
      result.host.gas.Credits rest ∧
      result.host.context.storageUsage = UInt64.ofNat (writeUsage extra phase key value) ∧
      result.host.gas.promises = before.host.gas.promises := by
  have hc := applyCharges_credits before.host
    (chargesBefore "storage_write" before (args keyLen keyPtr valueLen valuePtr))
    (burnSum before.host.extCosts (evictedCharges (.memory old)) +
        (burnSum before.host.extCosts (trieCharges ctx.trie ctx.trie) +
          (burnSum before.host.extCosts (postCharges (Output.paidStore before prePaid) key) + rest))) (preCharges_burnsOnly before keyLen keyPtr valueLen valuePtr) hcredits
  have hpre : applyCharges before.host (chargesBefore "storage_write" before
      (args keyLen keyPtr valueLen valuePtr)) = (prePaid, none) := by
    rw [hcomputed]
    exact Prod.ext rfl hc.1
  have hext : prePaid.extCosts = before.host.extCosts := by
    rw [hcomputed]
    exact hc.2.2.2.1
  have hrest : prePaid.gas.Credits (burnSum prePaid.extCosts (evictedCharges (.memory old)) +
        (burnSum prePaid.extCosts (trieCharges ctx.trie ctx.trie) +
          (burnSum prePaid.extCosts (postCharges (Output.paidStore before prePaid) key) + rest))) := by
    rw [hext]
    simpa only [← hcomputed] using hc.2.2.2.2
  have hm := metered_memory_credits extra before prePaid ctx raw hwf storage hs hr
    keyLen keyPtr valueLen valuePtr key value old rest hview hpre hpaidView haccounting
    hkey hvalue hkeyLimit hvalueLimit hselected hrest hproof
  refine ⟨hm.1, ?_, hm.2.2.1, hm.2.2.2.1, ?_⟩
  · have hburn : prePaid.gas.burnt = before.host.gas.burnt +
        burnSum before.host.extCosts (chargesBefore "storage_write" before
          (args keyLen keyPtr valueLen valuePtr)) := by
      rw [hcomputed]
      exact hc.2.1
    exact hm.2.1.trans (by rw [hburn])
  · exact hm.2.2.2.2.trans (by simpa only [← hcomputed] using hc.2.2.1)

end Wasm.Near.MeteredHosts.StorageOverlay
