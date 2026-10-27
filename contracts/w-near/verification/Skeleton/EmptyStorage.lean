import Skeleton.StorageResources
import Skeleton.Memory
import NearVM.MeteredHosts.StorageEmpty
import NearVM.MeteredHosts.StorageFrame
import NearVM.StorageRepresentation

/-!
# The walking method's storage frontier on an empty canonical base

The original boundary WF and the absence of an overlay selection discharge
all trie lookup obligations. The recorded-proof check remains explicit.
-/
namespace WNear.Skeleton
open Wasm Wasm.Near Wasm.Near.MeteredLogic
open MeteredHosts MeteredHosts.StorageMetered

set_option maxHeartbeats 800000

abbrev emptyBefore (ctx : NearInterface.Context) (raw : Storage) :=
  storageInput ctx.protocol (Near.Boundary.toVMContext ctx) raw

def emptyPreCharges (ctx : NearInterface.Context) (raw : Storage) : List Charge :=
  chargesBefore "storage_write" (emptyBefore ctx raw) (args 1 0 u64Max 0)

@[irreducible] def emptyPaid (ctx : NearInterface.Context) (raw : Storage) : NearState :=
  (applyCharges (emptyBefore ctx raw).host (emptyPreCharges ctx raw)).1

private theorem emptyPaid_fold (ctx : NearInterface.Context) (raw : Storage) :
    (applyCharges (emptyBefore ctx raw).host (emptyPreCharges ctx raw)).1 = emptyPaid ctx raw := by unfold emptyPaid; rfl

def emptyCost (ctx : NearInterface.Context) (raw : Storage) : Nat :=
  burnSum (emptyBefore ctx raw).host.extCosts (emptyPreCharges ctx raw)

@[irreducible] def emptyPhase (ctx : NearInterface.Context) (raw : Storage) : HostStore NearState :=
  let before := Output.paidStore (emptyBefore ctx raw) (emptyPaid ctx raw)
  let paid := (applyCharges (accounted before ctx.trie).host (trieCharges ctx.trie ctx.trie)).1
  prepared before paid (ctx.trie.set
    (Near.TrieOverlay.contractKey (emptyPaid ctx raw).context.currentAccountId "k".toUTF8.toList) ctx.args)

/-- Computed successful post-store of the metered write. Its definition does
not assume execution or gas success; `empty_invoke` proves when it is reached. -/
@[irreducible] def emptyAfter (ctx : NearInterface.Context) (raw : Storage) : HostStore NearState :=
  let phase := emptyPhase ctx raw
  let paid := (applyCharges (written phase "k".toUTF8.toList ctx.args).host
    (postCharges phase "k".toUTF8.toList)).1
  finished ctx.protocol.fees.numExtraBytesRecord phase 1 0 u64Max 0 "k".toUTF8.toList ctx.args paid

private theorem pre_burns (ctx : NearInterface.Context) (raw : Storage) :
    ∀ charge ∈ emptyPreCharges ctx raw, BurnsOnly charge :=
  StorageOverlay.preCharges_burnsOnly (emptyBefore ctx raw) 1 0 u64Max 0

/-- Prepayment preserves the resources used by the raw storage ABI. -/
theorem emptyPaid_frame (ctx : NearInterface.Context) (raw : Storage) :
    StorageFrame.Frame (emptyBefore ctx raw) (Output.paidStore (emptyBefore ctx raw) (emptyPaid ctx raw)) :=
by
  simpa only [emptyPaid] using StorageFrame.prepayment_frame (emptyBefore ctx raw) (emptyPreCharges ctx raw) (pre_burns ctx raw)

private theorem paid_functional (before : HostStore NearState) (charges : List Charge)
    (hburn : ∀ charge ∈ charges, BurnsOnly charge) :
    let paid := (applyCharges before.host charges).1
    (paid.context.currentAccountId = before.host.context.currentAccountId) ∧
    paid.storage = before.host.storage ∧ paid.storageAccounting = before.host.storageAccounting ∧
    paid.registers = before.host.registers ∧ paid.config = before.host.config := by
  have hf := applyCharges_frame before.host charges hburn
  have hcurrent := congrArg (fun ns : NearState => ns.context.currentAccountId) hf
  have hs := congrArg NearState.storage hf
  have ha := congrArg NearState.storageAccounting hf
  have hr := congrArg NearState.registers hf
  have hc := congrArg NearState.config hf
  exact ⟨hcurrent, hs, ha, hr, hc⟩

theorem emptyPaid_represents (ctx : NearInterface.Context) (raw : Storage) :
    StorageOverlay.Represents (emptyPaid ctx raw) ctx raw := by
  have hp := paid_functional (emptyBefore ctx raw) (emptyPreCharges ctx raw) (pre_burns ctx raw)
  dsimp only at hp
  rw [emptyPaid_fold] at hp
  have hr := storageInput_represents ctx raw
  change (emptyPaid ctx raw).context.currentAccountId = ctx.current.bytes ∧ _
  exact ⟨hp.1.trans hr.1, fun key => (congrFun hp.2.1 key).trans (hr.2 key)⟩

theorem emptyPaid_accounting (ctx : NearInterface.Context) (raw : Storage) :
    (emptyPaid ctx raw).storageAccounting = some ctx.trie := by
  have hp := paid_functional (emptyBefore ctx raw) (emptyPreCharges ctx raw) (pre_burns ctx raw)
  dsimp only at hp
  rw [emptyPaid_fold] at hp
  exact hp.2.2.1.trans (storageInput_accounting ctx.protocol (Near.Boundary.toVMContext ctx) raw)

theorem emptyPaid_register (ctx : NearInterface.Context) (raw : Storage) :
    (emptyPaid ctx raw).registers = (emptyBefore ctx raw).host.registers :=
by
  have hp := paid_functional (emptyBefore ctx raw) (emptyPreCharges ctx raw) (pre_burns ctx raw)
  dsimp only at hp
  rw [emptyPaid_fold] at hp
  exact hp.2.2.2.1

theorem emptyPaid_config (ctx : NearInterface.Context) (raw : Storage) :
    (emptyPaid ctx raw).config = (emptyBefore ctx raw).host.config :=
by
  have hp := paid_functional (emptyBefore ctx raw) (emptyPreCharges ctx raw) (pre_burns ctx raw)
  dsimp only at hp
  rw [emptyPaid_fold] at hp
  exact hp.2.2.2.2

theorem emptyBefore_isView (ctx : NearInterface.Context) (raw : Storage) :
    (emptyBefore ctx raw).host.context.isView = false := by
  exact storageInput_isView ctx.protocol (Near.Boundary.toVMContext ctx) raw

/-- The static key bytes are read from initialized memory, not a supplied
storage-read or whole-host-invocation premise. -/
theorem emptyPaid_key (ctx : NearInterface.Context) (raw : Storage)
    (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages) :
    getMemOrReg (Output.paidStore (emptyBefore ctx raw) (emptyPaid ctx raw)) 0 1 =
      some "k".toUTF8.toList := by
  have hm := storageInput_memory ctx.protocol (Near.Boundary.toVMContext ctx) raw
  have hs := (dataMemory_spec ctx.protocol.wasm.limits.initialMemoryPages
    (some ctx.protocol.wasm.limits.maxMemoryPages) hpages).2.1
  have hbound : ¬ (0 : UInt64).toNat + (1 : UInt64).toNat >
      (emptyBefore ctx raw).mem.size * 65536 := by
    rw [hm]
    change (dataMemory _ _).size * pageSize = _ at hs
    simp only [UInt64.toNat_zero, UInt64.toNat_one, Nat.zero_add]
    unfold preparedData
    change ¬ 1 > (dataMemory _ _).size * pageSize
    unfold pageSize at hs ⊢
    omega
  simp only [getMemOrReg, show (1 : UInt64) ≠ u64Max by decide +kernel, ↓reduceIte,
    Output.paidStore, hbound]
  rw [hm]
  exact congrArg some (dataMemory_key _ _ hpages)

/-- Input has installed the bytes in register zero for the sentinel ABI. -/
theorem emptyPaid_value (ctx : NearInterface.Context) (raw : Storage) :
    getMemOrReg (Output.paidStore (emptyBefore ctx raw) (emptyPaid ctx raw)) 0 u64Max = some ctx.args := by
  simp only [getMemOrReg, ↓reduceIte, Output.paidStore]
  rw [emptyPaid_register]
  exact storageInput_register ctx.protocol (Near.Boundary.toVMContext ctx) raw

private theorem paidStore_represents (before : HostStore NearState) (paid : NearState)
    (ctx : NearInterface.Context) (storage : Storage) (h : StorageOverlay.Represents paid ctx storage) :
    StorageOverlay.Represents (Output.paidStore before paid).host ctx storage := ⟨h.1, h.2⟩

private theorem paidStore_view (before : HostStore NearState) (paid : NearState) :
    (Output.paidStore before paid).host.context.isView = paid.context.isView := rfl

theorem emptyPaid_store_represents (ctx : NearInterface.Context) (raw : Storage) :
    StorageOverlay.Represents (Output.paidStore (emptyBefore ctx raw) (emptyPaid ctx raw)).host ctx raw :=
  paidStore_represents _ _ _ _ (emptyPaid_represents ctx raw)

/-- On a fresh key, no evicted register bytes are charged. -/
theorem empty_postCharges (ctx : NearInterface.Context) (storage : Storage)
    (raw : NearInterface.RawStorage) (hwf : ctx.WF raw) (hs : storage.toFinset = raw)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none) :
    postCharges (Output.paidStore (emptyBefore ctx storage) (emptyPaid ctx storage)) "k".toUTF8.toList = [] := by
  have hn := StorageEmpty.storage_none (Output.paidStore (emptyBefore ctx storage) (emptyPaid ctx storage))
    ctx raw hwf storage hs (emptyPaid_store_represents ctx storage) "k".toUTF8.toList hentries hselected
  simp only [postCharges, hn]

/-- Empty-base instantiation of the actual full host wrapper. All lookup,
value reads, cost equations, and residual credits are derived locally. -/
theorem empty_invoke (ctx : NearInterface.Context) (storage : Storage)
    (raw : NearInterface.RawStorage) (rest : Nat)
    (hwf : ctx.WF raw) (hs : storage.toFinset = raw)
    (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hkeyLimit : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalueLimit : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hcredits : (emptyBefore ctx storage).host.gas.Credits (emptyCost ctx storage + rest))
    (hproof : recordedStorageError (emptyPaid ctx storage)
      (ctx.trie.set (Near.TrieOverlay.contractKey (emptyPaid ctx storage).context.currentAccountId
        "k".toUTF8.toList) ctx.args) = none) :
    (metered ctx.protocol.fees.numExtraBytesRecord "storage_write" storageWriteFn).invoke
        (emptyBefore ctx storage) (args 1 0 u64Max 0) =
      .Return [.i64 0] (emptyAfter ctx storage) ∧
    (emptyAfter ctx storage).host.gas.burnt = (emptyBefore ctx storage).host.gas.burnt + emptyCost ctx storage ∧
    (emptyAfter ctx storage).host.gas.Credits rest ∧
    (emptyAfter ctx storage).host.context.storageUsage = UInt64.ofNat
      (writeUsage ctx.protocol.fees.numExtraBytesRecord (emptyPhase ctx storage) "k".toUTF8.toList ctx.args) ∧
    (emptyAfter ctx storage).host.gas.promises = (emptyBefore ctx storage).host.gas.promises := by
  have hf := emptyPaid_frame ctx storage
  have hpview := StorageFrame.Frame.isView hf
  rw [paidStore_view] at hpview
  have hv : (emptyPaid ctx storage).context.isView = false := hpview.trans (emptyBefore_isView ctx storage)
  have hk : withinLimit (emptyPaid ctx storage).config.maxStorageKeyLen "k".toUTF8.toList.length = true := by
    rw [emptyPaid_config, storageInput_config]
    rw [show "k".toUTF8.toList.length = 1 by decide +kernel]
    change withinLimit (some ctx.protocol.wasm.limits.maxLengthStorageKey) 1 = true
    simpa [withinLimit] using hkeyLimit
  have hval : withinLimit (emptyPaid ctx storage).config.maxStorageValueLen ctx.args.length = true := by
    rw [emptyPaid_config, storageInput_config]
    change withinLimit (some ctx.protocol.wasm.limits.maxLengthStorageValue) ctx.args.length = true
    simpa [withinLimit] using hvalueLimit
  have hpost := empty_postCharges ctx storage raw hwf hs hentries hselected
  have hn := StorageEmpty.storage_none (Output.paidStore (emptyBefore ctx storage) (emptyPaid ctx storage))
    ctx raw hwf storage hs (emptyPaid_store_represents ctx storage) "k".toUTF8.toList hentries hselected
  have hc : (emptyBefore ctx storage).host.gas.Credits
      (burnSum (emptyBefore ctx storage).host.extCosts (emptyPreCharges ctx storage) +
        (burnSum (emptyBefore ctx storage).host.extCosts (trieCharges ctx.trie ctx.trie) +
          (burnSum (emptyBefore ctx storage).host.extCosts
            (postCharges (Output.paidStore (emptyBefore ctx storage) (emptyPaid ctx storage)) "k".toUTF8.toList) + rest))) := by
    rw [StorageEmpty.trieCharges_self_cost, hpost]
    simpa only [burnSum, List.map_nil, List.sum_nil, Nat.zero_add, emptyCost] using hcredits
  have hm := StorageEmpty.metered_empty_sufficient ctx.protocol.fees.numExtraBytesRecord
    (emptyBefore ctx storage) (emptyPaid ctx storage) ctx raw hwf storage hs
    (emptyPaid_represents ctx storage) 1 0 u64Max 0 "k".toUTF8.toList ctx.args rest
    (emptyBefore_isView ctx storage) (by unfold emptyPaid emptyPreCharges; rfl) hv (emptyPaid_accounting ctx storage)
    (emptyPaid_key ctx storage hpages) (emptyPaid_value ctx storage) hk hval hentries hselected hc hproof
  have hn' : (emptyPaid ctx storage).storage "k".toUTF8.toList = none := hn
  simp only [hn', Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
    StorageEmpty.trieCharges_self_cost, hpost, Nat.add_zero] at hm
  simpa only [emptyAfter, emptyPhase, emptyCost, emptyPreCharges, burnSum,
    List.map_nil, List.sum_nil, Nat.add_zero] using hm

private theorem phases_frame (before : HostStore NearState) (prePaid triePaid : NearState)
    (trie : Near.TrieOverlay.State) (extra : Nat) (key value : List UInt8) :
    let phase := prepared (Output.paidStore before prePaid) triePaid trie
    let paid := (applyCharges (written phase key value).host (postCharges phase key)).1
    StorageFrame.Frame (Output.paidStore before prePaid)
      (finished extra phase 1 0 u64Max 0 key value paid) := by
  exact (StorageFrame.prepared_frame _ _ _).trans (StorageFrame.finished_frame _ _ _ _ _ _ _ _)

/-- All resources outside storage/accounting/gas effects survive the computed
write. This is independent of the successful invocation theorem. -/
theorem emptyAfter_frame (ctx : NearInterface.Context) (storage : Storage) :
    StorageFrame.Frame (emptyBefore ctx storage) (emptyAfter ctx storage) := by
  have hp := phases_frame (emptyBefore ctx storage) (emptyPaid ctx storage)
    (applyCharges (accounted (Output.paidStore (emptyBefore ctx storage) (emptyPaid ctx storage)) ctx.trie).host
      (trieCharges ctx.trie ctx.trie)).1
    (ctx.trie.set (Near.TrieOverlay.contractKey (emptyPaid ctx storage).context.currentAccountId
      "k".toUTF8.toList) ctx.args) ctx.protocol.fees.numExtraBytesRecord "k".toUTF8.toList ctx.args
  have hf : StorageFrame.Frame (Output.paidStore (emptyBefore ctx storage) (emptyPaid ctx storage))
      (emptyAfter ctx storage) := by
    simpa only [emptyAfter, emptyPhase] using hp
  exact (emptyPaid_frame ctx storage).trans hf

private theorem frontier_of_inputBefore (cfg : RuntimeConfig) (store : Store NearState)
    (before after : HostStore NearState) (cost rest : Nat)
    (hbefore : before = inputBefore cfg.wasm (successStorageBefore cfg store) moduleInstance)
    (hinvoke : (metered cfg.fees.numExtraBytesRecord "storage_write" storageWriteFn).invoke
      before (args 1 0 u64Max 0) = .Return [.i64 0] after)
    (hburn : after.host.gas.burnt = before.host.gas.burnt + cost)
    (hpromises : after.host.gas.promises = before.host.gas.promises)
    (hcredits : after.host.gas.Credits
      ((successCosts cfg store after cost).storageSuffix cfg.wasm.regularOpCost rest)) :
    StorageFrontier cfg store after cost rest 0 := by
  subst before
  refine ⟨hinvoke, Nat.le_of_eq hburn, ?_, hcredits⟩
  change after.host.gas.burnt + after.host.gas.promises ≤
    (inputBefore cfg.wasm (successStorageBefore cfg store) moduleInstance).host.gas.burnt +
      (inputBefore cfg.wasm (successStorageBefore cfg store) moduleInstance).host.gas.promises + cost
  rw [hburn, hpromises]
  omega

/-- The sole arbitrary storage frontier in the whole walking-body proof is
now discharged from original boundary representation and local resources. -/
theorem empty_storageFrontier (ctx : NearInterface.Context) (storage : Storage)
    (raw : NearInterface.RawStorage) (rest : Nat)
    (hwf : ctx.WF raw) (hs : storage.toFinset = raw)
    (hpages : 0 < ctx.protocol.wasm.limits.initialMemoryPages)
    (hkeyLimit : 1 ≤ ctx.protocol.wasm.limits.maxLengthStorageKey)
    (hvalueLimit : ctx.args.length ≤ ctx.protocol.wasm.limits.maxLengthStorageValue)
    (hentries : ctx.trie.entries = [])
    (hselected : Near.TrieOverlay.selected ctx.trie
      (Near.TrieOverlay.contractKey ctx.current.bytes "k".toUTF8.toList) = none)
    (hcredits : (emptyBefore ctx storage).host.gas.Credits (emptyCost ctx storage +
      (successCosts ctx.protocol
        (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) storage)
        (emptyAfter ctx storage) (emptyCost ctx storage)).storageSuffix ctx.protocol.wasm.regularOpCost rest))
    (hproof : recordedStorageError (emptyPaid ctx storage)
      (ctx.trie.set (Near.TrieOverlay.contractKey (emptyPaid ctx storage).context.currentAccountId
        "k".toUTF8.toList) ctx.args) = none) :
    StorageFrontier ctx.protocol (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) storage)
      (emptyAfter ctx storage) (emptyCost ctx storage) rest 0 := by
  have hm := empty_invoke ctx storage raw _ hwf hs hpages hkeyLimit hvalueLimit
    hentries hselected hcredits hproof
  exact frontier_of_inputBefore ctx.protocol
    (executionStore ctx.protocol (Near.Boundary.toVMContext ctx) storage)
    (emptyBefore ctx storage) (emptyAfter ctx storage) (emptyCost ctx storage) rest rfl
    hm.1 hm.2.1 hm.2.2.2.2 hm.2.2.1

/-- The startup/input prefix preserves finite raw-storage representation,
including key coverage needed by VM outcome extraction. -/
theorem emptyBefore_representation (ctx : NearInterface.Context) (storage : Storage)
    (raw : NearInterface.RawStorage) (hwf : ctx.WF raw) (hs : storage.toFinset = raw) :
    StorageRepresentation.Represents (emptyBefore ctx storage).host raw := by
  have hr := StorageRepresentation.toNearState_represents ctx.protocol (Near.Boundary.toVMContext ctx)
    storage raw hs hwf.raw_keys_unique
  have hstorage := storageInput_storage ctx.protocol (Near.Boundary.toVMContext ctx) storage
  have hkeys := storageInput_storageKeys ctx.protocol (Near.Boundary.toVMContext ctx) storage
  constructor
  · intro key value
    rw [show (emptyBefore ctx storage).host.storage =
      ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol storage).storage from hstorage]
    exact hr.lookup key value
  · intro key value hm
    rw [show (emptyBefore ctx storage).host.storageKeys =
      ((Near.Boundary.toVMContext ctx).toNearState ctx.protocol storage).storageKeys from hkeys]
    exact hr.coverage key value hm

private theorem phases_finalStorage (before : HostStore NearState) (prePaid triePaid : NearState)
    (trie : Near.TrieOverlay.State) (extra : Nat) (key value : List UInt8)
    (raw : NearInterface.RawStorage) (hr : StorageRepresentation.Represents prePaid raw) :
    let phase := prepared (Output.paidStore before prePaid) triePaid trie
    let paid := (applyCharges (written phase key value).host (postCharges phase key)).1
    (finalStorage (finished extra phase 1 0 u64Max 0 key value paid).host).toFinset =
      NearInterface.rawWrite raw key value := by
  have hpre := hr.paidStore before
  have hphase := hpre.prepared (Output.paidStore before prePaid) triePaid trie
  exact StorageRepresentation.finalStorage_finished extra _ raw hphase 1 0 u64Max 0 key value

/-- Deterministic post-storage is exactly the original finite records with
`k` installed; no complete host invocation is a premise. -/
theorem emptyAfter_finalStorage (ctx : NearInterface.Context) (storage : Storage)
    (raw : NearInterface.RawStorage) (hwf : ctx.WF raw) (hs : storage.toFinset = raw) :
    (finalStorage (emptyAfter ctx storage).host).toFinset =
      NearInterface.rawWrite raw "k".toUTF8.toList ctx.args := by
  have hp := (emptyBefore_representation ctx storage raw hwf hs).applyCharges
    (emptyPreCharges ctx storage) (pre_burns ctx storage)
  rw [emptyPaid_fold] at hp
  have hf := phases_finalStorage (emptyBefore ctx storage) (emptyPaid ctx storage)
    (applyCharges (accounted (Output.paidStore (emptyBefore ctx storage) (emptyPaid ctx storage)) ctx.trie).host
      (trieCharges ctx.trie ctx.trie)).1
    (ctx.trie.set (Near.TrieOverlay.contractKey (emptyPaid ctx storage).context.currentAccountId
      "k".toUTF8.toList) ctx.args) ctx.protocol.fees.numExtraBytesRecord "k".toUTF8.toList ctx.args raw hp
  simpa only [emptyAfter, emptyPhase] using hf

end WNear.Skeleton
